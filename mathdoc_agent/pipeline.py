from __future__ import annotations

import argparse
import asyncio
import json
import os
import selectors
import subprocess
import sys
import tempfile
import time
import tomllib
import urllib.error
import urllib.request
from pathlib import Path
from typing import Any

from mathdoc_agent.export.json import paper_structure_data
from mathdoc_agent.mathagents import definitions
from mathdoc_agent.models.document import MathDocument
from mathdoc_agent.orchestration.claim_audit import audit_claims_for_lean
from mathdoc_agent.orchestration.deduced_from_claim_rewrite import (
    rewrite_deduced_from_claims_for_lean,
)
from mathdoc_agent.orchestration.document_orchestrator import (
    document_from_text,
    refine_math_document,
)
from mathdoc_agent.orchestration.mathlib_reuse import record_mathlib_definitions
from mathdoc_agent.plugins.document_types import default_document_handler_registry
from mathdoc_agent.plugins.proof_types import default_proof_handler_registry
from mathdoc_agent.registries.document_handlers import DocumentHandlerRegistry
from mathdoc_agent.registries.proof_handlers import ProofHandlerRegistry


_DEFAULT_CLAIM_AGENT = object()
_DEFAULT_DEDUCED_FROM_CLAIM_AGENT = object()
_DEFAULT_PROOF_RESOLUTION_AGENTS = object()
_LEANAIDE_LAKE_NAME = "LeanAide"
_LEANAIDE_PROCESS_URL = "http://localhost:7654"
_LEANAIDE_READY_PREFIX = "Server ready"
_LEANAIDE_CODEGEN_TASKS = ["lean_from_json_structured", "elaborate"]
_LEANAIDE_SERVER_TIMEOUT = 6000.0


def lakefile_project_name(lakefile: Path) -> str | None:
    data = tomllib.loads(lakefile.read_text(encoding="utf-8"))
    name = data.get("name")
    return name if isinstance(name, str) else None


def is_leanaide_lakefile(lakefile: Path) -> bool:
    name = lakefile_project_name(lakefile)
    return name is not None and name.casefold() == _LEANAIDE_LAKE_NAME.casefold()


def find_leanaide_dir(start: Path | str | None = None) -> Path:
    path = Path.cwd() if start is None else Path(start)
    directory = path.parent if path.is_file() else path
    directory = directory.resolve()

    for candidate in (directory, *directory.parents):
        lakefile = candidate / "lakefile.toml"
        if lakefile.is_file() and is_leanaide_lakefile(lakefile):
            return candidate

    raise FileNotFoundError(
        f"Could not find a parent directory containing a LeanAide lakefile.toml from {directory}"
    )


def find_leanaide_dir_from_paths(*starts: Path | str | None) -> Path:
    errors: list[FileNotFoundError] = []
    for start in starts:
        try:
            return find_leanaide_dir(start)
        except FileNotFoundError as error:
            errors.append(error)
    try:
        return find_leanaide_dir()
    except FileNotFoundError as error:
        errors.append(error)
    raise FileNotFoundError(
        "Could not find a parent directory containing a LeanAide lakefile.toml"
    ) from errors[-1]


def _url_with_scheme(url: str) -> str:
    return url if "://" in url else f"http://{url}"


def post_leanaide_json(
    data: dict[str, Any],
    *,
    url: str = _LEANAIDE_PROCESS_URL,
    timeout: float = 30.0,
) -> dict[str, Any]:
    request = urllib.request.Request(
        _url_with_scheme(url),
        data=json.dumps(data).encode("utf-8"),
        headers={"Content-Type": "application/json"},
        method="POST",
    )
    try:
        with urllib.request.urlopen(request, timeout=timeout) as response:
            payload = json.loads(response.read().decode("utf-8"))
    except urllib.error.URLError as error:
        raise RuntimeError(f"LeanAide server request failed: {error}") from error

    if not isinstance(payload, dict):
        raise RuntimeError(f"LeanAide server returned non-object JSON: {payload!r}")
    return payload


def leanaide_server_echo_succeeds(
    *,
    url: str = _LEANAIDE_PROCESS_URL,
    timeout: float = 30.0,
) -> bool:
    try:
        response = post_leanaide_json({"task": "echo"}, url=url, timeout=timeout)
    except Exception:
        return False
    return response.get("result") == "success"


def _stderr_line_startswith(line: str, prefix: str) -> bool:
    stripped = line.lstrip()
    if stripped.startswith(prefix):
        return True
    return f"]  {prefix}" in stripped


def wait_for_process_stderr_prefix(
    process: subprocess.Popen[str],
    prefix: str,
    *,
    timeout: float = 120.0,
) -> str:
    if process.stderr is None:
        raise RuntimeError("LeanAide process was not started with stderr=PIPE")

    deadline = time.monotonic() + timeout
    selector = selectors.DefaultSelector()
    selector.register(process.stderr, selectors.EVENT_READ)
    stderr_lines: list[str] = []
    try:
        while True:
            if process.poll() is not None:
                raise RuntimeError(
                    "LeanAide process exited before becoming ready. "
                    f"stderr: {' | '.join(stderr_lines[-10:])}"
                )

            remaining = deadline - time.monotonic()
            if remaining <= 0:
                raise TimeoutError(
                    f"Timed out waiting for LeanAide stderr line starting with {prefix!r}"
                )

            events = selector.select(remaining)
            if not events:
                continue

            line = process.stderr.readline()
            if line == "":
                continue
            stderr_lines.append(line.rstrip("\n"))
            if _stderr_line_startswith(line, prefix):
                return line
    finally:
        selector.close()


def _terminate_process(process: subprocess.Popen[str]) -> None:
    if process.poll() is not None:
        return
    process.terminate()
    try:
        process.wait(timeout=5)
    except subprocess.TimeoutExpired:
        process.kill()
        process.wait(timeout=5)


def start_leanaide_process(
    start: Path | str | None = None,
    *,
    url: str = _LEANAIDE_PROCESS_URL,
    timeout: float = 120.0,
) -> subprocess.Popen[str]:
    leanaide_dir = find_leanaide_dir(start)
    process = subprocess.Popen(
        ["lake", "exe", "leanaide_process"],
        cwd=leanaide_dir,
        stdin=subprocess.PIPE,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        text=True,
        bufsize=1,
    )
    try:
        wait_for_process_stderr_prefix(
            process, _LEANAIDE_READY_PREFIX, timeout=timeout
        )
        response = post_leanaide_json({"task": "echo"}, url=url, timeout=timeout)
        result = response.get("result")
        if result != "success":
            raise RuntimeError(
                f"LeanAide echo health check failed: expected result='success', got {result!r}"
            )
        return process
    except Exception:
        _terminate_process(process)
        raise


def start_leanaide_http_server(leanaide_dir: Path) -> subprocess.Popen[str]:
    log_dir = Path(tempfile.gettempdir())
    stdout_path = log_dir / "leanaide_server.stdout.log"
    stderr_path = log_dir / "leanaide_server.stderr.log"
    env = os.environ.copy()
    env.setdefault("LEANAIDE_COMMAND", "lake exe leanaide_process")
    env.setdefault("LEANAIDE_LOG_FILE", str(log_dir / "leanaide.log"))
    python_executable = leanaide_server_python(leanaide_dir)
    venv_dir = leanaide_dir / "venv"
    if python_executable.parent == venv_dir / "bin":
        env["VIRTUAL_ENV"] = str(venv_dir)
        env["PATH"] = f"{python_executable.parent}{os.pathsep}{env.get('PATH', '')}"
    stdout = stdout_path.open("a", encoding="utf-8")
    stderr = stderr_path.open("a", encoding="utf-8")
    try:
        process = subprocess.Popen(
            [str(python_executable), str(leanaide_dir / "leanaide_server.py")],
            cwd=leanaide_dir,
            stdout=stdout,
            stderr=stderr,
            text=True,
            env=env,
        )
        return process
    except Exception:
        raise
    finally:
        stdout.close()
        stderr.close()


def leanaide_server_python(leanaide_dir: Path) -> Path:
    venv_python = leanaide_dir / "venv" / "bin" / "python"
    return venv_python if venv_python.exists() else Path(sys.executable)


def ensure_leanaide_http_server(
    leanaide_dir: Path,
    *,
    url: str = _LEANAIDE_PROCESS_URL,
    timeout: float = _LEANAIDE_SERVER_TIMEOUT,
) -> subprocess.Popen[str] | None:
    if leanaide_server_echo_succeeds(url=url, timeout=timeout):
        return None

    process = start_leanaide_http_server(leanaide_dir)
    deadline = time.monotonic() + timeout
    while True:
        if process.poll() is not None:
            raise RuntimeError(
                "LeanAide HTTP server exited before responding to echo. "
                "Check logs in the system temporary directory."
            )
        remaining = deadline - time.monotonic()
        if remaining <= 0:
            _terminate_process(process)
            raise TimeoutError("Timed out waiting for LeanAide HTTP server echo")
        if leanaide_server_echo_succeeds(url=url, timeout=remaining):
            return process
        time.sleep(min(1.0, remaining))


def strip_json_suffix(name: str) -> str:
    return name[: -len(".json")] if name.endswith(".json") else name


def codegen_output_path(input_path: Path, leanaide_dir: Path) -> Path:
    stem = strip_json_suffix(input_path.name or "generated.json")
    return leanaide_dir / "CodeGen" / f"{stem}.lean"


def ensure_mathlib_import(top_code: str) -> str:
    return top_code if "import Mathlib" in top_code else f"import Mathlib\n{top_code}"


def generated_file_contents(input_path: Path, top_code: str, document_code: str) -> str:
    top_code = ensure_mathlib_import(top_code).rstrip()
    document_code = document_code.rstrip()
    return (
        f"{top_code}\n\n"
        f"-- Generated by codegen.lean from {input_path}\n\n"
        f"{document_code}\n"
    )


def indent_lines(indent: str, text: str) -> str:
    return "\n".join(f"{indent}{line}" for line in text.split("\n"))


def count_label(n: int, singular: str, plural: str) -> str:
    return f"1 {singular}" if n == 1 else f"{n} {plural}"


def json_field_as_string(item: dict[str, Any], field: str) -> str:
    value = item.get(field, "<missing>")
    return value if isinstance(value, str) else json.dumps(value, ensure_ascii=False)


def flatten_json_array_items(items: Any) -> list[Any]:
    if not isinstance(items, list):
        return []
    flattened: list[Any] = []
    for item in items:
        if isinstance(item, list):
            flattened.extend(item)
        else:
            flattened.append(item)
    return flattened


def format_string_list(title: str, empty: str, items: Any) -> str:
    if not isinstance(items, list):
        items = []
    items = [item if isinstance(item, str) else json.dumps(item) for item in items]
    if not items:
        return empty
    numbered = []
    for idx, item in enumerate(items, start=1):
        indented = indent_lines("   ", item)
        numbered.append(f"{idx}. {indented[3:]}")
    return f"{title} ({len(items)}):\n" + "\n".join(numbered)


def format_sorry_item(idx: int, item: Any) -> str:
    obj = item if isinstance(item, dict) else {}
    declaration = json_field_as_string(obj, "declaration_name")
    sorry_type = json_field_as_string(obj, "sorry_type")
    return f"{idx + 1}. {declaration}\n{indent_lines('   ', sorry_type)}"


def format_sorries(title: str, empty: str, items: Any) -> str:
    items = flatten_json_array_items(items)
    if not items:
        return empty
    rendered = [format_sorry_item(idx, item) for idx, item in enumerate(items)]
    return (
        f"{title} ({count_label(len(items), 'goal', 'goals')}):\n"
        + "\n\n".join(rendered)
    )


def format_elaboration_result(result: dict[str, Any]) -> str:
    declarations = result.get("declarations", [])
    if not isinstance(declarations, list):
        declarations = []
    declarations = [
        item if isinstance(item, str) else json.dumps(item, ensure_ascii=False)
        for item in declarations
    ]
    decl_section = (
        "Declarations: none"
        if not declarations
        else f"Declarations ({len(declarations)}): {', '.join(declarations)}"
    )
    return "\n\n".join(
        [
            decl_section,
            format_string_list(
                "Elaboration logs", "Elaboration logs: none", result.get("logs", [])
            ),
            format_sorries("Sorries", "Sorries: none", result.get("sorries", [])),
            format_sorries(
                "Sorries after purge",
                "Sorries after purge: none",
                result.get("sorries_after_purge", []),
            ),
        ]
    )


def append_elaboration_results(out_file: Path, result: dict[str, Any]) -> None:
    with out_file.open("a", encoding="utf-8") as handle:
        handle.write("\n\n/-!\n## Elaboration results \n\n")
        handle.write(format_elaboration_result(result))
        handle.write("\n\n-/\n")


def leanaide_codegen_request(document_json: Any) -> dict[str, Any]:
    if isinstance(document_json, dict) and "document_json" in document_json:
        request = dict(document_json)
    else:
        request = {"document_json": document_json}
    request["tasks"] = list(_LEANAIDE_CODEGEN_TASKS)
    return request


def run_leanaide_server_codegen(
    json_path: Path,
    document_json: Any,
    leanaide_dir: Path,
    *,
    url: str = _LEANAIDE_PROCESS_URL,
    timeout: float = _LEANAIDE_SERVER_TIMEOUT,
) -> bool:
    ensure_leanaide_http_server(leanaide_dir, url=url, timeout=timeout)
    response = post_leanaide_json(
        leanaide_codegen_request(document_json),
        url=url,
        timeout=timeout,
    )
    result = response.get("result")
    if "document_code" not in response:
        raise RuntimeError(f"Code generation did not return document_code: {response!r}")

    document_code = response["document_code"]
    if not isinstance(document_code, str):
        raise RuntimeError(f"document_code is not a string: {document_code!r}")
    top_code = response.get("top_code", "import Mathlib\n")
    if not isinstance(top_code, str):
        top_code = "import Mathlib\n"

    out_file = codegen_output_path(json_path, leanaide_dir)
    out_file.parent.mkdir(parents=True, exist_ok=True)
    out_file.write_text(
        generated_file_contents(json_path, top_code, document_code),
        encoding="utf-8",
    )
    print(f"Generated {out_file}")
    append_elaboration_results(out_file, response)

    if result == "success":
        print("Elaboration succeeded", file=sys.stderr)
        print(format_elaboration_result(response), file=sys.stderr)
        return True

    print(f"Elaboration returned non-success result: {result}", file=sys.stderr)
    print(format_elaboration_result(response), file=sys.stderr)
    return False


async def generate_math_document(
    source_text: str,
    *,
    id: str = "doc",
    title: str | None = None,
    document_registry: DocumentHandlerRegistry | None = None,
    proof_registry: ProofHandlerRegistry | None = None,
    document_iterations: int = 20,
    proof_iterations: int = 100,
    proof_resolution_agents: dict[str, object] | None = None,
) -> MathDocument:
    document = document_from_text(source_text, id=id, title=title)
    return await refine_math_document(
        document,
        document_registry or default_document_handler_registry(),
        proof_registry or default_proof_handler_registry(),
        document_iterations=document_iterations,
        proof_iterations=proof_iterations,
        proof_resolution_agents=proof_resolution_agents,
    )


async def generate_math_document_json(
    source_text: str,
    *,
    id: str = "doc",
    title: str | None = None,
    document_registry: DocumentHandlerRegistry | None = None,
    proof_registry: ProofHandlerRegistry | None = None,
    document_iterations: int = 20,
    proof_iterations: int = 100,
    indent: int = 2,
    claim_agent: Any | None = _DEFAULT_CLAIM_AGENT,
    deduced_from_claim_agent: Any | None = _DEFAULT_DEDUCED_FROM_CLAIM_AGENT,
    proof_resolution_agents: (
        dict[str, object] | None | object
    ) = _DEFAULT_PROOF_RESOLUTION_AGENTS,
) -> str:
    using_default_registries = document_registry is None and proof_registry is None
    resolved_claim_agent = (
        definitions.claim_audit_agent
        if claim_agent is _DEFAULT_CLAIM_AGENT and using_default_registries
        else (None if claim_agent is _DEFAULT_CLAIM_AGENT else claim_agent)
    )
    resolved_deduced_from_claim_agent = (
        definitions.deduced_from_claim_rewrite_agent
        if deduced_from_claim_agent is _DEFAULT_DEDUCED_FROM_CLAIM_AGENT
        and using_default_registries
        else (
            None
            if deduced_from_claim_agent is _DEFAULT_DEDUCED_FROM_CLAIM_AGENT
            else deduced_from_claim_agent
        )
    )
    resolved_proof_resolution_agents = (
        definitions.proof_resolution_agents
        if proof_resolution_agents is _DEFAULT_PROOF_RESOLUTION_AGENTS and using_default_registries
        else (
            None
            if proof_resolution_agents is _DEFAULT_PROOF_RESOLUTION_AGENTS
            else proof_resolution_agents
        )
    )
    document = await generate_math_document(
        source_text,
        id=id,
        title=title,
        document_registry=document_registry,
        proof_registry=proof_registry,
        document_iterations=document_iterations,
        proof_iterations=proof_iterations,
        proof_resolution_agents=resolved_proof_resolution_agents,
    )
    document = record_mathlib_definitions(document)
    data = paper_structure_data(document)
    data = await rewrite_deduced_from_claims_for_lean(
        data,
        resolved_deduced_from_claim_agent,
    )
    data = await audit_claims_for_lean(data, resolved_claim_agent)
    return json.dumps(data, indent=indent, ensure_ascii=False)


def generate_math_document_json_sync(
    source_text: str,
    *,
    id: str = "doc",
    title: str | None = None,
    document_registry: DocumentHandlerRegistry | None = None,
    proof_registry: ProofHandlerRegistry | None = None,
    document_iterations: int = 20,
    proof_iterations: int = 100,
    indent: int = 2,
    claim_agent: Any | None = _DEFAULT_CLAIM_AGENT,
    deduced_from_claim_agent: Any | None = _DEFAULT_DEDUCED_FROM_CLAIM_AGENT,
    proof_resolution_agents: (
        dict[str, object] | None | object
    ) = _DEFAULT_PROOF_RESOLUTION_AGENTS,
) -> str:
    return asyncio.run(
        generate_math_document_json(
            source_text,
            id=id,
            title=title,
            document_registry=document_registry,
            proof_registry=proof_registry,
            document_iterations=document_iterations,
            proof_iterations=proof_iterations,
            indent=indent,
            claim_agent=claim_agent,
            deduced_from_claim_agent=deduced_from_claim_agent,
            proof_resolution_agents=proof_resolution_agents,
        )
    )


def main() -> None:
    parser = argparse.ArgumentParser(
        description="Generate mathdoc_agent JSON from a mathematical source text file."
    )
    parser.add_argument("source", type=Path, help="Source text/Markdown file to parse.")
    parser.add_argument(
        "-o",
        "--output",
        type=Path,
        help="JSON output path. If omitted, write JSON to stdout.",
    )
    parser.add_argument(
        "--id",
        help="Document id. Defaults to the source file stem.",
    )
    parser.add_argument("--title", help="Optional document title.")
    parser.add_argument(
        "--document-iterations",
        type=int,
        default=20,
        help="Maximum document refinement iterations.",
    )
    parser.add_argument(
        "--proof-iterations",
        type=int,
        default=100,
        help="Maximum proof refinement iterations per proof.",
    )
    parser.add_argument(
        "--skip-claim-audit",
        action="store_true",
        help="Skip the final LLM audit that repairs claim fields for Lean codegen.",
    )
    parser.add_argument(
        "--skip-deduced-from-claim-rewrite",
        action="store_true",
        help=(
            "Skip the final LLM rewrite of deduced_from_claim dependencies. "
            "Residual dependencies are still materialized as explicit assertions."
        ),
    )
    parser.add_argument(
        "--skip-proof-resolution",
        action="store_true",
        help=(
            "Skip the post-refinement agents that rewrite proof kinds without "
            "dedicated Lean handlers into simpler handled proof structures."
        ),
    )
    parser.add_argument(
        "--lean",
        action="store_true",
        help=(
            "After writing JSON with -o/--output, generate and elaborate Lean through "
            "the LeanAide server."
        ),
    )
    parser.add_argument("--indent", type=int, default=2, help="JSON indentation.")
    args = parser.parse_args()
    if args.lean and args.output is None:
        parser.error("--lean requires -o/--output so there is a JSON file for codegen.")

    source_text = args.source.read_text(encoding="utf-8")
    json_text = generate_math_document_json_sync(
        source_text,
        id=args.id or args.source.stem,
        title=args.title,
        document_iterations=args.document_iterations,
        proof_iterations=args.proof_iterations,
        indent=args.indent,
        claim_agent=None if args.skip_claim_audit else definitions.claim_audit_agent,
        deduced_from_claim_agent=(
            None
            if args.skip_deduced_from_claim_rewrite
            else definitions.deduced_from_claim_rewrite_agent
        ),
        proof_resolution_agents=(
            None if args.skip_proof_resolution else definitions.proof_resolution_agents
        ),
    )
    if args.output is None:
        print(json_text)
    else:
        args.output.write_text(json_text + "\n", encoding="utf-8")
        if args.lean:
            leanaide_dir = find_leanaide_dir_from_paths(args.source, args.output)
            lean_ok = run_leanaide_server_codegen(
                args.output.resolve(),
                json.loads(json_text),
                leanaide_dir,
            )
            if not lean_ok:
                raise SystemExit(1)


if __name__ == "__main__":
    main()
