from __future__ import annotations

import argparse
import asyncio
import json
import selectors
import subprocess
import time
import tomllib
import urllib.error
import urllib.request
from pathlib import Path
from typing import Any

from mathdoc_agent.export.json import paper_structure_data, to_json
from mathdoc_agent.mathagents import definitions
from mathdoc_agent.models.document import MathDocument
from mathdoc_agent.orchestration.claim_audit import audit_claims_for_lean
from mathdoc_agent.orchestration.document_orchestrator import (
    document_from_text,
    refine_math_document,
)
from mathdoc_agent.plugins.document_types import default_document_handler_registry
from mathdoc_agent.plugins.proof_types import default_proof_handler_registry
from mathdoc_agent.registries.document_handlers import DocumentHandlerRegistry
from mathdoc_agent.registries.proof_handlers import ProofHandlerRegistry


_DEFAULT_CLAIM_AGENT = object()
_DEFAULT_PROOF_RESOLUTION_AGENTS = object()
_LEANAIDE_LAKE_NAME = "LeanAide"
_LEANAIDE_PROCESS_URL = "http://localhost:7654"
_LEANAIDE_READY_PREFIX = "Server ready"


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
    if resolved_claim_agent is None:
        return to_json(document, indent=indent)
    data = await audit_claims_for_lean(paper_structure_data(document), resolved_claim_agent)
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
        help="After writing JSON with -o/--output, run `lake exe codegen <jsonfile>`.",
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
            subprocess.run(
                ["lake", "exe", "codegen", str(args.output.resolve())],
                check=True,
                cwd=leanaide_dir,
            )


if __name__ == "__main__":
    main()
