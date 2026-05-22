from __future__ import annotations

import tempfile
import unittest
from pathlib import Path
from unittest.mock import Mock, patch

from mathdoc_agent.pipeline import (
    _stderr_line_startswith,
    append_elaboration_results,
    codegen_output_path,
    ensure_leanaide_http_server,
    format_elaboration_result,
    find_leanaide_dir,
    find_leanaide_dir_from_paths,
    generated_file_contents,
    is_leanaide_lakefile,
    lakefile_project_name,
    leanaide_codegen_request,
    leanaide_server_python,
    post_leanaide_json,
    run_leanaide_server_codegen,
    start_leanaide_http_server,
    start_leanaide_process,
)


class LeanAideDirTests(unittest.TestCase):
    def test_lakefile_project_name(self) -> None:
        with tempfile.TemporaryDirectory() as tmpdir:
            lakefile = Path(tmpdir) / "lakefile.toml"
            lakefile.write_text('name = "LeanAide"\n', encoding="utf-8")

            self.assertEqual(lakefile_project_name(lakefile), "LeanAide")

    def test_is_leanaide_lakefile_accepts_current_package_name_case(self) -> None:
        with tempfile.TemporaryDirectory() as tmpdir:
            lakefile = Path(tmpdir) / "lakefile.toml"
            lakefile.write_text('name = "leanaide"\n', encoding="utf-8")

            self.assertTrue(is_leanaide_lakefile(lakefile))

    def test_find_leanaide_dir_walks_up_from_nested_directory(self) -> None:
        with tempfile.TemporaryDirectory() as tmpdir:
            root = Path(tmpdir)
            nested = root / "mathdoc_agent" / "examples"
            nested.mkdir(parents=True)
            (root / "lakefile.toml").write_text('name = "LeanAide"\n', encoding="utf-8")

            self.assertEqual(find_leanaide_dir(nested), root.resolve())

    def test_find_leanaide_dir_accepts_file_path_start(self) -> None:
        with tempfile.TemporaryDirectory() as tmpdir:
            root = Path(tmpdir)
            source = root / "mathdoc_agent" / "examples" / "source.md"
            source.parent.mkdir(parents=True)
            source.write_text("text\n", encoding="utf-8")
            (root / "lakefile.toml").write_text('name = "LeanAide"\n', encoding="utf-8")

            self.assertEqual(find_leanaide_dir(source), root.resolve())

    def test_find_leanaide_dir_raises_when_missing(self) -> None:
        with tempfile.TemporaryDirectory() as tmpdir:
            nested = Path(tmpdir) / "mathdoc_agent"
            nested.mkdir()

            with self.assertRaises(FileNotFoundError):
                find_leanaide_dir(nested)

    def test_find_leanaide_dir_from_paths_tries_later_paths(self) -> None:
        with tempfile.TemporaryDirectory() as missing_dir:
            with tempfile.TemporaryDirectory() as repo_dir:
                root = Path(repo_dir)
                source = root / "source.md"
                source.write_text("text\n", encoding="utf-8")
                (root / "lakefile.toml").write_text(
                    'name = "LeanAide"\n', encoding="utf-8"
                )

                self.assertEqual(
                    find_leanaide_dir_from_paths(Path(missing_dir), source),
                    root.resolve(),
                )

    def test_post_leanaide_json_posts_echo_payload(self) -> None:
        response = Mock()
        response.read.return_value = b'{"result": "success", "data": {"task": "echo"}}'
        response.__enter__ = Mock(return_value=response)
        response.__exit__ = Mock(return_value=None)

        with patch("urllib.request.urlopen", return_value=response) as urlopen:
            result = post_leanaide_json(
                {"task": "echo"}, url="localhost:7654", timeout=3
            )

        self.assertEqual(result["result"], "success")
        request = urlopen.call_args.args[0]
        self.assertEqual(request.full_url, "http://localhost:7654")
        self.assertEqual(request.data, b'{"task": "echo"}')
        self.assertEqual(request.get_method(), "POST")

    def test_start_leanaide_process_waits_for_ready_and_echoes(self) -> None:
        with tempfile.TemporaryDirectory() as tmpdir:
            root = Path(tmpdir)
            (root / "lakefile.toml").write_text('name = "LeanAide"\n', encoding="utf-8")
            process = Mock()

            with (
                patch("subprocess.Popen", return_value=process) as popen,
                patch("mathdoc_agent.pipeline.wait_for_process_stderr_prefix") as wait,
                patch(
                    "mathdoc_agent.pipeline.post_leanaide_json",
                    return_value={"result": "success"},
                ) as post,
            ):
                result = start_leanaide_process(root, timeout=3)

        self.assertIs(result, process)
        popen.assert_called_once()
        self.assertEqual(popen.call_args.args[0], ["lake", "exe", "leanaide_process"])
        self.assertEqual(popen.call_args.kwargs["cwd"], root.resolve())
        wait.assert_called_once_with(process, "Server ready", timeout=3)
        post.assert_called_once_with({"task": "echo"}, url="http://localhost:7654", timeout=3)

    def test_stderr_line_startswith_accepts_logged_ready_line(self) -> None:
        line = (
            "[2026-05-22T10:57:54] [leanaide.tasks.info] [root]  "
            "Server ready. Waiting for input..."
        )

        self.assertTrue(_stderr_line_startswith(line, "Server ready"))

    def test_leanaide_codegen_request_wraps_document_json(self) -> None:
        request = leanaide_codegen_request({"body": []})

        self.assertEqual(
            request["tasks"], ["lean_from_json_structured", "elaborate"]
        )
        self.assertEqual(request["document_json"], {"body": []})

    def test_leanaide_codegen_request_preserves_existing_document_json(self) -> None:
        request = leanaide_codegen_request({"document_json": {"body": []}, "x": 1})

        self.assertEqual(
            request,
            {
                "document_json": {"body": []},
                "x": 1,
                "tasks": ["lean_from_json_structured", "elaborate"],
            },
        )

    def test_generated_file_contents_matches_codegen_pattern(self) -> None:
        contents = generated_file_contents(
            Path("/tmp/source.json"), "set_option maxHeartbeats 0\n", "theorem t : True := by\n  trivial\n"
        )

        self.assertTrue(contents.startswith("import Mathlib\nset_option"))
        self.assertIn("-- Generated by codegen.lean from /tmp/source.json", contents)
        self.assertTrue(contents.endswith("theorem t : True := by\n  trivial\n"))

    def test_format_elaboration_result_matches_sections(self) -> None:
        result = {
            "declarations": ["t"],
            "logs": ["warning: x"],
            "sorries": [[{"declaration_name": "t", "sorry_type": "True"}]],
            "sorries_after_purge": [],
        }

        formatted = format_elaboration_result(result)

        self.assertIn("Declarations (1): t", formatted)
        self.assertIn("Elaboration logs (1):", formatted)
        self.assertIn("Sorries (1 goal):", formatted)
        self.assertIn("Sorries after purge: none", formatted)

    def test_codegen_output_path_uses_codegen_directory(self) -> None:
        with tempfile.TemporaryDirectory() as tmpdir:
            root = Path(tmpdir)

            self.assertEqual(
                codegen_output_path(Path("examples/source.json"), root),
                root / "CodeGen" / "source.lean",
            )

    def test_append_elaboration_results_uses_comment_block(self) -> None:
        with tempfile.TemporaryDirectory() as tmpdir:
            out_file = Path(tmpdir) / "out.lean"
            out_file.write_text("import Mathlib\n", encoding="utf-8")

            append_elaboration_results(
                out_file,
                {"result": "success", "logs": [], "sorries": [], "sorries_after_purge": []},
            )

            contents = out_file.read_text(encoding="utf-8")
            self.assertIn("/-!\n## Elaboration results \n\n", contents)
            self.assertTrue(contents.endswith("\n\n-/\n"))

    def test_ensure_leanaide_http_server_starts_when_echo_fails(self) -> None:
        process = Mock()
        process.poll.return_value = None

        with (
            patch(
                "mathdoc_agent.pipeline.leanaide_server_echo_succeeds",
                side_effect=[False, True],
            ) as echo,
            patch(
                "mathdoc_agent.pipeline.start_leanaide_http_server",
                return_value=process,
            ) as start,
        ):
            result = ensure_leanaide_http_server(Path("/repo"), timeout=3)

        self.assertIs(result, process)
        start.assert_called_once_with(Path("/repo"))
        self.assertEqual(echo.call_count, 2)

    def test_start_leanaide_http_server_uses_top_level_server(self) -> None:
        with tempfile.TemporaryDirectory() as tmpdir:
            root = Path(tmpdir)
            (root / "leanaide_server.py").write_text("", encoding="utf-8")
            venv_python = root / "venv" / "bin" / "python"
            venv_python.parent.mkdir(parents=True)
            venv_python.write_text("", encoding="utf-8")
            process = Mock()

            with patch("subprocess.Popen", return_value=process) as popen:
                result = start_leanaide_http_server(root)

        self.assertIs(result, process)
        command = popen.call_args.args[0]
        self.assertEqual(Path(command[0]), venv_python)
        self.assertEqual(Path(command[1]).name, "leanaide_server.py")
        self.assertEqual(popen.call_args.kwargs["cwd"], root)
        self.assertEqual(
            popen.call_args.kwargs["env"]["LEANAIDE_COMMAND"],
            "lake exe leanaide_process",
        )
        self.assertEqual(popen.call_args.kwargs["env"]["VIRTUAL_ENV"], str(root / "venv"))

    def test_leanaide_server_python_prefers_project_venv(self) -> None:
        with tempfile.TemporaryDirectory() as tmpdir:
            root = Path(tmpdir)
            venv_python = root / "venv" / "bin" / "python"
            venv_python.parent.mkdir(parents=True)
            venv_python.write_text("", encoding="utf-8")

            self.assertEqual(leanaide_server_python(root), venv_python)

    def test_run_leanaide_server_codegen_writes_codegen_file(self) -> None:
        with tempfile.TemporaryDirectory() as tmpdir:
            root = Path(tmpdir)
            json_path = root / "example.json"
            response = {
                "result": "success",
                "document_code": "theorem t : True := by\n  trivial",
                "top_code": "import Mathlib\n",
                "declarations": ["t"],
                "logs": [],
                "sorries": [],
                "sorries_after_purge": [],
            }

            with (
                patch("mathdoc_agent.pipeline.ensure_leanaide_http_server") as ensure,
                patch(
                    "mathdoc_agent.pipeline.post_leanaide_json",
                    return_value=response,
                ) as post,
            ):
                ok = run_leanaide_server_codegen(
                    json_path, {"body": []}, root, timeout=3
                )

            self.assertTrue(ok)
            ensure.assert_called_once_with(root, url="http://localhost:7654", timeout=3)
            post.assert_called_once()
            self.assertEqual(
                post.call_args.args[0]["tasks"],
                ["lean_from_json_structured", "elaborate"],
            )
            out_file = root / "CodeGen" / "example.lean"
            contents = out_file.read_text(encoding="utf-8")
            self.assertIn("-- Generated by codegen.lean from", contents)
            self.assertIn("theorem t : True := by", contents)
            self.assertIn("## Elaboration results", contents)


if __name__ == "__main__":
    unittest.main()
