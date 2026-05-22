from __future__ import annotations

import tempfile
import unittest
from pathlib import Path
from unittest.mock import Mock, patch

from mathdoc_agent.pipeline import (
    _stderr_line_startswith,
    find_leanaide_dir,
    find_leanaide_dir_from_paths,
    is_leanaide_lakefile,
    lakefile_project_name,
    post_leanaide_json,
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


if __name__ == "__main__":
    unittest.main()
