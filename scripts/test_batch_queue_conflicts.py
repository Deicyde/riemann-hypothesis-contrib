#!/usr/bin/env python3
"""Comparison and report checks on a small local repository; no GitHub calls."""
import importlib.util
import json
import os
from pathlib import Path
import subprocess
import tempfile
import unittest
from unittest.mock import patch

SCRIPT = Path(__file__).with_name("batch-queue-conflicts.py")
spec = importlib.util.spec_from_file_location("batch_queue_conflicts", SCRIPT)
conflicts = importlib.util.module_from_spec(spec)
spec.loader.exec_module(conflicts)

LINES = "".join(f"line {number}\n" for number in range(1, 21))
IDENTITY = {"GIT_AUTHOR_NAME": "t", "GIT_AUTHOR_EMAIL": "t@example.invalid",
            "GIT_COMMITTER_NAME": "t", "GIT_COMMITTER_EMAIL": "t@example.invalid"}


class Repository:
    """A throwaway repository with one base commit and one branch per case."""

    def __init__(self, root):
        self.root = Path(root)
        self.git("init", "--quiet", "--initial-branch=main")
        for name in ("a.txt", "b.txt", "c.txt", "odd `name` ₂.txt"):
            (self.root / name).write_text("".join(f"{name} {line}" for line in LINES.splitlines(keepends=True)))
        self.base = self.commit("base")

    def git(self, *args):
        done = subprocess.run(["git", "-C", str(self.root), "-c", "commit.gpgsign=false", *args],
                              check=True, capture_output=True, env={**os.environ, **IDENTITY})
        return done.stdout.decode().strip()

    def commit(self, message):
        self.git("add", "--all")
        self.git("commit", "--quiet", "--message", message)
        return self.git("rev-parse", "HEAD")

    def branch(self, name, change):
        """Make a commit on a new branch off the base, and return it."""
        self.git("checkout", "--quiet", "-b", name, self.base)
        change(self.root)
        return self.commit(name)


def edit(name, line, text):
    def change(root):
        lines = (root / name).read_text().splitlines(keepends=True)
        lines[line - 1] = text + "\n"
        (root / name).write_text("".join(lines))
    return change


class Comparisons(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.directory = tempfile.TemporaryDirectory()
        cls.repo = Repository(cls.directory.name)
        cls.ours = cls.repo.branch("ours", lambda root: (edit("a.txt", 2, "ours")(root), edit("b.txt", 2, "ours")(root)))

    @classmethod
    def tearDownClass(cls):
        cls.directory.cleanup()

    def against(self, name, change, **options):
        theirs = self.repo.branch(name, change)
        return conflicts.compare(self.repo.root, self.repo.base, self.ours, theirs, **options)

    def test_different_files_are_apart(self):
        result = self.against("apart", edit("c.txt", 2, "theirs"))
        self.assertEqual((result.kind, result.shared, result.conflicts), ("apart", [], []))

    def test_same_line_is_a_conflict(self):
        result = self.against("same-line", edit("a.txt", 2, "theirs"))
        self.assertEqual((result.kind, result.shared, result.conflicts), ("conflict", [b"a.txt"], [b"a.txt"]))

    def test_same_file_different_lines_merges_cleanly(self):
        result = self.against("other-line", edit("a.txt", 18, "theirs"))
        self.assertEqual((result.kind, result.shared, result.conflicts), ("clean", [b"a.txt"], []))

    def test_identical_change_merges_cleanly(self):
        result = self.against("same-change", edit("a.txt", 2, "ours"))
        self.assertEqual(result.kind, "clean")

    def test_edit_against_delete_is_a_conflict(self):
        result = self.against("delete", lambda root: (root / "a.txt").unlink())
        self.assertEqual((result.kind, result.conflicts), ("conflict", [b"a.txt"]))

    def test_edit_follows_a_rename_when_both_sides_are_small(self):
        result = self.against("rename", lambda root: (root / "b.txt").rename(root / "moved.txt"))
        self.assertEqual((result.kind, result.shared), ("clean", [b"b.txt"]))

    def test_exact_rename_is_still_followed_on_large_pull_requests(self):
        result = self.against("rename-large", lambda root: (root / "b.txt").rename(root / "moved2.txt"), rename_limit=0)
        self.assertEqual((result.kind, result.shared), ("clean", [b"b.txt"]))

    @staticmethod
    def rename_and_edit(suffix):
        def change(root):
            for name in ("b.txt", "c.txt"):
                (root / name).rename(root / f"{name}.{suffix}")
                edit(f"{name}.{suffix}", 18, "theirs")(root)
        return change

    def test_edited_rename_is_followed_when_both_sides_are_small(self):
        result = self.against("renames-edited", self.rename_and_edit("one"))
        self.assertEqual((result.kind, result.shared), ("clean", [b"b.txt"]))

    def test_edited_rename_is_a_conflict_on_large_pull_requests(self):
        result = self.against("renames-edited-large", self.rename_and_edit("two"), rename_limit=0)
        self.assertEqual((result.kind, result.conflicts), ("conflict", [b"b.txt"]))

    def test_too_many_shared_files_skips_the_merge(self):
        result = self.against("many", edit("a.txt", 2, "theirs"), merge_limit=0)
        self.assertEqual((result.kind, result.shared, result.conflicts), ("too many", [b"a.txt"], []))


class LaterForks(unittest.TestCase):
    """The other pull request left main after main had moved on."""

    @classmethod
    def setUpClass(cls):
        cls.directory = tempfile.TemporaryDirectory()
        cls.repo = Repository(cls.directory.name)
        # Ours edits a.txt and c.txt. Main then changes the same line of c.txt, and b.txt.
        cls.ours = cls.repo.branch("ours", lambda root: (edit("a.txt", 2, "ours")(root), edit("c.txt", 2, "ours")(root)))
        cls.main = cls.repo.branch("later-main", lambda root: (edit("c.txt", 2, "main")(root), edit("b.txt", 2, "main")(root)))

    @classmethod
    def tearDownClass(cls):
        cls.directory.cleanup()

    def against(self, name, change):
        self.repo.git("checkout", "--quiet", "-b", name, self.main)
        change(self.repo.root)
        theirs = self.repo.commit(name)
        return conflicts.compare(self.repo.root, self.repo.base, self.ours, theirs, theirs_fork=self.main)

    def test_changes_already_on_main_are_not_the_other_pull_requests(self):
        # Ours conflicts with main in c.txt, but theirs never touched c.txt.
        result = self.against("elsewhere", edit("odd `name` ₂.txt", 2, "theirs"))
        self.assertEqual((result.kind, result.shared, result.conflicts), ("apart", [], []))

    def test_only_conflicts_between_the_two_are_reported(self):
        result = self.against("same-line-later", edit("a.txt", 2, "theirs"))
        self.assertEqual((result.kind, result.shared, result.conflicts), ("conflict", [b"a.txt"], [b"a.txt"]))

    def test_shared_file_that_merges_is_clean_despite_a_conflict_with_main(self):
        result = self.against("other-line-later", edit("a.txt", 18, "theirs"))
        self.assertEqual((result.kind, result.shared, result.conflicts), ("clean", [b"a.txt"], []))


class Reports(unittest.TestCase):
    def test_nothing_to_compare(self):
        body, needed = conflicts.report(7, "0" * 40, {}, {})
        self.assertFalse(needed)
        self.assertIn("was not compared with anything", body)
        self.assertTrue(body.startswith(conflicts.MARKER))

    def test_quiet_when_everything_merges(self):
        others = {11: "batch queue", 12: "building"}
        results = {11: conflicts.Comparison("apart"), 12: conflicts.Comparison("clean", [b"a.txt"])}
        body, needed = conflicts.report(7, "abcdef0123" + "0" * 30, others, results)
        self.assertFalse(needed)
        self.assertIn("compared with the 2 other pull requests", body)
        self.assertIn("- #12 (`building`): 1 file", body)
        self.assertIn("no file in common with #11.", body)
        self.assertIn("at `abcdef0123`", body)

    def test_conflicts_need_a_comment_and_long_lists_are_cut(self):
        files = [f"src/F{number:02}.lean".encode() for number in range(25)]
        others = {11: "batch queue", 12: "building", 13: "batch queue"}
        results = {11: conflicts.Comparison("conflict", files, files),
                   12: conflicts.Comparison("too many", files),
                   13: conflicts.Comparison("unknown", note="GitHub reports no common ancestor")}
        body, needed = conflicts.report(7, "0" * 40, others, results)
        self.assertTrue(needed)
        self.assertIn("- #11 (`batch queue`): 25 files in conflict: `src/F00.lean`", body)
        self.assertIn("`src/F09.lean` and 15 more", body)
        self.assertNotIn("src/F10.lean", body)
        self.assertIn("- #12 (`building`): 25 files changed by both", body)
        self.assertIn("- #13 (`batch queue`): GitHub reports no common ancestor", body)

    def test_one_file_is_singular(self):
        results = {11: conflicts.Comparison("conflict", [b"a.txt"], [b"a.txt"])}
        body, _ = conflicts.report(7, "0" * 40, {11: "batch queue"}, results)
        self.assertIn("compared with the 1 other pull request labelled", body)
        self.assertIn("1 file in conflict: `a.txt`", body)

    def test_file_names_cannot_break_out_of_code_formatting(self):
        self.assertEqual(conflicts.show("odd `name` ₂.txt".encode()), "`odd ?name? ₂.txt`")
        self.assertEqual(conflicts.show(b"line\nbreak @someone <b>.txt"), "`line?break @someone <b>.txt`")
        self.assertEqual(conflicts.show(b"\xff\xfe.txt"), "`��.txt`")
        self.assertEqual(len(conflicts.show(b"x" * 500)), 202)


class Publishing(unittest.TestCase):
    """Which GitHub calls a report leads to. `gh` is replaced; nothing leaves this machine."""

    def publish(self, earlier, needed):
        calls = []

        def fake(*args, data=None):
            calls.append((args, data))
            return earlier if "--paginate" in args else ""

        with patch.object(conflicts, "gh", fake):
            said = conflicts.publish("o/r", 7, "the report", needed)
        writes = [(args[1], args[2], json.loads(data)) for args, data in calls if args[0] == "-X"]
        return said, writes

    def test_first_report_with_news_is_posted(self):
        said, writes = self.publish("", True)
        self.assertEqual(writes, [("POST", "repos/o/r/issues/7/comments", {"body": "the report"})])
        self.assertEqual(said, "posted a comment")

    def test_no_news_and_no_earlier_comment_stays_quiet(self):
        said, writes = self.publish("", False)
        self.assertEqual(writes, [])
        self.assertEqual(said, "nothing to report, so no comment")

    def test_earlier_comment_is_edited_even_when_the_news_is_good(self):
        for needed in (True, False):
            said, writes = self.publish("41\n42\n", needed)
            self.assertEqual(writes, [("PATCH", "repos/o/r/issues/comments/42", {"body": "the report"})])
            self.assertEqual(said, "updated the earlier comment")


if __name__ == "__main__":
    unittest.main()
