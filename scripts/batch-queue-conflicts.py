#!/usr/bin/env python3
"""Report text conflicts between one queued pull request and the rest of the batch queue.

The batch-queue workflow runs this from its trusted checkout. Pull request commits are fetched
as git objects and compared with `git merge-tree`. Nothing from a pull request is checked out
or run, and the only thing written to GitHub is one comment on the pull request being checked.

This finds pull requests that edit the same lines. It cannot tell whether pull requests that
merge cleanly also build together.
"""
from __future__ import annotations

import argparse
import json
from pathlib import Path
import subprocess
import sys
import tempfile

# Compared against, in this order: what is being built now, then what is waiting.
LABELS = ("building", "batch queue")
# Branches of this repository that hold a batch. Their pull requests are not compared.
BATCHES = "batch/"
# Hidden in the comment so that a later run edits it instead of adding another.
MARKER = "<!-- batch-queue-conflicts -->"
BOT = "github-actions[bot]"
# Most files a trial merge may have to read. Past this the report only counts shared files.
MERGE_LIMIT = 5000
# Matching a renamed file that was also edited means reading every file the other side added.
# Past this many changed files on the two sides together, only exact renames are followed.
RENAME_LIMIT = 2000
# Most file names listed for one pull request in the report.
LISTED = 10


def run(args, *, data=None, ok=(0,)):
    """Run a command and return (exit code, stdout). Any exit code outside `ok` is an error."""
    done = subprocess.run(args, input=data, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    if done.returncode not in ok:
        sys.stderr.write(done.stderr.decode("utf-8", "replace"))
        raise RuntimeError(f"{args[0]} failed with exit code {done.returncode}")
    return done.returncode, done.stdout


def git(repo, *args, data=None, ok=(0,), config=()):
    settings = [part for item in config for part in ("-c", item)]
    return run(["git", "-C", str(repo), *settings, *args], data=data, ok=ok)


# ---------------------------------------------------------------------------------------------
# Comparing two commits in a local repository.


class Comparison:
    """How one other pull request relates to the one being checked."""

    def __init__(self, kind, shared=(), conflicts=(), note=""):
        self.kind = kind  # "apart", "clean", "conflict", "too many" or "unknown"
        self.shared = list(shared)  # files both change
        self.conflicts = list(conflicts)  # files git cannot merge
        self.note = note


def changed(repo, base, head):
    """Paths that differ between two commits. Reads trees only."""
    _, out = git(repo, "diff", "--name-only", "--no-renames", "-z", base, head)
    return {path for path in out.split(b"\0") if path}


def fetch_blobs(repo, commits, paths):
    """Fetch the contents of `paths` at `commits` in one request, for a clone without blobs."""
    wanted = set()
    paths = sorted(paths)
    for commit in commits:
        for start in range(0, len(paths), 200):
            chunk = paths[start:start + 200]
            _, out = git(repo, "--literal-pathspecs", "ls-tree", "-r", "-z", commit, "--", *chunk)
            for entry in out.split(b"\0"):
                meta = entry.split(b"\t", 1)[0].split()
                if len(meta) == 3 and meta[1] == b"blob":
                    wanted.add(meta[2])
    if wanted:
        git(repo, "fetch", "--quiet", "--no-tags", "--no-write-fetch-head", "--recurse-submodules=no",
            "--filter=blob:none", "--stdin", "origin", data=b"\n".join(sorted(wanted)) + b"\n",
            config=("fetch.negotiationAlgorithm=noop",))


def compare(repo, base, ours, theirs, *, ours_fork=None, theirs_fork=None,
            merge_limit=MERGE_LIMIT, rename_limit=RENAME_LIMIT, partial=False):
    """Compare two pull request heads that share the ancestor `base`.

    A fork is the commit where a pull request left the main branch. What a pull request itself
    changes is measured from its fork, so that changes already on main, which one branch has
    and the other has not caught up with, are not counted against either.
    """
    mine = changed(repo, ours_fork or base, ours)
    other = changed(repo, theirs_fork or base, theirs)
    shared = sorted(mine & other)
    if not shared:
        return Comparison("apart")
    # The merge itself starts from `base`, and reads every file that differs on both sides.
    seen_mine, seen_other = changed(repo, base, ours), changed(repo, base, theirs)
    to_merge = seen_mine & seen_other
    if len(shared) > merge_limit or len(to_merge) > merge_limit:
        return Comparison("too many", shared)
    if partial:
        fetch_blobs(repo, (base, ours, theirs), to_merge)
    # git's merge ignores `merge.renames=false` in some versions, but it does honour the limit.
    config = () if len(seen_mine) + len(seen_other) <= rename_limit else ("merge.renameLimit=1",)
    code, out = git(repo, "merge-tree", "--write-tree", "--name-only", "--no-messages", "-z",
                    f"--merge-base={base}", ours, theirs, ok=(0, 1), config=config)
    # The first entry is the tree that was written; the conflicted paths follow. A conflict in
    # a file only one of the two changed is a conflict with main, which GitHub already shows.
    conflicts = sorted({path for path in out.split(b"\0")[1:] if path} & set(shared)) if code else []
    return Comparison("conflict" if conflicts else "clean", shared, conflicts)


# ---------------------------------------------------------------------------------------------
# Asking GitHub.


def gh(*args, data=None):
    _, out = run(["gh", "api", *args], data=data)
    return out.decode("utf-8", "replace")


def head_of(repo, number):
    return gh(f"repos/{repo}/pulls/{number}", "--jq", ".head.sha").strip()


def open_pulls(repo):
    """Every open pull request as {number: (head commit, labels, whether it is a batch)}.

    One listing answers for all of them. The workflow's token is allowed 1,000 requests an hour,
    shared with every other workflow, so nothing here asks GitHub about pull requests one by one.
    """
    rows = gh("--paginate", f"repos/{repo}/pulls?state=open&per_page=100", "--jq",
              '.[] | [.number, .head.sha, .head.ref, (.head.repo.full_name // ""), ([.labels[].name] | join("|"))] | @tsv')
    found = {}
    for row in rows.splitlines():
        number, sha, ref, home, labels = (row.split("\t") + [""] * 5)[:5]
        found[int(number)] = (sha, set(labels.split("|")), home == repo and ref.startswith(BATCHES))
    return found


def labelled(pulls, exclude):
    """Pull requests carrying one of LABELS, as {number: label}. The first label wins.

    A batch pull request is left out: what it contains is compared one pull request at a time.
    """
    found = {}
    for label in LABELS:
        for number, (_, labels, batch) in sorted(pulls.items()):
            if label in labels and number != exclude and not batch:
                found.setdefault(number, label)
    return found


def merge_base(work, ours, theirs):
    """The common ancestor of two commits that have been fetched, or None if they have none."""
    code, out = git(work, "merge-base", ours, theirs, ok=(0, 1))
    return out.decode().strip() if code == 0 else None


def survey(repo, number, work):
    """Compare pull request `number` with every other labelled one.

    Returns its head commit, the others as {number: label}, and {number: Comparison}.
    """
    main = gh(f"repos/{repo}", "--jq", ".default_branch").strip()
    pulls = open_pulls(repo)
    head = pulls[number][0] if number in pulls else head_of(repo, number)
    others = labelled(pulls, number)
    results = {}
    if not others:
        return head, others, results
    # One fetch of commits and trees, without file contents, for every pull request involved.
    # The history comes with it, so common ancestors are worked out here and not asked for.
    git(work, "init", "--quiet")
    git(work, "remote", "add", "origin", f"https://github.com/{repo}.git")
    git(work, "fetch", "--quiet", "--filter=blob:none", "--no-tags", "origin",
        f"+refs/heads/{main}:refs/remotes/origin/{main}", head, *sorted({pulls[other][0] for other in others}))
    trunk = f"refs/remotes/origin/{main}"
    fork = merge_base(work, trunk, head)
    for other in others:
        theirs = pulls[other][0]
        base, theirs_fork = merge_base(work, head, theirs), merge_base(work, trunk, theirs)
        if None in (fork, base, theirs_fork):
            results[other] = Comparison("unknown", note="no common ancestor")
            continue
        try:
            results[other] = compare(work, base, head, theirs, ours_fork=fork, theirs_fork=theirs_fork,
                                     partial=True)
        except RuntimeError as error:
            results[other] = Comparison("unknown", note=str(error))
    return head, others, results


# ---------------------------------------------------------------------------------------------
# Writing the report.


def show(path):
    """A file name as inline code. Names come from pull requests, so keep them inert."""
    text = path.decode("utf-8", "replace")
    text = "".join(char if char.isprintable() and char != "`" else "?" for char in text)
    return f"`{text[:200]}`"


def listing(paths):
    names = ", ".join(show(path) for path in paths[:LISTED])
    more = len(paths) - LISTED
    return names + (f" and {more:,} more" if more > 0 else "")


def count(number, noun):
    return f"{number:,} {noun}" if number == 1 else f"{number:,} {noun}s"


def report(number, head, others, results):
    """The comment text, and whether it says anything a maintainer has to act on."""
    def rows(kind):
        return [(other, others[other], results[other])
                for other in sorted(results) if results[other].kind == kind]

    lines = [MARKER]
    if not results:
        lines.append(f"No other pull request is labelled `{LABELS[0]}` or `{LABELS[1]}`, "
                     f"so #{number} was not compared with anything.")
        return "\n".join(lines) + "\n", False
    lines.append(f"#{number} was compared with the {count(len(results), 'other pull request')} "
                 f"labelled `{LABELS[0]}` or `{LABELS[1]}`.")

    conflicts, too_many, unknown = rows("conflict"), rows("too many"), rows("unknown")
    if conflicts:
        lines += ["", "It does not merge cleanly with:", ""]
        lines += [f"- #{other} (`{label}`): {count(len(result.conflicts), 'file')} in conflict: "
                  f"{listing(result.conflicts)}" for other, label, result in conflicts]
    if too_many:
        lines += ["", "It shares too many files with these for a trial merge here:", ""]
        lines += [f"- #{other} (`{label}`): {count(len(result.shared), 'file')} changed by both"
                  for other, label, result in too_many]
    if unknown:
        lines += ["", "These could not be compared:", ""]
        lines += [f"- #{other} (`{label}`): {result.note}" for other, label, result in unknown]
    clean = rows("clean")
    if clean:
        lines += ["", "It changes some of the same files as these, and git merges them without conflict:", ""]
        lines += [f"- #{other} (`{label}`): {count(len(result.shared), 'file')}" for other, label, result in clean]
    apart = rows("apart")
    if apart:
        lines += ["", "It has no file in common with " + ", ".join(f"#{other}" for other, _, _ in apart) + "."]
    lines += ["", f"This compares text only, at `{head[:10]}`. "
                  "Pull requests that merge cleanly can still fail to build together."]
    return "\n".join(lines) + "\n", bool(conflicts or too_many or unknown)


def publish(repo, number, body, needed):
    """Post the comment, or bring an earlier one up to date. Stay quiet when there is no news."""
    earlier = gh("--paginate", f"repos/{repo}/issues/{number}/comments?per_page=100", "--jq",
                 f'.[] | select(.user.login == "{BOT}" and (.body | contains("{MARKER}"))) | .id').split()
    payload = json.dumps({"body": body}).encode()
    if earlier:
        gh("-X", "PATCH", f"repos/{repo}/issues/comments/{earlier[-1]}", "--input", "-", data=payload)
        return "updated the earlier comment"
    if needed:
        gh("-X", "POST", f"repos/{repo}/issues/{number}/comments", "--input", "-", data=payload)
        return "posted a comment"
    return "nothing to report, so no comment"


def main():
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--repo", required=True, help="owner/name")
    parser.add_argument("--pr", required=True, type=int, help="the pull request to check")
    parser.add_argument("--comment", action="store_true", help="post or update the comment on the pull request")
    parser.add_argument("--summary", type=Path, help="append the report to this file")
    args = parser.parse_args()

    with tempfile.TemporaryDirectory() as work:
        head, others, results = survey(args.repo, args.pr, work)
    body, needed = report(args.pr, head, others, results)
    sys.stdout.write(body)
    if args.summary:
        with args.summary.open("a") as handle:
            handle.write(body)
    if args.comment:
        print(publish(args.repo, args.pr, body, needed))


if __name__ == "__main__":
    main()
