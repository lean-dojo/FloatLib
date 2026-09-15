#!/usr/bin/env python3

"""Verify retained source evidence and disclose its relationship to the working tree."""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import re
import subprocess
import tarfile
import tempfile
from pathlib import Path, PurePosixPath


def digest(path: Path) -> str:
    value = hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b""):
            value.update(block)
    return value.hexdigest()


def read_assignments(path: Path) -> dict[str, str]:
    result: dict[str, str] = {}
    for line_number, line in enumerate(
        path.read_text(encoding="utf-8").splitlines(), start=1
    ):
        if not line or "=" not in line:
            raise ValueError(f"invalid assignment at {path}:{line_number}")
        key, value = line.split("=", 1)
        if not key or key in result:
            raise ValueError(f"duplicate or empty key at {path}:{line_number}")
        result[key] = value
    return result


def require_safe_path(raw: str) -> PurePosixPath:
    path = PurePosixPath(raw)
    if (
        not raw
        or path.is_absolute()
        or "\\" in raw
        or any(part in {"", ".", ".."} for part in path.parts)
        or path.as_posix() != raw
    ):
        raise ValueError(f"unsafe source path: {raw!r}")
    return path


def read_hashes(path: Path) -> dict[str, str]:
    result: dict[str, str] = {}
    for line_number, line in enumerate(
        path.read_text(encoding="utf-8").splitlines(), start=1
    ):
        if len(line) < 67 or line[64:66] != "  ":
            raise ValueError(f"invalid source hash at {path}:{line_number}")
        expected, raw = line[:64], line[66:]
        require_safe_path(raw)
        if (
            len(expected) != 64
            or expected.lower() != expected
            or any(character not in "0123456789abcdef" for character in expected)
        ):
            raise ValueError(f"invalid SHA-256 at {path}:{line_number}")
        if raw in result:
            raise ValueError(f"duplicate source path at {path}:{line_number}")
        result[raw] = expected
    return result


def run_git(arguments: list[str], cwd: Path) -> subprocess.CompletedProcess[str]:
    environment = os.environ.copy()
    environment["GIT_CONFIG_NOSYSTEM"] = "1"
    environment["GIT_CONFIG_GLOBAL"] = os.devnull
    try:
        return subprocess.run(
            ["git", "-C", str(cwd), *arguments],
            check=True,
            capture_output=True,
            text=True,
            env=environment,
        )
    except FileNotFoundError as error:
        raise ValueError("git is required to verify the repository bundle") from error
    except subprocess.CalledProcessError as error:
        detail = (error.stderr or error.stdout).strip()
        raise ValueError(
            f"git {' '.join(arguments)} failed"
            + (f": {detail}" if detail else "")
        ) from error


def bundle_heads(output: str) -> dict[str, str]:
    result: dict[str, str] = {}
    object_length: int | None = None
    for line_number, line in enumerate(output.splitlines(), start=1):
        fields = line.split(" ", 1)
        if len(fields) != 2:
            raise ValueError(f"invalid bundle head at line {line_number}: {line!r}")
        object_id, reference = fields
        if (
            len(object_id) not in {40, 64}
            or object_id.lower() != object_id
            or not re.fullmatch(r"[0-9a-f]+", object_id)
        ):
            raise ValueError(
                f"invalid object ID in bundle head at line {line_number}: "
                f"{object_id!r}"
            )
        if object_length is None:
            object_length = len(object_id)
        elif len(object_id) != object_length:
            raise ValueError("bundle advertises mixed object-ID lengths")
        if not reference or reference in result:
            raise ValueError(
                f"empty or duplicate bundle reference at line {line_number}: "
                f"{reference!r}"
            )
        result[reference] = object_id
    if not result:
        raise ValueError("repository bundle advertises no references")
    return result


def verify_bundle(bundle: Path, snapshot: dict[str, str]) -> None:
    head_revision = snapshot["head_revision"]
    if (
        len(head_revision) not in {40, 64}
        or head_revision.lower() != head_revision
        or not re.fullmatch(r"[0-9a-f]+", head_revision)
    ):
        raise ValueError(f"invalid head_revision: {head_revision!r}")

    with tempfile.TemporaryDirectory(prefix="floatlib-bundle-") as raw_temporary:
        repository = Path(raw_temporary) / "repository.git"
        subprocess.run(
            ["git", "init", "--bare", "--quiet", str(repository)],
            check=True,
            capture_output=True,
            text=True,
        )
        run_git(["bundle", "verify", str(bundle)], repository)
        advertised = bundle_heads(
            run_git(["bundle", "list-heads", str(bundle)], repository).stdout
        )
        unpacked = bundle_heads(
            run_git(["bundle", "unbundle", str(bundle)], repository).stdout
        )
        if unpacked != advertised:
            raise ValueError("bundle heads differ between inspection and unpacking")
        if len(head_revision) != len(next(iter(advertised.values()))):
            raise ValueError("head_revision uses a different hash format from the bundle")
        try:
            object_type = run_git(
                ["cat-file", "-t", head_revision],
                repository,
            ).stdout.strip()
        except ValueError as error:
            raise ValueError(
                f"head_revision is not contained in the repository bundle: "
                f"{head_revision}"
            ) from error
        if object_type != "commit":
            raise ValueError(
                f"head_revision is not a commit in the repository bundle: "
                f"{head_revision} ({object_type!r})"
            )


def verify_archive(
    shared: Path,
    snapshot: dict[str, str],
    repository_bundle: Path | None = None,
) -> None:
    archive = shared / "FloatLib-source.tar.gz"
    archive_digest = snapshot["source_archive_sha256"]
    omitted: dict[str, str] = {}
    publication_path = shared / "public-source-archive.json"
    if publication_path.exists():
        publication = json.loads(publication_path.read_text(encoding="utf-8"))
        if not isinstance(publication, dict) or set(publication) != {
            "archive", "sha256", "original_archive_sha256", "omitted_files"
        }:
            raise ValueError("invalid public source archive metadata")
        if publication["archive"] != "FloatLib-source-public.tar.gz":
            raise ValueError("unexpected public source archive name")
        if publication["original_archive_sha256"] != archive_digest:
            raise ValueError("public archive metadata names a different original capture")
        omitted = publication["omitted_files"]
        if not isinstance(omitted, dict) or not omitted:
            raise ValueError("public archive must identify its omitted history bundles")
        for raw in omitted:
            path = require_safe_path(raw)
            if path.parent.as_posix() not in {
                "tests/results/main/provenance", "benchmarks/results/main/provenance"
            } or not path.name.endswith("-repository.bundle"):
                raise ValueError(f"public source archive cannot omit source file: {raw}")
        archive = shared / publication["archive"]
        archive_digest = publication["sha256"]
    hashes_path = shared / "source-files.sha256"
    list_path = shared / "source-files.nul"
    status_path = shared / "worktree-status.txt"
    patch_path = shared / "worktree.patch"
    for path in (
        archive,
        hashes_path,
        list_path,
        status_path,
        patch_path,
    ):
        if not path.is_file():
            raise ValueError(f"missing source provenance file: {path}")

    expected_digests = {
        archive: archive_digest,
        hashes_path: snapshot["source_file_hashes_sha256"],
        list_path: snapshot["source_file_list_sha256"],
        status_path: snapshot["worktree_status_sha256"],
        patch_path: snapshot["worktree_patch_sha256"],
    }
    if repository_bundle is not None:
        if not repository_bundle.is_file():
            raise ValueError(f"missing repository bundle: {repository_bundle}")
        expected_digests[repository_bundle] = snapshot["repository_bundle_sha256"]
    for path, expected in expected_digests.items():
        actual = digest(path)
        if actual != expected:
            raise ValueError(
                f"source provenance digest differs for {path}: "
                f"{actual} != {expected}"
            )

    if repository_bundle is not None:
        verify_bundle(repository_bundle, snapshot)

    hashes = read_hashes(hashes_path)
    for raw, expected in omitted.items():
        if raw not in hashes or hashes[raw] != expected:
            raise ValueError(f"omitted bundle does not match the original source ledger: {raw}")
    listed_raw = list_path.read_bytes().split(b"\0")
    if not listed_raw or listed_raw[-1] != b"":
        raise ValueError(f"source list is not NUL terminated: {list_path}")
    try:
        listed = [item.decode("utf-8") for item in listed_raw[:-1]]
    except UnicodeDecodeError as error:
        raise ValueError(f"source list is not UTF-8: {list_path}") from error
    if listed != list(hashes):
        raise ValueError("source file list and source hash order differ")
    if int(snapshot["source_file_count"]) != len(hashes):
        raise ValueError(
            "source file count differs: "
            f"{len(hashes)} != {snapshot['source_file_count']}"
        )

    archived: dict[str, str] = {}
    with tarfile.open(archive, "r:gz") as stream:
        for member in stream:
            require_safe_path(member.name)
            if not member.isfile():
                raise ValueError(
                    f"source archive contains a non-regular member: {member.name}"
                )
            if member.name in archived:
                raise ValueError(
                    f"source archive contains a duplicate member: {member.name}"
                )
            extracted = stream.extractfile(member)
            if extracted is None:
                raise ValueError(f"cannot read source archive member: {member.name}")
            value = hashlib.sha256()
            for block in iter(lambda: extracted.read(1024 * 1024), b""):
                value.update(block)
            archived[member.name] = value.hexdigest()
    retained = {path: value for path, value in hashes.items() if path not in omitted}
    if archived != retained:
        missing = sorted(set(retained) - set(archived))
        extra = sorted(set(archived) - set(retained))
        changed = sorted(
            path
            for path in set(retained) & set(archived)
            if retained[path] != archived[path]
        )
        raise ValueError(
            "source archive differs from its hash ledger: "
            f"missing={missing}, extra={extra}, changed={changed}"
        )
    if omitted:
        print(
            f"Verified {len(archived)} archived files against the original source ledger; "
            f"omitted {len(omitted)} private Git history bundle(s)."
        )


def verify_attached(
    shared: Path,
    attached: Path,
    snapshot: dict[str, str],
    run_mode: str,
) -> None:
    pairs = {
        "source-snapshot.txt": "SNAPSHOT.txt",
        "source-files.sha256": "source-files.sha256",
        "source-files.nul": "source-files.nul",
        "worktree-status.txt": "worktree-status.txt",
        "worktree.patch": "worktree.patch",
    }
    for attached_name, shared_name in pairs.items():
        attached_path = attached / attached_name
        shared_path = shared / shared_name
        if not attached_path.is_file():
            raise ValueError(f"missing attached provenance file: {attached_path}")
        if attached_path.read_bytes() != shared_path.read_bytes():
            raise ValueError(
                f"attached provenance differs from source capture: {attached_path}"
            )

    cluster = read_assignments(attached / "cluster-status.txt")
    campaign = read_assignments(attached / "campaign-status.txt")
    expected = {
        "campaign_id": snapshot["campaign_id"],
        "run_mode": run_mode,
    }
    for key, value in expected.items():
        if cluster.get(key) != value:
            raise ValueError(
                f"cluster status {key} differs: {cluster.get(key)!r} != {value!r}"
            )
        if campaign.get(key) != value:
            raise ValueError(
                f"campaign status {key} differs: "
                f"{campaign.get(key)!r} != {value!r}"
            )
    codes: dict[str, int] = {}
    for key in ("run_exit_code", "packaging_exit_code", "final_exit_code"):
        raw = campaign.get(key)
        try:
            value = int(raw) if raw is not None else -1
        except ValueError as error:
            raise ValueError(
                f"campaign status {key} is not an integer: {raw!r}"
            ) from error
        if not 0 <= value <= 255:
            raise ValueError(f"campaign status {key} is out of range: {value}")
        codes[key] = value
    if cluster.get("run_exit_code") != str(codes["run_exit_code"]):
        raise ValueError(
            "cluster and campaign run exit codes differ: "
            f"{cluster.get('run_exit_code')!r} != {codes['run_exit_code']}"
        )
    derived_final = (
        codes["run_exit_code"]
        if codes["run_exit_code"] != 0
        else codes["packaging_exit_code"]
    )
    if codes["final_exit_code"] != derived_final:
        raise ValueError(
            "campaign final exit code is inconsistent: "
            f"{codes['final_exit_code']} != {derived_final}"
        )
    for required in ("run-entrypoint.sh", f"{run_mode}-job.yaml"):
        if not (attached / required).is_file():
            raise ValueError(f"missing attached campaign file: {attached / required}")


def source_input_group(raw: str) -> str | None:
    """Select source inputs, excluding prose, the website, and generated results."""
    path = PurePosixPath(raw)
    if any(part in {".lake", "results", "__pycache__"} for part in path.parts):
        return None
    if path.parts[0] in {"site", "paper", "papers", "blueprint"}:
        return None
    if path.suffix.lower() in {
        ".md", ".rst", ".png", ".svg", ".pdf", ".jpg", ".jpeg", ".webp", ".ico",
    } or raw.startswith("benchmarks/docs/"):
        return None
    if path.name in {"lakefile.lean", "lakefile.toml", "lake-manifest.json", "lean-toolchain"}:
        return "library and build inputs"
    if (
        raw in {"FloatLib.lean", "LeanFloat.lean"}
        or path.parts[0] in {"FloatLib", "LeanFloat"}
    ) and path.suffix == ".lean":
        return "library and build inputs"
    if path.parts[0] in {"tests", "benchmarks", "scripts"}:
        return "test and benchmark inputs"
    return None


def source_ledger_digest(hashes: dict[str, str]) -> str:
    ledger = "".join(f"{value}  {path}\n" for path, value in sorted(hashes.items()))
    return hashlib.sha256(ledger.encode("utf-8")).hexdigest()


def disclose_current_sources(
    shared: Path, snapshot: dict[str, str], source_root: Path
) -> None:
    measured = {
        path: value
        for path, value in read_hashes(shared / "source-files.sha256").items()
        if source_input_group(path) is not None
    }
    if not measured:
        raise ValueError("source capture contains no comparable source inputs")
    source_paths = run_git(
        ["ls-files", "-z", "--cached", "--others", "--exclude-standard"],
        source_root,
    ).stdout.split("\0")
    current: dict[str, str] = {}
    for raw in sorted(set(source_paths) - {""}):
        if source_input_group(raw) is None:
            continue
        path = source_root / require_safe_path(raw)
        if path.is_file():
            current[raw] = digest(path)
    try:
        revision = run_git(["rev-parse", "--verify", "HEAD"], source_root).stdout.strip()
    except ValueError:
        revision = "unavailable (working files are still compared)"
    print(
        f"Measured snapshot: base revision {snapshot['head_revision']}; "
        f"source ledger SHA-256 {snapshot['source_file_hashes_sha256']}."
    )
    print(f"Current checkout revision: {revision}.")
    print(
        "Comparing recorded source paths and bytes, including uncommitted files. "
        "Documentation files, website files, generated results, and the Git revision alone "
        "do not change this comparison."
    )
    for group in ("library and build inputs", "test and benchmark inputs"):
        before = {
            path: value for path, value in measured.items()
            if source_input_group(path) == group
        }
        after = {
            path: value for path, value in current.items()
            if source_input_group(path) == group
        }
        changed = sum(before[path] != after[path] for path in before.keys() & after.keys())
        added = len(after.keys() - before.keys())
        removed = len(before.keys() - after.keys())
        status = "match" if before == after else "differ"
        print(
            f"{group.capitalize()}: {status}; "
            f"changed={changed}, added={added}, removed={removed}."
        )
        print(f"  measured SHA-256: {source_ledger_digest(before)}")
        print(f"  current SHA-256:  {source_ledger_digest(after)}")
    if measured == current:
        print("Compared source inputs match; measurements describe the recorded environment.")
    else:
        print(
            "Current sources differ from the measured snapshot. "
            "Saved evidence remains valid for that snapshot; "
            "these checks do not rerun comparisons or timings on the current sources."
        )


def verify(
    shared: Path,
    attached: Path,
    run_mode: str,
    source_root: Path | None = None,
    repository_bundle: Path | None = None,
) -> None:
    snapshot_path = shared / "SNAPSHOT.txt"
    if not snapshot_path.is_file():
        raise ValueError(f"missing source snapshot: {snapshot_path}")
    snapshot = read_assignments(snapshot_path)
    required = {
        "campaign_id",
        "created_utc",
        "head_revision",
        "branch",
        "source_file_count",
        "source_archive_sha256",
        "repository_bundle_sha256",
        "source_file_hashes_sha256",
        "source_file_list_sha256",
        "worktree_status_sha256",
        "worktree_patch_sha256",
    }
    missing = sorted(required - set(snapshot))
    if missing:
        raise ValueError(f"source snapshot is missing keys: {missing}")
    verify_archive(shared, snapshot, repository_bundle)
    verify_attached(
        shared,
        attached,
        snapshot,
        run_mode,
    )
    print(
        f"verified source capture {snapshot['campaign_id']} "
        f"and {run_mode} status"
    )
    if repository_bundle is None:
        print("Verified the measured source archive; private Git history was not checked.")
    else:
        print("Verified the original repository bundle and recorded Git revision.")
    disclose_current_sources(
        shared, snapshot, source_root or Path(__file__).resolve().parents[2]
    )


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("shared", type=Path)
    parser.add_argument("attached", type=Path)
    parser.add_argument("--run-mode", choices=("benchmark", "conformance"), required=True)
    parser.add_argument(
        "--source-root",
        type=Path,
        default=Path(__file__).resolve().parents[2],
        help="working tree to compare with the measured source capture",
    )
    parser.add_argument(
        "--repository-bundle",
        type=Path,
        help="also verify an original Git history bundle kept outside the public result tree",
    )
    arguments = parser.parse_args()
    try:
        verify(
            arguments.shared.resolve(),
            arguments.attached.resolve(),
            arguments.run_mode,
            arguments.source_root.resolve(),
            arguments.repository_bundle.resolve() if arguments.repository_bundle else None,
        )
    except (KeyError, OSError, tarfile.TarError, ValueError) as error:
        raise SystemExit(str(error)) from error


if __name__ == "__main__":
    main()
