"""Fetch only pinned, sparse upstream trees; verify their selected file hashes."""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import subprocess
import urllib.request
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]


def git(directory: Path, *args: str) -> str:
    return subprocess.check_output(
        ["git", "-C", str(directory), *args], text=True,
        env={**os.environ, "GIT_TERMINAL_PROMPT": "0"},
    ).strip()


def fetch(manifest_path: Path) -> Path:
    manifest = json.loads(manifest_path.read_text())
    dest = manifest_path.parent / "upstream" / manifest["name"]
    dest.parent.mkdir(parents=True, exist_ok=True)
    if "files" in manifest:
        dest.mkdir(exist_ok=True)
        for name, entry in manifest["files"].items():
            if Path(name).name != name:
                raise ValueError("Download names must be simple filenames")
            path = dest / name
            if not path.exists():
                temporary = path.with_suffix(path.suffix + ".download")
                with urllib.request.urlopen(entry["url"], timeout=60) as source:
                    with temporary.open("wb") as output:
                        while block := source.read(1024 * 1024):
                            output.write(block)
                if hashlib.sha256(temporary.read_bytes()).hexdigest() != entry["sha256"]:
                    temporary.unlink()
                    raise ValueError(f"Download checksum mismatch: {name}")
                temporary.rename(path)
            if hashlib.sha256(path.read_bytes()).hexdigest() != entry["sha256"]:
                raise ValueError(f"Source checksum mismatch: {path}")
        return dest
    revision = manifest["revision"]
    if len(revision) != 40 or any(c not in "0123456789abcdef" for c in revision):
        raise ValueError("A full pinned commit is required")
    if not (dest / ".git").is_dir():
        subprocess.run(
            ["git", "clone", "--depth", "1", "--filter=blob:none", "--sparse",
             "--no-checkout", manifest["git"], str(dest)],
            check=True, env={**os.environ, "GIT_TERMINAL_PROMPT": "0"},
        )
        git(dest, "fetch", "--depth", "1", "origin", revision)
        git(dest, "sparse-checkout", "set", "--no-cone", *manifest["sparse"])
        git(dest, "checkout", "--detach", revision)
    if git(dest, "rev-parse", "HEAD") != revision:
        raise ValueError(f"Wrong source revision: {dest}")
    if git(dest, "status", "--porcelain", "--untracked-files=no"):
        raise ValueError(f"Modified upstream files: {dest}")
    for relative, expected in manifest["sha256"].items():
        path = dest / relative
        actual = hashlib.sha256(path.read_bytes()).hexdigest()
        if actual != expected:
            raise ValueError(f"Source checksum mismatch: {path}")
    return dest


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("manifest", type=Path, nargs="+")
    args = parser.parse_args()
    for manifest in args.manifest:
        print(fetch(manifest))


if __name__ == "__main__":
    main()
