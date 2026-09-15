#!/usr/bin/env python3

"""Write a deterministic SHA-256 manifest for a result directory."""

from __future__ import annotations

import argparse
import hashlib
import os
from pathlib import Path


HEADER = "path\tbytes\tsha256\n"


def digest(path: Path) -> str:
    value = hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b""):
            value.update(block)
    return value.hexdigest()


def regular_files(root: Path, manifest: Path) -> list[Path]:
    files: list[Path] = []
    for directory, names, filenames in os.walk(root, followlinks=False):
        parent = Path(directory)
        for name in names:
            path = parent / name
            if path.is_symlink():
                raise ValueError(f"result bundle contains a symbolic link: {path}")
        for name in filenames:
            path = parent / name
            if path.is_symlink():
                raise ValueError(f"result bundle contains a symbolic link: {path}")
            if path == manifest:
                continue
            if not path.is_file():
                raise ValueError(f"result bundle contains a non-regular file: {path}")
            files.append(path)
    return sorted(files, key=lambda path: path.relative_to(root).as_posix())


def write_manifest(root: Path) -> int:
    root = root.resolve()
    if not root.is_dir():
        raise ValueError(f"result directory does not exist: {root}")
    manifest = root / "MANIFEST.tsv"
    temporary = root / ".MANIFEST.tsv.tmp"
    if temporary.exists():
        raise ValueError(f"temporary manifest already exists: {temporary}")

    files = regular_files(root, manifest)
    try:
        with temporary.open("x", encoding="utf-8", newline="") as stream:
            stream.write(HEADER)
            for path in files:
                relative = path.relative_to(root).as_posix()
                stream.write(
                    f"{relative}\t{path.stat().st_size}\t{digest(path)}\n"
                )
        temporary.replace(manifest)
    finally:
        temporary.unlink(missing_ok=True)
    return len(files)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("root", type=Path)
    arguments = parser.parse_args()
    try:
        count = write_manifest(arguments.root)
    except (OSError, ValueError) as error:
        raise SystemExit(str(error)) from error
    print(f"wrote manifest for {count} files under {arguments.root}")


if __name__ == "__main__":
    main()
