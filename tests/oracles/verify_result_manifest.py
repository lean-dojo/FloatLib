#!/usr/bin/env python3

"""Verify that a result directory agrees exactly with its SHA-256 manifest."""

from __future__ import annotations

import argparse
import csv
import hashlib
from pathlib import Path, PurePosixPath


HEADER = ["path", "bytes", "sha256"]


def digest(path: Path) -> str:
    value = hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b""):
            value.update(block)
    return value.hexdigest()


def checked_relative_path(raw: str) -> PurePosixPath:
    path = PurePosixPath(raw)
    if (
        not raw
        or path.is_absolute()
        or "\\" in raw
        or any(part in {"", ".", ".."} for part in path.parts)
        or path.as_posix() != raw
    ):
        raise ValueError(f"unsafe or non-canonical manifest path: {raw!r}")
    return path


def verify(root: Path) -> int:
    root = root.resolve()
    manifest = root / "MANIFEST.tsv"
    if not manifest.is_file():
        raise ValueError(f"missing manifest: {manifest}")

    listed: dict[str, tuple[int, str]] = {}
    previous_path: str | None = None
    with manifest.open(newline="", encoding="utf-8") as stream:
        reader = csv.reader(stream, delimiter="\t")
        try:
            header = next(reader)
        except StopIteration as error:
            raise ValueError(f"empty manifest: {manifest}") from error
        if header != HEADER:
            raise ValueError(
                f"unexpected header in {manifest}: {header!r}"
            )
        for line_number, row in enumerate(reader, start=2):
            if len(row) != len(HEADER):
                raise ValueError(
                    f"unexpected field count in {manifest}:{line_number}: "
                    f"{len(row)}"
                )
            raw_path, raw_size, expected_digest = row
            checked_relative_path(raw_path)
            if previous_path is not None and raw_path <= previous_path:
                raise ValueError(
                    f"manifest paths are not in canonical order at "
                    f"{manifest}:{line_number}: {raw_path!r} follows "
                    f"{previous_path!r}"
                )
            previous_path = raw_path
            try:
                size = int(raw_size)
            except ValueError as error:
                raise ValueError(
                    f"invalid byte count in {manifest}:{line_number}"
                ) from error
            if size < 0:
                raise ValueError(
                    f"negative byte count in {manifest}:{line_number}"
                )
            if (
                len(expected_digest) != 64
                or expected_digest.lower() != expected_digest
                or any(
                    character not in "0123456789abcdef"
                    for character in expected_digest
                )
            ):
                raise ValueError(
                    f"invalid SHA-256 in {manifest}:{line_number}"
                )
            listed[raw_path] = (size, expected_digest)

    actual: dict[str, Path] = {}
    for path in root.rglob("*"):
        if path.is_symlink():
            raise ValueError(f"result bundle contains a symbolic link: {path}")
        if path.is_file() and path != manifest:
            relative = path.relative_to(root).as_posix()
            actual[relative] = path

    missing = sorted(set(listed) - set(actual))
    extra = sorted(set(actual) - set(listed))
    if missing or extra:
        raise ValueError(
            f"manifest tree differs at {root}: missing={missing}, extra={extra}"
        )

    for relative, (expected_size, expected_digest) in sorted(listed.items()):
        path = actual[relative]
        actual_size = path.stat().st_size
        actual_digest = digest(path)
        if actual_size != expected_size or actual_digest != expected_digest:
            raise ValueError(
                f"manifest mismatch for {path}: "
                f"bytes={actual_size}/{expected_size}, "
                f"sha256={actual_digest}/{expected_digest}"
            )

    return len(listed)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("root", type=Path)
    arguments = parser.parse_args()
    try:
        count = verify(arguments.root)
    except ValueError as error:
        raise SystemExit(str(error)) from error
    print(f"verified {count} files under {arguments.root}")


if __name__ == "__main__":
    main()
