#!/usr/bin/env python3
"""Reject private infrastructure metadata in published files, including nested archives."""

from __future__ import annotations

import io
from pathlib import Path
import re
import subprocess
import tarfile
import zipfile


ROOT = Path(__file__).resolve().parents[2]
PATTERNS = {
    "private mount": re.compile(rb"/(?:efs)/robert"),
    "local home": re.compile(
        rb"/(?:home)/(?!(?:coq|rocq|runner|lean)(?:/|\s|$))[^/\s\x00\"'<>]+"
    ),
    "local mount": re.compile(rb"/(?:mnt)/[^/\s\x00\"'<>]+"),
    "internal host": re.compile(
        rb"(?:ip-[0-9]+-[0-9]+-[0-9]+-[0-9]+(?:\.[A-Za-z0-9.-]+)?"
        rb"|[A-Za-z0-9.-]+\.compute\.internal)"
    ),
    "private registry": re.compile(
        rb"[0-9]{12}\.dkr\.ecr\.[A-Za-z0-9-]+\.amazonaws\.com"
    ),
}


def inspect(data: bytes, name: str, depth: int = 0) -> list[str]:
    """Report categories and member names without printing the private values."""
    findings = [f"{name}: {kind}" for kind, pattern in PATTERNS.items()
                if pattern.search(data)]
    if depth > 6:
        raise ValueError(f"archive nesting exceeds the publication check limit: {name}")
    if data.startswith(b"PK\x03\x04"):
        with zipfile.ZipFile(io.BytesIO(data)) as archive:
            for member in archive.infolist():
                if not member.is_dir():
                    findings.extend(inspect(archive.read(member),
                                            f"{name}!{member.filename}", depth + 1))
    elif data.startswith(b"\x1f\x8b"):
        try:
            archive = tarfile.open(fileobj=io.BytesIO(data), mode="r:gz")
        except tarfile.ReadError:
            return findings
        with archive:
            for member in archive:
                if member.isfile():
                    stream = archive.extractfile(member)
                    if stream is None:
                        raise ValueError(f"cannot read archive member: {name}!{member.name}")
                    findings.extend(inspect(stream.read(), f"{name}!{member.name}", depth + 1))
    return findings


def main() -> None:
    paths = subprocess.check_output(
        ["git", "ls-files", "-z", "--cached", "--others", "--exclude-standard"], cwd=ROOT
    ).decode().split("\0")
    findings = []
    count = 0
    for name in sorted(set(paths) - {""}):
        path = ROOT / name
        if path.is_file():
            findings.extend(inspect(path.read_bytes(), name))
            count += 1
    if findings:
        raise SystemExit("Publication privacy check failed:\n" + "\n".join(findings))
    print(f"Publication privacy check passed for {count} files and their embedded archives.")


if __name__ == "__main__":
    main()
