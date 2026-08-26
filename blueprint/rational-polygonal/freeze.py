#!/usr/bin/env python3
"""Create or verify the sealed rational-polygonal production snapshot."""

from __future__ import annotations

import argparse
import hashlib
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]
HERE = Path(__file__).resolve().parent
MANIFEST = HERE / "SNAPSHOT.sha256"


def payloads() -> list[Path]:
    files: set[Path] = {
        ROOT / "Tiling.lean",
        ROOT / "TranslationalTilings.lean",
        ROOT / "lakefile.toml",
        ROOT / "lake-manifest.json",
        ROOT / "lean-toolchain",
    }
    files.update((ROOT / "Tiling").rglob("*.lean"))
    files.update((ROOT / "TranslationalTilings").rglob("*.lean"))
    for path in HERE.iterdir():
        if path.is_file() and path != MANIFEST:
            files.add(path)
    return sorted(files, key=lambda path: str(path.relative_to(ROOT)))


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def render() -> str:
    return "".join(
        f"{digest(path)}  {path.relative_to(ROOT)}\n"
        for path in payloads()
    )


def main() -> int:
    parser = argparse.ArgumentParser()
    group = parser.add_mutually_exclusive_group(required=True)
    group.add_argument("--update", action="store_true")
    group.add_argument("--check", action="store_true")
    args = parser.parse_args()

    expected = render()
    if args.update:
        MANIFEST.write_text(expected)
    elif not MANIFEST.exists() or MANIFEST.read_text() != expected:
        raise SystemExit("sealed snapshot mismatch")

    manifest_digest = hashlib.sha256(expected.encode()).hexdigest()
    print(f"PASS: {len(payloads())} payloads, manifest SHA-256 {manifest_digest}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
