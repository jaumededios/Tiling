#!/usr/bin/env python3
"""Render this comparator's Challenge as README.md, or check it with --check."""

from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parent
sys.dont_write_bytecode = True
sys.path.insert(0, str(ROOT.parent))

from literate_readme import main


if __name__ == "__main__":
    raise SystemExit(main(ROOT, "AxisParallelComputabilityComparator"))
