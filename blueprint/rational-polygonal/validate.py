#!/usr/bin/env python3
"""Generate and check the rational-polygonal paper API ledger.

The validator imports genuine production modules.  It never supplies declarations or proof
stubs: the committed signature dump is the fully elaborated output of `#check @name`, while the
live trust pass runs `#print axioms` for every public theorem/lemma in the ledger.
"""

from __future__ import annotations

import argparse
import csv
import hashlib
import re
import subprocess
import sys
import tempfile
from dataclasses import dataclass
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]
HERE = Path(__file__).resolve().parent

MODULES = [
    "Tiling.Geometry.Plane",
    "Tiling.Geometry.LocalLine",
    "Tiling.Geometry.PolygonalTopology",
    "Tiling.Geometry.Plate",
    "Tiling.Geometry.PackingTopology",
    "Tiling.Geometry.Sliding",
    "Tiling.Geometry.Connected",
    "Tiling.RationalPolygonal.Basic",
    "Tiling.RationalPolygonal.IntegerReduction",
    "Tiling.RationalPolygonal.Raster",
    "Tiling.RationalPolygonal.RasterMarker",
    "Tiling.RationalPolygonal.RigidFrame",
    "Tiling.RationalPolygonal.RasterRigidity",
    "Tiling.RationalPolygonal.Earthquake",
    "Tiling.RationalPolygonal.EarthquakeUniform",
    "Tiling.RationalPolygonal.ContinuousEarthquake",
    "Tiling.RationalPolygonal.SlidingReduction",
    "Tiling.RationalPolygonal.WeakPeriodicity",
    "Tiling.RationalPolygonal.Decision",
    "Tiling.RationalPolygonal.Main",
]

LEDGER = HERE / "declaration-coverage.tsv"
VALIDATOR = HERE / "BlueprintValidation.lean"
SIGNATURES = HERE / "api-signatures.txt"
DEFINITIONS = HERE / "definition-bodies.txt"
HASHES = HERE / "generated-hashes.sha256"

DECL_RE = re.compile(
    r"^(?:(?:noncomputable|protected)\s+)*(abbrev|def|theorem|lemma|structure|class|instance)\s+"
    r"([A-Za-z_][A-Za-z0-9_'.]*)"
)
FIELD_RE = re.compile(r"^  ([A-Za-z_][A-Za-z0-9_']*)\s*(?:\([^)]*\)|\{[^}]*\})*\s*:")


@dataclass(frozen=True)
class Decl:
    module: str
    source: str
    line: int
    kind: str
    name: str
    paper_item: str


def source_for(module: str) -> Path:
    return ROOT / (module.replace(".", "/") + ".lean")


def paper_item(name: str) -> str:
    exact = {
        "Tiling.RationalPolygonal.RationalPolygonalRegion.theorem_1_1": "Theorem 1.1",
        "Tiling.RationalPolygonal.RationalPolygonalRegion.corollary_1_1": "Corollary 1.1",
        "Tiling.RationalPolygonal.RationalPolygonalRegion.theorem_1_2": "Theorem 1.2",
        "Tiling.RationalPolygonal.PolygonalRegion.exists_integer_tiling": "Lemma 2.2",
        "Tiling.RationalPolygonal.PolygonalRegion.samePlate_translation_sub_mem_integerLattice": "Lemma 2.4",
        "Tiling.RationalPolygonal.exists_uniformQuakePeriodicDecomposition": "Lemma 4.2",
    }
    if name in exact:
        return exact[name]
    if "IsSlidingDirection" in name or "sliding" in name.lower():
        return "Lemmas 2.5-2.7 / compatibility"
    if name.startswith("Tiling.RationalPolygonal.RasterPresentation"):
        return "Corollary 1.1 support"
    if "Raster" in name or "signature" in name or "marker" in name.lower():
        return "Lemma 3.1 / raster support"
    if "quake" in name.lower() or "Earthquake" in name:
        return "Definition 4.1 / Lemma 4.2 support"
    if "WeakPeriodic" in name or "weaklyPeriodic" in name:
        return "Theorem 1.2 support"
    return "model / geometric support"


def parse_module(module: str) -> list[Decl]:
    path = source_for(module)
    lines = path.read_text().splitlines()
    namespace: list[str] = []
    blocks: list[tuple[str, str | None]] = []
    result: list[Decl] = []
    active_structure: tuple[str, int] | None = None

    for lineno, line in enumerate(lines, 1):
        if line.startswith("namespace "):
            name = line.split(None, 1)[1].strip()
            namespace.extend(name.split("."))
            blocks.append(("namespace", name))
            active_structure = None
            continue
        if line.startswith("section"):
            blocks.append(("section", None))
            active_structure = None
            continue
        if line.startswith("end"):
            if blocks:
                kind, name = blocks.pop()
                if kind == "namespace" and name is not None:
                    del namespace[-len(name.split(".")) :]
            active_structure = None
            continue

        if line.startswith("private "):
            active_structure = None
            continue

        match = DECL_RE.match(line)
        if match:
            kind, local = match.groups()
            full = ".".join([*namespace, local])
            result.append(Decl(module, str(path.relative_to(ROOT)), lineno, kind, full, paper_item(full)))
            active_structure = (full, len(line) - len(line.lstrip())) if kind in {"structure", "class"} else None
            continue

        if active_structure is not None:
            field = FIELD_RE.match(line)
            if field:
                full = f"{active_structure[0]}.{field.group(1)}"
                result.append(Decl(module, str(path.relative_to(ROOT)), lineno, "field", full, paper_item(full)))

    return result


def declarations() -> list[Decl]:
    out: list[Decl] = []
    for module in MODULES:
        out.extend(parse_module(module))
    seen: set[str] = set()
    duplicates = [decl.name for decl in out if decl.name in seen or seen.add(decl.name)]
    if duplicates:
        raise RuntimeError(f"duplicate parsed declarations: {duplicates}")
    return out


def render_ledger(decls: list[Decl]) -> str:
    rows = ["module\tsource\tline\tkind\tname\tpaper_item\tstatus"]
    rows.extend(
        "\t".join([d.module, d.source, str(d.line), d.kind, d.name, d.paper_item, "proved"])
        for d in decls
    )
    return "\n".join(rows) + "\n"


def render_validator(decls: list[Decl]) -> str:
    rows = [
        *(f"import {module}" for module in MODULES),
        "",
        "/-! Generated production-API validator for arXiv:2408.02151v2. -/",
        "",
        "set_option linter.style.header false",
        "set_option pp.universes true",
        "",
    ]
    for decl in decls:
        rows.append(f"#check @{decl.name}")
    return "\n".join(rows) + "\n"


def lean_output(source: str) -> str:
    proc = subprocess.run(
        ["lake", "env", "lean", "--stdin", "-DwarningAsError=true"],
        cwd=ROOT,
        input=source,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        check=False,
    )
    if proc.returncode != 0:
        raise RuntimeError(f"Lean failed ({proc.returncode}):\n{proc.stdout}")
    return proc.stdout


def signature_output(decls: list[Decl]) -> str:
    source = "\n".join([
        *(f"import {module}" for module in MODULES),
        "set_option pp.universes true",
        "set_option pp.explicit true",
        "set_option pp.all true",
        *(f"#check @{decl.name}" for decl in decls),
        "",
    ])
    return lean_output(source)


def definition_output(decls: list[Decl]) -> str:
    names = [
        decl.name for decl in decls
        if decl.kind in {"abbrev", "def", "structure", "class", "instance"}
    ]
    source = "\n".join([
        *(f"import {module}" for module in MODULES),
        "set_option pp.universes true",
        "set_option pp.explicit true",
        "set_option pp.all true",
        *(f"#print {name}" for name in names),
        "",
    ])
    return lean_output(source)


def lake_build() -> None:
    proc = subprocess.run(
        ["lake", "build", *MODULES],
        cwd=ROOT,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        text=True,
        check=False,
    )
    if proc.returncode != 0:
        raise RuntimeError(f"production Lake build failed:\n{proc.stdout}")


def strict_compile() -> None:
    for module in MODULES:
        proc = subprocess.run(
            ["lake", "env", "lean", "-DwarningAsError=true", str(source_for(module))],
            cwd=ROOT,
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
            text=True,
            check=False,
        )
        if proc.returncode != 0:
            raise RuntimeError(f"strict compile failed for {module}:\n{proc.stdout}")


def documentation_check() -> None:
    for module in MODULES:
        source = source_for(module).read_text() + "\n#lint only docBlame\n"
        try:
            lean_output(source)
        except RuntimeError as exc:
            raise RuntimeError(f"documentation check failed for {module}:\n{exc}") from exc


def trust_check(decls: list[Decl]) -> tuple[int, str]:
    theorem_names = [d.name for d in decls if d.kind in {"theorem", "lemma"}]
    source = "\n".join([
        *(f"import {module}" for module in MODULES),
        *(f"#print axioms {name}" for name in theorem_names),
        "",
    ])
    output = lean_output(source)
    forbidden = [
        line for line in output.splitlines()
        if "depends on axioms:" in line and not any(
            standard in line for standard in ("propext", "Classical.choice", "Quot.sound")
        )
    ]
    # Multi-line standard lists are accepted; reject any explicit project/unknown axiom token.
    tokens = re.findall(r"axioms:\s*\[([^\]]*)\]", output.replace("\n", " "))
    allowed = {"propext", "Classical.choice", "Quot.sound"}
    unexpected: set[str] = set()
    for token_group in tokens:
        unexpected.update(
            token.strip() for token in token_group.split(",")
            if token.strip() and token.strip() not in allowed
        )
    if forbidden and not tokens:
        raise RuntimeError("could not parse theorem axiom output")
    if unexpected:
        raise RuntimeError(f"unexpected axioms: {sorted(unexpected)}")
    return len(theorem_names), output


def render_hashes(payloads: dict[Path, str]) -> str:
    rows = []
    for path, text in sorted(payloads.items(), key=lambda item: str(item[0])):
        digest = hashlib.sha256(text.encode()).hexdigest()
        rows.append(f"{digest}  {path.relative_to(HERE)}")
    return "\n".join(rows) + "\n"


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--update", action="store_true", help="rewrite generated artifacts")
    parser.add_argument("--check", action="store_true", help="check committed artifacts and live Lean gates")
    args = parser.parse_args()
    if args.update == args.check:
        parser.error("choose exactly one of --update or --check")

    decls = declarations()
    ledger = render_ledger(decls)
    validator = render_validator(decls)
    signatures = signature_output(decls)
    definitions = definition_output(decls)
    payloads = {
        LEDGER: ledger,
        VALIDATOR: validator,
        SIGNATURES: signatures,
        DEFINITIONS: definitions,
    }
    hashes = render_hashes(payloads)

    if args.update:
        for path, text in payloads.items():
            path.write_text(text)
        HASHES.write_text(hashes)
        print(f"updated {len(decls)} declarations across {len(MODULES)} modules")
        return 0

    expected = {**payloads, HASHES: hashes}
    stale = [path for path, text in expected.items() if not path.exists() or path.read_text() != text]
    if stale:
        raise RuntimeError("stale generated artifacts: " + ", ".join(str(path) for path in stale))
    lake_build()
    strict_compile()
    documentation_check()
    # Compile the committed validator as its own source gate.
    proc = subprocess.run(
        ["lake", "env", "lean", "-DwarningAsError=true", str(VALIDATOR)],
        cwd=ROOT,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        text=True,
        check=False,
    )
    if proc.returncode != 0:
        raise RuntimeError(f"validator compile failed:\n{proc.stdout}")
    theorem_count, _ = trust_check(decls)
    print(
        f"PASS: {len(MODULES)} modules, {len(decls)} declarations, "
        f"{theorem_count} theorem trust closures, documentation clean"
    )
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except Exception as exc:  # fail with one concise diagnostic in CI
        print(f"ERROR: {exc}", file=sys.stderr)
        raise SystemExit(1)
