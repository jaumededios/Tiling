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
    "Tiling.RationalPolygonal.DiscreteCarrier",
    "Tiling.RationalPolygonal.IntegerReduction",
    "Tiling.RationalPolygonal.Raster",
    "Tiling.RationalPolygonal.RasterMarker",
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

ATTRIBUTE = r"(?:@\[[^]]*\]\s*)*"
MODIFIER = r"(?:(?:private|protected|noncomputable|unsafe|partial|local)\s+)*"
DECL_RE = re.compile(
    rf"^{ATTRIBUTE}(?P<modifiers>{MODIFIER})"
    r"(?P<kind>abbrev|def|theorem|lemma|structure|class|instance|inductive|axiom|opaque)\s+"
    r"(?P<name>[A-Za-z_][A-Za-z0-9_'.]*)"
)
FIELD_RE = re.compile(
    rf"^  {ATTRIBUTE}(?P<name>[A-Za-z_][A-Za-z0-9_']*)"
    r"\s*(?:\([^)]*\)|\{[^}]*\})*\s*:"
)

# Lean generates these public-looking helpers for structures/inductives.  They share source ranges
# with user commands but are not source-level public commands or explicit structure fields.
GENERATED_SUFFIXES = (
    ".casesOn",
    ".recOn",
    ".noConfusion",
    ".mk.noConfusion",
)


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
        "Tiling.RationalPolygonal.RationalPolygonalRegion.corollary_1_1_spec": "Corollary 1.1 support",
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


def parse_lines(module: str, source: str, path_label: str) -> list[Decl]:
    lines = source.splitlines()
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

        match = DECL_RE.match(line)
        if match:
            modifiers = match.group("modifiers").split()
            if "private" in modifiers or "local" in modifiers:
                active_structure = None
                continue
            kind = match.group("kind")
            local = match.group("name")
            full = ".".join([*namespace, local])
            result.append(Decl(module, path_label, lineno, kind, full, paper_item(full)))
            active_structure = (full, len(line) - len(line.lstrip())) if kind in {"structure", "class"} else None
            continue

        if active_structure is not None:
            field = FIELD_RE.match(line)
            if field:
                full = f"{active_structure[0]}.{field.group('name')}"
                result.append(Decl(module, path_label, lineno, "field", full, paper_item(full)))

    return result


def parse_module(module: str) -> list[Decl]:
    path = source_for(module)
    return parse_lines(module, path.read_text(), str(path.relative_to(ROOT)))


def parser_regression() -> None:
    """Keep same-line attributes/modifiers from silently falling out of the source ledger."""
    source = """namespace LedgerRegression
@[simp] theorem attributed_theorem : True := by trivial
@[simp] protected theorem protected_theorem : True := by trivial
noncomputable def public_definition : Nat := 0
@[simp] private theorem private_theorem : True := by trivial
local instance local_instance : Inhabited Nat := inferInstance
structure Packet where
  @[simp] payload : Nat
end LedgerRegression
"""
    parsed = parse_lines("LedgerRegression", source, "<parser-regression>")
    actual = [(decl.kind, decl.name, decl.line) for decl in parsed]
    expected = [
        ("theorem", "LedgerRegression.attributed_theorem", 2),
        ("theorem", "LedgerRegression.protected_theorem", 3),
        ("def", "LedgerRegression.public_definition", 4),
        ("structure", "LedgerRegression.Packet", 7),
        ("field", "LedgerRegression.Packet.payload", 8),
    ]
    if actual != expected:
        raise RuntimeError(f"declaration-parser regression: expected {expected}, got {actual}")


def compiled_public_declarations() -> dict[str, tuple[str, int]]:
    """Enumerate public, source-ranged constants owned by each compiled production module.

    This is deliberately independent of the source parser.  Module ownership comes from Lean's
    environment, and source positions come from the compiled declaration-range extension.
    """
    module_rows = ",\n    ".join(f"(`{module}, \"{module}\")" for module in MODULES)
    source = f"""import Lean
{chr(10).join(f'import {module}' for module in MODULES)}

open Lean Elab Command

private def ledgerConstantKind? : ConstantInfo → Option String
  | .axiomInfo _ => some \"axiom\"
  | .defnInfo _ => some \"definition\"
  | .thmInfo _ => some \"theorem\"
  | .opaqueInfo _ => some \"opaque\"
  | .inductInfo _ => some \"inductive\"
  | .quotInfo _ | .ctorInfo _ | .recInfo _ => none

run_cmd do
  let env ← getEnv
  let modules : Array (Name × String) := #[
    {module_rows}
  ]
  for (moduleName, moduleText) in modules do
    let some moduleIdx := env.getModuleIdx? moduleName
      | throwError m!\"compiled module is missing: {{moduleName}}\"
    for (declName, info) in env.constants.toList do
      if env.getModuleIdxFor? declName == some moduleIdx && !isPrivateName declName then
        if let some kind := ledgerConstantKind? info then
          if let some ranges ← findDeclarationRanges? declName then
            logInfo m!\"LEDGER_OWNED\\t{{moduleText}}\\t{{ranges.selectionRange.pos.line}}\\t{{kind}}\\t{{declName}}\"
"""
    output = lean_output(source)
    compiled: dict[str, tuple[str, int]] = {}
    prefix = "LEDGER_OWNED\t"
    for line in output.splitlines():
        if not line.startswith(prefix):
            continue
        module, lineno, _kind, name = line[len(prefix) :].split("\t", 3)
        if name.endswith(GENERATED_SUFFIXES):
            continue
        if name in compiled:
            raise RuntimeError(f"duplicate compiled public declaration: {name}")
        compiled[name] = (module, int(lineno))
    if not compiled:
        raise RuntimeError("compiled declaration cross-check produced no declarations")
    return compiled


def cross_check_compiled(decls: list[Decl]) -> None:
    compiled = compiled_public_declarations()
    parsed = {decl.name: (decl.module, decl.line) for decl in decls}
    extras = sorted(set(parsed) - set(compiled))
    moved = sorted(
        name for name in parsed if name in compiled and parsed[name] != compiled[name]
    )

    # Several declarations can legitimately share one source command line (structure-generated
    # recursors and inherited projections).  Conversely, `deriving` generates declarations on a
    # line which is not itself a public command or explicit field.  Comparing all other owned
    # source-range lines makes omissions detectable without mistaking those generated constants
    # for source commands.
    parsed_lines = set(parsed.values())
    source_lines = {
        module: source_for(module).read_text().splitlines() for module in MODULES
    }
    compiled_lines = {
        (module, line)
        for module, line in compiled.values()
        if not source_lines[module][line - 1].lstrip().startswith("deriving")
    }
    omitted_lines = sorted(compiled_lines - parsed_lines)
    if omitted_lines or extras or moved:
        details = []
        if omitted_lines:
            details.append(f"source parser omitted compiled declaration lines: {omitted_lines}")
        if extras:
            details.append(f"source ledger extras: {extras}")
        if moved:
            details.append(
                "source/compiled ownership or line mismatches: "
                + repr([(name, parsed[name], compiled[name]) for name in moved])
            )
        raise RuntimeError("; ".join(details))


def declarations() -> list[Decl]:
    parser_regression()
    out: list[Decl] = []
    for module in MODULES:
        out.extend(parse_module(module))
    seen: set[str] = set()
    duplicates = [decl.name for decl in out if decl.name in seen or seen.add(decl.name)]
    if duplicates:
        raise RuntimeError(f"duplicate parsed declarations: {duplicates}")
    cross_check_compiled(out)
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
        [
            "lake", "env", "lean", "--stdin",
            "-DwarningAsError=true", "-Dlinter.unusedDecidableInType=true",
        ],
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
            [
                "lake", "env", "lean", "-DwarningAsError=true",
                "-Dlinter.unusedDecidableInType=true", str(source_for(module)),
            ],
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

    # Refresh the production oleans before asking Lean for elaborated types or bodies.  This is
    # required after an upstream source change because later imports otherwise see a stale API.
    lake_build()
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
    strict_compile()
    documentation_check()
    # Compile the committed validator as its own source gate.
    proc = subprocess.run(
        [
            "lake", "env", "lean", "-DwarningAsError=true",
            "-Dlinter.unusedDecidableInType=true", str(VALIDATOR),
        ],
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
