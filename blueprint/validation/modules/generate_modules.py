#!/usr/bin/env python3
"""Generate and build the module-aware blueprint signature validator.

This validator is deliberately outside production trust.  It reuses the
integrated validator's Markdown extraction semantics, but distributes every
declaration across the exact production module DAG in ``module-map.json``.
Definitions and checked theorem bodies are copied; bodyless theorems become
exact-type validator-only axioms.
"""

from __future__ import annotations

import argparse
import hashlib
import importlib.util
import json
import os
import re
import subprocess
import sys
import tomllib
from collections import defaultdict
from dataclasses import dataclass
from pathlib import Path


def repository_root() -> Path:
    for candidate in Path(__file__).resolve().parents:
        if (candidate / "blueprint" / "README.md").is_file():
            return candidate
    raise RuntimeError("could not locate blueprint repository root")


ROOT = repository_root()
HERE = ROOT / "blueprint" / "validation" / "modules"
MAP_PATH = HERE / "module-map.json"
FUTURE_LAKEFILE = HERE / "future-lakefile.toml"
CANONICAL_GENERATOR = ROOT / "blueprint" / "validation" / "generate_integrated.py"
CANONICAL_LEDGER = ROOT / "blueprint" / "validation" / "declaration-coverage.tsv"
OUTPUT_LEDGER = HERE / "declaration-modules.tsv"
SOURCE_MANIFEST = HERE / "module-sources.tsv"
HASHES = HERE / "generated-hashes.sha256"
PACKAGE = HERE / "BlueprintModuleValidation"
PINNED_PACKAGE = Path("/home/codex/Documents/Codex/2026-08-14/Tiling")
PINNED_MATHLIB = PINNED_PACKAGE / ".lake" / "packages" / "mathlib"
PINNED_MATHLIB_REV = "db584cd6d46c92f209a44c0f1c829460d327499d"
PINNED_LEAN_VERSION = "4.33.0"


def load_integrated_generator():
    spec = importlib.util.spec_from_file_location(
        "blueprint_integrated_generator", CANONICAL_GENERATOR
    )
    if spec is None or spec.loader is None:
        raise RuntimeError(f"cannot load {CANONICAL_GENERATOR}")
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module


GEN = load_integrated_generator()


@dataclass(frozen=True)
class ModuleSpec:
    name: str
    imports: tuple[str, ...]

    @property
    def source(self) -> Path:
        return PACKAGE / (self.name.replace(".", "/") + ".lean")

    @property
    def production_source(self) -> str:
        return self.name.replace(".", "/") + ".lean"


@dataclass(frozen=True)
class Declaration:
    chapter: str
    line: int
    namespace: str
    kind: str
    identity: str
    visibility: str
    representation: str
    module: str
    chunk: tuple[str, ...]


def load_map() -> tuple[list[ModuleSpec], tuple[str, ...]]:
    raw = json.loads(MAP_PATH.read_text())
    if raw.get("schema") != 1 or raw.get("library") != "TranslationalTilings":
        raise RuntimeError("unsupported or wrong module-map schema")
    modules = [
        ModuleSpec(item["name"], tuple(item["imports"]))
        for item in raw["modules"]
    ]
    umbrella = tuple(raw["umbrella_imports"])
    names = [module.name for module in modules]
    if len(modules) != 29:
        raise RuntimeError(f"expected exactly 29 modules, found {len(modules)}")
    if len(names) != len(set(names)):
        raise RuntimeError("duplicate module name in module-map.json")
    return modules, umbrella


MODULES, UMBRELLA_IMPORTS = load_map()
MODULE_BY_NAME = {module.name: module for module in MODULES}


def validate_dag() -> list[str]:
    """Check resolution and cycles, returning the unique listed topological order."""
    position = {module.name: index for index, module in enumerate(MODULES)}
    for module in MODULES:
        for imported in module.imports:
            if imported not in MODULE_BY_NAME:
                raise RuntimeError(f"{module.name}: unresolved project import {imported}")
            if imported == module.name:
                raise RuntimeError(f"{module.name}: self import")
            if position[imported] >= position[module.name]:
                raise RuntimeError(
                    f"module-map order is not topological: {module.name} imports {imported}"
                )
    for imported in UMBRELLA_IMPORTS:
        if imported not in MODULE_BY_NAME:
            raise RuntimeError(f"umbrella has unresolved import {imported}")

    visiting: set[str] = set()
    visited: set[str] = set()

    def visit(name: str) -> None:
        if name in visiting:
            raise RuntimeError(f"project import cycle through {name}")
        if name in visited:
            return
        visiting.add(name)
        for imported in MODULE_BY_NAME[name].imports:
            visit(imported)
        visiting.remove(name)
        visited.add(name)

    for module in MODULES:
        visit(module.name)
    return [module.name for module in MODULES]


def validate_future_lakefile() -> None:
    future = tomllib.loads(FUTURE_LAKEFILE.read_text())
    if future.get("defaultTargets") != ["Tiling", "TranslationalTilings"]:
        raise RuntimeError("future lakefile has wrong defaultTargets")
    lean_libs = [item.get("name") for item in future.get("lean_lib", [])]
    if lean_libs != ["Tiling", "TranslationalTilings"]:
        raise RuntimeError(f"future lakefile has wrong lean_lib list: {lean_libs}")
    options = future.get("leanOptions", {})
    required_options = {
        "pp": {"unicode": {"fun": True}},
        "relaxedAutoImplicit": False,
        "weak": {"linter": {"mathlibStandardSet": True}},
        "maxSynthPendingDepth": 3,
    }
    if options != required_options:
        raise RuntimeError(f"future lakefile changed pinned options: {options}")


def module_for(chapter: str, line: int, identity: str) -> str:
    """Unique production home for a displayed declaration.

    Line cuts are the exact Markdown section boundaries recorded in
    ``MODULE_LAYOUT.md``.  The non-contiguous Chapter 05b exceptions are the
    terminal proof of ``PolynomialPrimeSumBound`` and the three unconditional
    wrappers that specialize the conditional Chen recursion with that proof,
    together with the two composite quadratic wrappers whose proofs consume
    both the local quadratic API and Chen's factorization certificate.
    """
    if chapter == "blueprint/01-foundations.md":
        return (
            "TranslationalTilings.Basic"
            if line < 244
            else "TranslationalTilings.FiniteDifference"
        )
    if chapter == "blueprint/02-lattice-geometry.md":
        return (
            "TranslationalTilings.Arithmetic"
            if line < 133
            else "TranslationalTilings.LatticeGeometry"
        )
    if chapter == "blueprint/03-dilation-structure.md":
        return (
            "TranslationalTilings.Dilation.Periodic"
            if line < 162
            else "TranslationalTilings.Structure.Grouped"
        )
    if chapter == "blueprint/04-counterexample.md":
        return "TranslationalTilings.Counterexample"
    if chapter == "blueprint/05a-weil-stepanov.md":
        cuts = [
            (521, "TranslationalTilings.NumberTheory.Stepanov.NewtonWaring"),
            (912, "TranslationalTilings.NumberTheory.Stepanov.ArtinLSeries"),
            (1094, "TranslationalTilings.NumberTheory.Stepanov.ArtinSchreier"),
            (1525, "TranslationalTilings.NumberTheory.Stepanov.HasseMultiplicity"),
            (1809, "TranslationalTilings.NumberTheory.Stepanov.TranslationProduct"),
            (1880, "TranslationalTilings.NumberTheory.Stepanov.AdditivePointCount"),
            (1979, "TranslationalTilings.NumberTheory.Stepanov.ReciprocalRoots"),
            (10**9, "TranslationalTilings.NumberTheory.PolynomialWeilBound"),
        ]
        return next(module for stop, module in cuts if line < stop)
    if chapter == "blueprint/05b-chen-complete-sums.md":
        terminal_specializations = {
            "TranslationalTilings.polynomialPrimeSumBound",
            "TranslationalTilings.chen_prime_base",
            "TranslationalTilings.primePower_completeSum_bound",
            "TranslationalTilings.ack_theorem_2_2_finiteProduct",
            "TranslationalTilings.quadratic_polynomialCompleteSum_parity_bound",
            "TranslationalTilings.quadratic_polynomialCompleteSum_bound",
        }
        if identity in terminal_specializations:
            return "TranslationalTilings.NumberTheory.CompleteExponentialSum"
        if line < 231:
            return "TranslationalTilings.NumberTheory.FiniteCyclicPhase"
        if line < 468:
            return "TranslationalTilings.NumberTheory.PolynomialCongruence"
        if line < 1185:
            return "TranslationalTilings.NumberTheory.ChenCompleteSum"
        if line < 1348:
            return "TranslationalTilings.NumberTheory.QuadraticCompleteSum"
        return "TranslationalTilings.NumberTheory.CompleteExponentialSum"
    if chapter == "blueprint/05-polynomial-rigidity.md":
        if line < 155 or 304 <= line < 447:
            return "TranslationalTilings.Analysis.CirclePolynomial"
        if line < 304:
            return "TranslationalTilings.Analysis.Equidistribution"
        if 514 <= line < 577:
            return "TranslationalTilings.Analysis.FejerSeparator"
        return "TranslationalTilings.Analysis.PolynomialRigidity"
    if chapter == "blueprint/06-weak-periodicity.md":
        return "TranslationalTilings.WeakPeriodicity"
    if chapter == "blueprint/07-periodic-completion.md":
        return (
            "TranslationalTilings.Slicing"
            if line < 144
            else "TranslationalTilings.PeriodicCompletion"
        )
    if chapter == "blueprint/08-algorithms.md":
        return "TranslationalTilings.Algorithms"
    if chapter == "blueprint/09-main-results.md":
        return "TranslationalTilings.Main"
    raise RuntimeError(f"no ownership rule for {chapter}:{line} ({identity})")


NAMESPACE_COMMAND = re.compile(r"^\s*(?:namespace\s+\S+|end(?:\s+\S+)?|open(?:\s+scoped)?\s+.+)\s*$")


def declaration_only(chunk: list[str]) -> list[str]:
    """Drop namespace/open commands trailing a declaration chunk.

    The canonical splitter keeps interstitial commands with the preceding
    declaration.  This validator wraps each declaration in its fully-qualified
    source namespace instead, so retaining those commands would double-close
    nested namespaces.
    """
    result: list[str] = []
    in_block_comment = False
    for line in chunk:
        stripped = line.strip()
        if in_block_comment:
            if "-/" in stripped:
                in_block_comment = False
            continue
        if stripped.startswith("/-"):
            if "-/" not in stripped[2:]:
                in_block_comment = True
            continue
        if NAMESPACE_COMMAND.match(line) or stripped.startswith("#"):
            continue
        result.append(line)
    while result and not result[-1].strip():
        result.pop()
    return result


def extract_declarations() -> tuple[list[Declaration], dict[str, set[str]]]:
    declarations: list[Declaration] = []
    mathlib_imports: dict[str, set[str]] = defaultdict(set)
    seen: set[tuple[str, int, str]] = set()

    for chapter in GEN.CHAPTERS:
        extracted = GEN.extract_lean(chapter)
        if extracted.fence_errors:
            raise RuntimeError("; ".join(extracted.fence_errors))
        chapter_name = str(chapter.path.relative_to(ROOT))
        previous_source_line = 0
        for is_decl, raw_chunk in GEN.split_items(extracted.lines):
            if not is_decl:
                continue
            line = GEN.source_line(chapter, raw_chunk, previous_source_line)
            previous_source_line = line
            namespace = GEN.namespace_at_source_line(chapter, line)
            named = GEN.declaration_name(raw_chunk, namespace)
            if named is not None:
                kind, qualified_name, local_name, is_private = named
                if is_private:
                    identity = f"<private:{local_name}@{chapter_name}:{line}>"
                    visibility = "private"
                else:
                    identity = qualified_name
                    visibility = "public"
            else:
                kind_match = GEN.DECL_KIND.match(raw_chunk[0])
                if kind_match is None:
                    raise RuntimeError(f"cannot classify {chapter_name}:{line}")
                kind = kind_match.group(1)
                identity = f"<{kind}@{chapter_name}:{line}>"
                visibility = "anonymous"

            has_colon, has_assign = GEN.top_level_tokens(raw_chunk)
            representation = "definition"
            if kind in {"theorem", "lemma"}:
                if has_assign and has_colon:
                    representation = "checked-body"
                elif has_assign:
                    representation = "invalid-untyped-alias"
                else:
                    representation = "exact-type-axiom-stub"
            elif visibility == "anonymous":
                # This is the canonical ledger convention for instances and
                # examples: they carry executable terms rather than API stubs.
                representation = "checked-body"
            if representation == "invalid-untyped-alias":
                raise RuntimeError(f"untyped theorem alias {identity}")

            module = module_for(chapter_name, line, identity)
            if module not in MODULE_BY_NAME:
                raise RuntimeError(f"ownership maps {identity} to unknown {module}")
            key = (chapter_name, line, identity)
            if key in seen:
                raise RuntimeError(f"duplicate declaration key {key}")
            seen.add(key)
            chunk = declaration_only(raw_chunk)
            gaps: list[str] = []
            rendered = GEN.theorem_to_stub(
                chunk,
                identity if named is not None else None,
                False,
                gaps,
            )
            if gaps:
                raise RuntimeError("; ".join(gaps))
            declarations.append(
                Declaration(
                    chapter_name,
                    line,
                    namespace,
                    kind,
                    identity,
                    visibility,
                    representation,
                    module,
                    tuple(rendered),
                )
            )
            mathlib_imports[module].update(extracted.imports)

    if not declarations:
        raise RuntimeError("no declarations extracted")
    if any(module.name not in mathlib_imports for module in MODULES):
        missing = [m.name for m in MODULES if m.name not in mathlib_imports]
        raise RuntimeError(f"modules with no owned declarations: {missing}")
    return declarations, mathlib_imports


def canonical_rows() -> list[tuple[str, ...]]:
    lines = CANONICAL_LEDGER.read_text().splitlines()
    if not lines:
        raise RuntimeError("canonical declaration ledger is empty")
    expected_header = (
        "chapter\tline\tnamespace\tkind\tqualified_name\tvisibility\t"
        "validator_representation"
    )
    if lines[0] != expected_header:
        raise RuntimeError("unexpected canonical ledger header")
    return [tuple(line.split("\t")) for line in lines[1:]]


def ownership_ledger(declarations: list[Declaration]) -> str:
    header = (
        "chapter\tline\tnamespace\tkind\tqualified_name\tvisibility\t"
        "validator_representation\tproduction_module\tproduction_source"
    )
    rows = [
        (
            declaration.chapter,
            str(declaration.line),
            declaration.namespace,
            declaration.kind,
            declaration.identity,
            declaration.visibility,
            declaration.representation,
        )
        for declaration in declarations
    ]
    expected = canonical_rows()
    if rows != expected:
        for index, (actual, canonical) in enumerate(
            zip(rows, expected, strict=False), start=2
        ):
            if actual != canonical:
                raise RuntimeError(
                    "module ledger disagrees with canonical ledger at row "
                    f"{index}: actual={actual}, canonical={canonical}"
                )
        raise RuntimeError(
            f"ledger length mismatch: module={len(rows)}, canonical={len(expected)}"
        )
    ownership = {declaration.identity: declaration.module for declaration in declarations}
    terminal = "TranslationalTilings.NumberTheory.CompleteExponentialSum"
    conditional = "TranslationalTilings.NumberTheory.ChenCompleteSum"
    expected_specializations = {
        "TranslationalTilings.polynomialPrimeSumBound": terminal,
        "TranslationalTilings.chen_prime_base": terminal,
        "TranslationalTilings.primePower_completeSum_bound": terminal,
        "TranslationalTilings.ack_theorem_2_2_finiteProduct": terminal,
        "TranslationalTilings.quadratic_polynomialCompleteSum_parity_bound": terminal,
        "TranslationalTilings.quadratic_polynomialCompleteSum_bound": terminal,
        "TranslationalTilings.chen_prime_base_of": conditional,
        "TranslationalTilings.primePower_completeSum_bound_of_primeBound": conditional,
        "TranslationalTilings.ack_theorem_2_2_finiteProduct_of_primeBound": conditional,
    }
    for identity, expected_module in expected_specializations.items():
        actual_module = ownership.get(identity)
        if actual_module != expected_module:
            raise RuntimeError(
                f"Chapter 05b terminal ownership regression for {identity}: "
                f"expected {expected_module}, found {actual_module}"
            )
    rendered = [header]
    for row, declaration in zip(rows, declarations, strict=True):
        rendered.append(
            "\t".join(
                [
                    *row,
                    declaration.module,
                    MODULE_BY_NAME[declaration.module].production_source,
                ]
            )
        )
    return "\n".join(rendered) + "\n"


def render_module(
    module: ModuleSpec,
    declarations: list[Declaration],
    mathlib_imports: set[str],
) -> str:
    chapter_hashes = sorted(
        {
            (
                declaration.chapter,
                hashlib.sha256((ROOT / declaration.chapter).read_bytes()).hexdigest(),
            )
            for declaration in declarations
        }
    )
    lines = [
        *[f"import {name}" for name in sorted(mathlib_imports)],
        *[f"import {name}" for name in module.imports],
        "",
        "/-!",
        "Validator-only module generated from the blueprint.",
        "It contains exact-type theorem axioms and is outside production trust.",
        "",
        *[f"source-sha256 {digest}  {chapter}" for chapter, digest in chapter_hashes],
        "-/",
        "",
    ]
    lines.extend(
        [
            "",
            "set_option relaxedAutoImplicit false",
            "set_option maxSynthPendingDepth 3",
            "",
            "open scoped BigOperators Real",
            "",
        ]
    )
    if "Mathlib.Data.Finset.SymmDiff" in mathlib_imports:
        lines.extend(["open scoped symmDiff", ""])
    if module.name == "TranslationalTilings.NumberTheory.PolynomialWeilBound":
        lines.extend(["open TranslationalTilings.Stepanov", ""])

    for declaration in declarations:
        lines.extend(
            [
                f"/- {declaration.chapter}:{declaration.line}; {declaration.identity} -/",
                f"namespace {declaration.namespace}",
                *declaration.chunk,
                f"end {declaration.namespace}",
                "",
            ]
        )
    return "\n".join(lines).rstrip() + "\n"


def render_umbrella() -> str:
    lines = [
        *[f"import {name}" for name in UMBRELLA_IMPORTS],
        "",
        "/-! Validator-only umbrella for the planned production library. -/",
        "",
        "set_option relaxedAutoImplicit false",
        "set_option maxSynthPendingDepth 3",
        "",
    ]
    return "\n".join(lines)


def render_lakefile() -> str:
    return f'''name = "BlueprintModuleValidation"
version = "0.0.0"
defaultTargets = ["TranslationalTilings"]

[leanOptions]
pp.unicode.fun = true
relaxedAutoImplicit = false
weak.linter.mathlibStandardSet = true
maxSynthPendingDepth = 3

[[require]]
name = "mathlib"
path = "{PINNED_MATHLIB}"

[[lean_lib]]
name = "TranslationalTilings"
'''


def render_offline_manifest() -> str:
    pinned = json.loads((PINNED_PACKAGE / "lake-manifest.json").read_text())
    packages = []
    for item in pinned["packages"]:
        name = item["name"]
        directory = PINNED_PACKAGE / ".lake" / "packages" / name
        if not directory.is_dir():
            raise RuntimeError(f"missing pinned dependency directory {directory}")
        packages.append(
            {
                "type": "path",
                "scope": "" if name == "mathlib" else item.get("scope", ""),
                "name": name,
                "manifestFile": item.get("manifestFile", "lake-manifest.json"),
                "inherited": name != "mathlib",
                "dir": str(directory),
                "configFile": item["configFile"],
            }
        )
    manifest = {
        "version": "1.2.0",
        "packagesDir": ".lake/packages",
        "packages": packages,
        "name": "BlueprintModuleValidation",
        "lakeDir": ".lake",
        "fixedToolchain": False,
    }
    return json.dumps(manifest, indent=1) + "\n"


def render_source_manifest(
    declarations: list[Declaration], module_text: dict[str, str]
) -> str:
    counts: dict[str, int] = defaultdict(int)
    for declaration in declarations:
        counts[declaration.module] += 1
    lines = ["module\tproduction_source\tdirect_project_imports\tdeclarations\tvalidator_sha256"]
    for module in MODULES:
        imports = ",".join(module.imports) if module.imports else "-"
        digest = hashlib.sha256(module_text[module.name].encode()).hexdigest()
        lines.append(
            "\t".join(
                [module.name, module.production_source, imports, str(counts[module.name]), digest]
            )
        )
    umbrella_text = render_umbrella()
    lines.append(
        "\t".join(
            [
                "TranslationalTilings",
                "TranslationalTilings.lean",
                ",".join(UMBRELLA_IMPORTS),
                "0",
                hashlib.sha256(umbrella_text.encode()).hexdigest(),
            ]
        )
    )
    return "\n".join(lines) + "\n"


def expected_outputs() -> dict[Path, str]:
    validate_dag()
    validate_future_lakefile()
    declarations, mathlib_imports = extract_declarations()
    grouped: dict[str, list[Declaration]] = defaultdict(list)
    for declaration in declarations:
        grouped[declaration.module].append(declaration)
    module_text = {
        module.name: render_module(
            module, grouped[module.name], mathlib_imports[module.name]
        )
        for module in MODULES
    }
    outputs: dict[Path, str] = {
        OUTPUT_LEDGER: ownership_ledger(declarations),
        PACKAGE / "TranslationalTilings.lean": render_umbrella(),
        PACKAGE / "lakefile.toml": render_lakefile(),
        PACKAGE / "lean-toolchain": "leanprover/lean4:v4.33.0\n",
        PACKAGE / "lake-manifest.json": render_offline_manifest(),
    }
    for module in MODULES:
        outputs[module.source] = module_text[module.name]
    outputs[SOURCE_MANIFEST] = render_source_manifest(declarations, module_text)
    return outputs


def render_hashes(outputs: dict[Path, str]) -> str:
    hash_inputs = {
        MAP_PATH: MAP_PATH.read_text(),
        FUTURE_LAKEFILE: FUTURE_LAKEFILE.read_text(),
        Path(__file__).resolve(): Path(__file__).read_text(),
        **outputs,
    }
    lines = []
    for path in sorted(hash_inputs, key=lambda value: str(value)):
        digest = hashlib.sha256(hash_inputs[path].encode()).hexdigest()
        lines.append(f"{digest}  {path.relative_to(ROOT)}")
    return "\n".join(lines) + "\n"


def write_outputs(outputs: dict[Path, str]) -> None:
    for path, content in outputs.items():
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(content)
    HASHES.write_text(render_hashes(outputs))


def check_outputs(outputs: dict[Path, str]) -> None:
    stale = []
    for path, content in outputs.items():
        if not path.is_file() or path.read_text() != content:
            stale.append(str(path.relative_to(ROOT)))
    expected_hashes = render_hashes(outputs)
    if not HASHES.is_file() or HASHES.read_text() != expected_hashes:
        stale.append(str(HASHES.relative_to(ROOT)))
    if stale:
        raise RuntimeError(
            "stale or missing module-validation artifacts:\n  " + "\n  ".join(stale)
        )


def verify_pinned_environment() -> None:
    mathlib_rev = subprocess.run(
        ["git", "-C", str(PINNED_MATHLIB), "rev-parse", "HEAD"],
        check=True,
        text=True,
        capture_output=True,
    ).stdout.strip()
    if mathlib_rev != PINNED_MATHLIB_REV:
        raise RuntimeError(
            f"wrong Mathlib revision: expected {PINNED_MATHLIB_REV}, found {mathlib_rev}"
        )
    lean_version = subprocess.run(
        ["lean", "--version"],
        cwd=PACKAGE,
        check=True,
        text=True,
        capture_output=True,
    ).stdout
    if f"version {PINNED_LEAN_VERSION}" not in lean_version:
        raise RuntimeError(f"wrong Lean executable: {lean_version.strip()}")


def build() -> None:
    verify_pinned_environment()
    environment = os.environ.copy()
    # If Lake unexpectedly tries to update a path-pinned dependency, rewrite
    # git transports to nonexistent local paths.  Cache downloads are disabled
    # separately by `--no-cache`.
    environment.update(
        {
            "GIT_CONFIG_COUNT": "2",
            "GIT_CONFIG_KEY_0": "url.file:///__blueprint_network_disabled_https__/.insteadOf",
            "GIT_CONFIG_VALUE_0": "https://",
            "GIT_CONFIG_KEY_1": "url.file:///__blueprint_network_disabled_http__/.insteadOf",
            "GIT_CONFIG_VALUE_1": "http://",
        }
    )
    subprocess.run(
        ["lake", "--no-cache", "build", "TranslationalTilings"],
        cwd=PACKAGE,
        env=environment,
        check=True,
    )


def main() -> None:
    parser = argparse.ArgumentParser()
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument("--write", action="store_true")
    mode.add_argument("--check", action="store_true")
    mode.add_argument("--build", action="store_true")
    args = parser.parse_args()

    outputs = expected_outputs()
    if args.write:
        write_outputs(outputs)
        print(
            f"wrote {len(MODULES)} modules, umbrella, and "
            f"{len(canonical_rows())} declaration ownership rows"
        )
        return
    check_outputs(outputs)
    print(
        f"module validation current: {len(MODULES)} modules; "
        f"{len(canonical_rows())} declarations; DAG acyclic"
    )
    if args.build:
        build()


if __name__ == "__main__":
    main()
