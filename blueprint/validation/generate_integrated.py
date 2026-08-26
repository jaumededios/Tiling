#!/usr/bin/env python3
"""Generate the dependency-ordered Lean signature skeleton for the blueprint.

This is deliberately a validator generator, not project source.  It copies
definitions, structures, instances, and aliases from Markdown Lean fences.
Bodyless theorem declarations become `axiom` declarations with the exact
public name and type.  This is the only honest way to elaborate an interface
before its proofs exist; the generated module must never be imported by the
formalization.

Strict mode is the acceptance mode.  It rejects malformed Lean fences and any
duplicate public declaration across chapters.  `--allow-known-gaps` exists only
to generate a de-duplicated diagnostic skeleton and discover errors after the
first blocker.
"""

from __future__ import annotations

import argparse
import hashlib
import re
import sys
from dataclasses import dataclass
from pathlib import Path


def repository_root() -> Path:
    for candidate in Path(__file__).resolve().parents:
        if (candidate / "blueprint" / "README.md").is_file():
            return candidate
    raise RuntimeError("could not locate the blueprint repository root")


ROOT = repository_root()
VALIDATION = ROOT / "blueprint" / "validation"
OUTPUT = VALIDATION / "BlueprintIntegrated.lean"
LEDGER = VALIDATION / "declaration-coverage.tsv"
DIAGNOSTIC_OUTPUT = ROOT / "tmp" / "BlueprintIntegratedDiagnostic.lean"

# These are the pinned package options that affect whether displayed public
# signatures elaborate.  Keep them in the generated module so a direct
# `lake env lean path/to/BlueprintIntegrated.lean` command cannot silently use
# more permissive frontend defaults.
REQUIRED_PACKAGE_OPTION_LINES = (
    "set_option relaxedAutoImplicit false",
    "set_option maxSynthPendingDepth 3",
    "set_option maxErrors 1000",
)


@dataclass(frozen=True)
class Chapter:
    path: Path
    namespace: str


CHAPTERS = [
    Chapter(ROOT / "blueprint" / "01-foundations.md", "TranslationalTilings"),
    Chapter(ROOT / "blueprint" / "02-lattice-geometry.md", "TranslationalTilings"),
    Chapter(ROOT / "blueprint" / "03-dilation-structure.md", "TranslationalTilings"),
    Chapter(ROOT / "blueprint" / "04-counterexample.md", "TranslationalTilings.Counterexample"),
    Chapter(
        ROOT / "blueprint" / "05a-weil-stepanov.md",
        "TranslationalTilings",
    ),
    Chapter(
        ROOT / "blueprint" / "05b-chen-complete-sums.md",
        "TranslationalTilings",
    ),
    Chapter(ROOT / "blueprint" / "05-polynomial-rigidity.md", "TranslationalTilings"),
    Chapter(ROOT / "blueprint" / "06-weak-periodicity.md", "TranslationalTilings"),
    Chapter(ROOT / "blueprint" / "07-periodic-completion.md", "TranslationalTilings"),
    Chapter(ROOT / "blueprint" / "08-algorithms.md", "TranslationalTilings"),
    Chapter(ROOT / "blueprint" / "09-main-results.md", "TranslationalTilings"),
]


DECL_ATTRIBUTES = r"(?:@\[[^\]\n]+\]\s+)*"
DECL_MODIFIERS = r"(?:(?:private|noncomputable|protected)\s+)*"
DECL_START = re.compile(
    rf"^{DECL_ATTRIBUTES}{DECL_MODIFIERS}(?:abbrev|def|structure|class|inductive|instance|theorem|lemma|example)\b"
)
NAMED_DECL = re.compile(
    rf"^{DECL_ATTRIBUTES}({DECL_MODIFIERS})(abbrev|def|structure|class|inductive|theorem|lemma)\s+([^\s({{:]+)"
)
DECL_KIND = re.compile(
    rf"^{DECL_ATTRIBUTES}{DECL_MODIFIERS}(abbrev|def|structure|class|inductive|instance|theorem|lemma|example)\b"
)
THEOREM_START = re.compile(
    rf"^(\s*)({DECL_ATTRIBUTES})({DECL_MODIFIERS})(theorem|lemma)\b"
)


@dataclass
class ExtractedChapter:
    chapter: Chapter
    imports: list[str]
    lines: list[str]
    fence_errors: list[str]


def extract_lean(chapter: Chapter) -> ExtractedChapter:
    imports: list[str] = []
    code_lines: list[str] = []
    fence_errors: list[str] = []
    inside = False
    language = ""
    opened_at = 0
    current: list[str] = []

    for number, line in enumerate(chapter.path.read_text().splitlines(), start=1):
        if not inside and line.startswith("```"):
            inside = True
            language = line[3:].strip()
            opened_at = number
            current = []
            continue
        if inside and line.startswith("```"):
            if language == "lean":
                code_lines.extend(current)
                code_lines.append("")
            inside = False
            language = ""
            current = []
            continue
        if inside:
            current.append(line)

    if inside:
        fence_errors.append(
            f"{chapter.path.relative_to(ROOT)}:{opened_at}: unclosed `{language}` fence"
        )

    cleaned: list[str] = []
    for line in code_lines:
        stripped = line.strip()
        if stripped.startswith("import "):
            module = stripped.removeprefix("import ").strip()
            if module.startswith("Mathlib"):
                imports.append(module)
            continue
        # The chapter-to-namespace map is the public ownership manifest and
        # wraps declarations that are displayed in separate Markdown fences.
        # Strip only that outer namespace; preserve any genuine nested
        # namespace used to organize public declarations.
        if stripped in {
            f"namespace {chapter.namespace}",
            f"end {chapter.namespace}",
        }:
            continue
        cleaned.append(line)

    for number, line in enumerate(chapter.path.read_text().splitlines(), start=1):
        if re.search(r"(?<!\.)\.\.\.(?!\.)", line):
            # Prose uses mathematical `1,...,q`; only a Lean fence is a
            # declaration contract.  Determine fence membership below.
            inside_lean = False
            inside = False
            language = ""
            for probe_number, probe in enumerate(
                chapter.path.read_text().splitlines(), start=1
            ):
                if probe_number > number:
                    break
                if not inside and probe.startswith("```"):
                    inside = True
                    language = probe[3:].strip()
                    continue
                if inside and probe.startswith("```"):
                    inside = False
                    language = ""
                    continue
            inside_lean = inside and language == "lean"
            if inside_lean:
                fence_errors.append(
                    f"{chapter.path.relative_to(ROOT)}:{number}: Lean placeholder `...`"
                )

    forbidden = re.compile(
        rf"\b(sorry|admit)\b|^\s*{DECL_ATTRIBUTES}{DECL_MODIFIERS}(?:axiom|opaque)\b|:=\s*True\s*$"
    )
    # Retain source line numbers in diagnostics without placing forbidden
    # source constructs into the generated interface.
    inside = False
    language = ""
    for number, line in enumerate(chapter.path.read_text().splitlines(), start=1):
        if not inside and line.startswith("```"):
            inside = True
            language = line[3:].strip()
            continue
        if inside and line.startswith("```"):
            inside = False
            language = ""
            continue
        code_before_comment = line.split("--", 1)[0]
        if (
            inside
            and language == "lean"
            and forbidden.search(code_before_comment)
        ):
            fence_errors.append(
                f"{chapter.path.relative_to(ROOT)}:{number}: forbidden placeholder or vacuous declaration `{line.strip()}`"
            )

    return ExtractedChapter(chapter, imports, cleaned, fence_errors)


def split_items(lines: list[str]) -> list[tuple[bool, list[str]]]:
    """Split raw text into top-level declaration chunks and interstitial text."""
    starts = [i for i, line in enumerate(lines) if DECL_START.match(line)]
    if not starts:
        return [(False, lines)] if lines else []

    items: list[tuple[bool, list[str]]] = []
    cursor = 0
    for index, start in enumerate(starts):
        if cursor < start:
            items.append((False, lines[cursor:start]))
        stop = starts[index + 1] if index + 1 < len(starts) else len(lines)
        items.append((True, lines[start:stop]))
        cursor = stop
    return items


def declaration_name(
    chunk: list[str], namespace: str
) -> tuple[str, str, str, bool] | None:
    match = NAMED_DECL.match(chunk[0])
    if not match:
        return None
    modifiers, kind, name = match.groups()
    is_private = "private" in modifiers.split()
    if name.startswith("_root_."):
        return kind, name.removeprefix("_root_."), name, is_private
    return kind, f"{namespace}.{name}", name, is_private


def normalize(chunk: list[str]) -> str:
    return "".join("".join(chunk).split())


def source_line(chapter: Chapter, chunk: list[str], after: int) -> int:
    """Locate the first line of a copied declaration in its Markdown source."""
    needle = chunk[0].strip()
    for number, line in enumerate(chapter.path.read_text().splitlines(), start=1):
        if number > after and line.strip() == needle:
            return number
    return 0


def namespace_at_source_line(chapter: Chapter, declaration_line: int) -> str:
    """Return the actual namespace enclosing a displayed declaration.

    The chapter ownership namespace is supplied by ``CHAPTERS`` and is
    deliberately re-opened around every extracted chapter.  Markdown may also
    contain genuine nested namespaces, however.  Track those source commands
    independently of the stripped outer wrapper so the coverage ledger and
    duplicate check use the same fully-qualified names that Lean creates.

    A ``section`` does not affect names.  There currently are no nested
    sections in the blueprint, but keeping a command-kind stack makes a named
    ``end`` robust if one is introduced later.
    """
    command_stack: list[tuple[str, str]] = []
    inside = False
    language = ""
    source = chapter.path.read_text().splitlines()
    for number, line in enumerate(source, start=1):
        if number >= declaration_line:
            break
        if not inside and line.startswith("```"):
            inside = True
            language = line[3:].strip()
            continue
        if inside and line.startswith("```"):
            inside = False
            language = ""
            continue
        if not inside or language != "lean":
            continue

        stripped = line.strip()
        if stripped in {
            f"namespace {chapter.namespace}",
            f"end {chapter.namespace}",
        }:
            continue
        namespace_match = re.fullmatch(r"namespace\s+([^\s]+)", stripped)
        if namespace_match is not None:
            command_stack.append(("namespace", namespace_match.group(1)))
            continue
        section_match = re.fullmatch(r"section(?:\s+([^\s]+))?", stripped)
        if section_match is not None:
            command_stack.append(("section", section_match.group(1) or ""))
            continue
        if re.fullmatch(r"end(?:\s+[^\s]+)?", stripped) is not None:
            if command_stack:
                command_stack.pop()

    nested = [name for kind, name in command_stack if kind == "namespace"]
    return ".".join([chapter.namespace, *nested])


def top_level_tokens(chunk: list[str]) -> tuple[bool, bool]:
    """Return whether a declaration has a result colon and a declaration body.

    A `let x := t` inside a theorem's result proposition is not the theorem
    body.  In this blueprint, actual theorem bodies place `:=` on a non-`let`
    line; the distinction matters for exact cost statements whose result is a
    let-expression.
    """
    depth = 0
    has_colon = False
    has_assign = False
    for line in chunk:
        index = 0
        while index < len(line):
            char = line[index]
            if char in "([{":
                depth += 1
            elif char in ")]}":
                depth = max(0, depth - 1)
            elif char == ":" and depth == 0:
                if index + 1 < len(line) and line[index + 1] == "=":
                    prefix = line[:index].strip()
                    if not prefix.startswith(("let ", "letI ", "have ")):
                        has_assign = True
                    index += 1
                else:
                    has_colon = True
            index += 1
    return has_colon, has_assign


def theorem_to_stub(
    chunk: list[str], qualified_name: str | None, allow_known_gaps: bool, gaps: list[str]
) -> list[str]:
    if not THEOREM_START.match(chunk[0]):
        return chunk
    has_colon, has_assign = top_level_tokens(chunk)
    if has_assign:
        if not has_colon:
            name = qualified_name or chunk[0].strip()
            gaps.append(
                f"theorem alias `{name}` omits the mandatory explicit result type"
            )
            if allow_known_gaps:
                # Lean theorem declarations require an explicit result type;
                # even replacing `theorem` by `def` need not infer all target
                # implicits.  Omit the bad alias only in diagnostic mode.  The
                # strict artifact reproduces it verbatim and therefore fails.
                return [f"-- INTEGRATION GAP: ill-typed theorem alias `{name}` omitted."]
        # A theorem with an explicit type and body is a real declaration in the
        # blueprint.  Keeping it validates the proof-term wiring to lower stubs.
        return chunk
    first = THEOREM_START.sub(
        lambda m: f"{m.group(1)}{m.group(2)}{m.group(3)}axiom",
        chunk[0],
        count=1,
    )
    return [first, *chunk[1:]]


def render(allow_known_gaps: bool) -> tuple[str, str, list[str]]:
    extracted = [extract_lean(chapter) for chapter in CHAPTERS]
    imports = sorted({module for item in extracted for module in item.imports})
    gaps = [gap for item in extracted for gap in item.fence_errors]
    seen: dict[str, tuple[str, str, int]] = {}
    duplicate_keys: set[str] = set()
    rendered_chapters: list[str] = []
    coverage: list[tuple[str, str, str, str, str, str, str]] = []
    private_declarations: set[tuple[str, str]] = set()

    for item in extracted:
        relative = item.chapter.path.relative_to(ROOT)
        previous_source_line = 0
        body: list[str] = [
            f"/-! ## Generated from `{relative}` -/",
            "",
            f"namespace {item.chapter.namespace}",
            "",
        ]
        for is_decl, chunk in split_items(item.lines):
            if not is_decl:
                body.extend(chunk)
                continue

            declaration_line = source_line(item.chapter, chunk, previous_source_line)
            previous_source_line = declaration_line
            actual_namespace = namespace_at_source_line(
                item.chapter, declaration_line
            )
            named = declaration_name(chunk, actual_namespace)
            if named is not None:
                kind, qualified_name, local_name, is_private = named
                if is_private:
                    visibility = "private"
                    ledger_identity = (
                        f"<private:{local_name}@{relative}:{declaration_line}>"
                    )
                    duplicate_key = (
                        f"private:{relative}:{actual_namespace}:{local_name}"
                    )
                    private_declarations.add((str(relative), local_name))
                else:
                    visibility = "public"
                    ledger_identity = qualified_name
                    duplicate_key = qualified_name
                # The generator checks theorem names too, not merely data
                # definitions.  This catches accidental paper/API aliases that
                # collide with a lower declaration.  Private names are scoped
                # to their intended source module rather than treated as a
                # stable exported fully-qualified name.
                if duplicate_key in seen:
                    previous_normalized, previous_file, previous_line = seen[
                        duplicate_key
                    ]
                    duplicate_keys.add(duplicate_key)
                    same = normalize(chunk) == previous_normalized
                    gaps.append(
                        f"{relative}: duplicate `{ledger_identity}`; first declared in "
                        f"{previous_file}:{previous_line}; token-identical={same}"
                    )
                    if allow_known_gaps:
                        body.append(
                            f"-- INTEGRATION GAP: duplicate `{ledger_identity}` omitted from diagnostic build."
                        )
                        continue
                else:
                    first_line = declaration_line
                    # Store the normalized declaration in the first tuple slot
                    # so a later duplicate can be compared without reparsing.
                    seen[duplicate_key] = (
                        normalize(chunk),
                        str(relative),
                        first_line,
                    )

                has_colon, has_assign = top_level_tokens(chunk)
                representation = "definition"
                if kind in {"theorem", "lemma"}:
                    if has_assign and has_colon:
                        representation = "checked-body"
                    elif has_assign:
                        representation = "invalid-untyped-alias"
                    else:
                        representation = "exact-type-axiom-stub"
                coverage.append(
                    (
                        str(relative),
                        str(declaration_line),
                        actual_namespace,
                        kind,
                        ledger_identity,
                        visibility,
                        representation,
                    )
                )
            else:
                kind_match = DECL_KIND.match(chunk[0])
                if kind_match is not None:
                    kind = kind_match.group(1)
                    coverage.append(
                        (
                            str(relative),
                            str(declaration_line),
                            actual_namespace,
                            kind,
                            f"<{kind}@{relative}:{declaration_line}>",
                            "anonymous",
                            "checked-body",
                        )
                    )

            body.extend(
                theorem_to_stub(
                    chunk,
                    ledger_identity if named is not None else None,
                    allow_known_gaps,
                    gaps,
                )
            )

        body.extend(["", f"end {item.chapter.namespace}", ""])
        rendered_chapters.append("\n".join(body))

    exported_names = {row[4] for row in coverage if row[5] == "public"}
    namespace_regressions = {
        "eraseConstant": "TranslationalTilings.Stepanov.eraseConstant",
        "toPolynomial": (
            "TranslationalTilings.Stepanov.MonicDegreePolynomial.toPolynomial"
        ),
        "waringPowerSum": "TranslationalTilings.Stepanov.waringPowerSum",
        "polynomial_addChar_sum_prime": (
            "TranslationalTilings.polynomial_addChar_sum_prime"
        ),
    }
    for local_name, expected in namespace_regressions.items():
        actual = sorted(
            row[4]
            for row in coverage
            if row[0] == "blueprint/05a-weil-stepanov.md"
            and row[5] == "public"
            and row[4].rsplit(".", 1)[-1] == local_name
        )
        if actual != [expected]:
            gaps.append(
                f"namespace regression for `{local_name}`: "
                f"expected [`{expected}`], found {actual}"
            )

    private_waring = (
        "blueprint/05a-weil-stepanov.md",
        "waringVariable",
    )
    if private_waring not in private_declarations:
        gaps.append(
            "private-declaration regression: `waringVariable` is not literally private"
        )
    if any(name.rsplit(".", 1)[-1] == "waringVariable" for name in exported_names):
        gaps.append(
            "private-declaration regression: `waringVariable` leaked into the exported public-name set"
        )

    attributed_declaration_regressions = {
        "TranslationalTilings.factorizationScalarLookup_of_mem",
        "TranslationalTilings.factorizationScalarLookup_of_not_mem",
    }
    missing_attributed = attributed_declaration_regressions - exported_names
    if missing_attributed:
        gaps.append(
            "attribute-prefixed declaration regression: missing "
            + ", ".join(f"`{name}`" for name in sorted(missing_attributed))
        )

    diagnostic_instances = ""
    if allow_known_gaps:
        diagnostic_instances = """
-- Diagnostic-only ambient classical instances.  Strict generation omits
-- these, so signatures that forgot to localize decidability still fail the
-- acceptance build.
local instance (p : Prop) : Decidable p := Classical.propDecidable p
local instance (α : Type u) : DecidableEq α := Classical.decEq α
"""
    diagnostic_instances = diagnostic_instances.replace(
        "local instance", "noncomputable local instance"
    )
    option_prelude = "\n".join(REQUIRED_PACKAGE_OPTION_LINES)
    prelude = (
        "\n\n"
        + option_prelude
        + "\n\nopen scoped symmDiff\n"
        + diagnostic_instances
        + "\n"
    )
    for required_line in REQUIRED_PACKAGE_OPTION_LINES:
        if prelude.splitlines().count(required_line) != 1:
            gaps.append(
                f"package-option regression: expected exactly one `{required_line}`"
            )

    digest_lines = [
        f"{hashlib.sha256(chapter.path.read_bytes()).hexdigest()}  "
        f"{chapter.path.relative_to(ROOT)}"
        for chapter in CHAPTERS
    ]
    gap_lines = [f"- {gap}" for gap in gaps] or ["- none"]
    validation_mode = "permissive diagnostic" if allow_known_gaps else "strict acceptance"
    header = f"""/-!
# Integrated blueprint signature validator

Generated by `blueprint/validation/generate_integrated.py` in dependency order.
Generation mode: **{validation_mode}**.

This module is **not project source and must never be imported**.  Definitions,
structures, instances, and theorem aliases are copied from the Markdown.  A
bodyless public theorem is represented by an `axiom` with its exact public name
and type solely so downstream signatures can elaborate.  This validates names,
types, typeclasses, namespaces, and dependencies; it proves no mathematics.

Source hashes:
{chr(10).join(digest_lines)}

Generator integration gaps:
{chr(10).join(gap_lines)}
-/

"""
    import_text = "\n".join(f"import {module}" for module in imports)
    # Lean requires every import before any command, including a module doc
    # comment.  Keep the generated provenance immediately after the imports.
    ledger_header = (
        "chapter\tline\tnamespace\tkind\tqualified_name\tvisibility\tvalidator_representation\n"
    )
    ledger = ledger_header + "".join("\t".join(row) + "\n" for row in coverage)
    return (
        import_text + "\n\n" + header + prelude + "\n".join(rendered_chapters),
        ledger,
        gaps,
    )


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--write", action="store_true", help="write the generated Lean file")
    parser.add_argument("--check", action="store_true", help="check that the generated file is current")
    parser.add_argument(
        "--allow-known-gaps",
        action="store_true",
        help="omit later duplicates to permit diagnostic Lean compilation",
    )
    args = parser.parse_args()
    if args.write == args.check:
        parser.error("choose exactly one of --write or --check")

    generated, ledger, gaps = render(args.allow_known_gaps)
    output = DIAGNOSTIC_OUTPUT if args.allow_known_gaps else OUTPUT
    if args.write:
        VALIDATION.mkdir(parents=True, exist_ok=True)
        output.write_text(generated)
        if not args.allow_known_gaps:
            LEDGER.write_text(ledger)
    else:
        stale = False
        expected_artifacts = [(output, generated)]
        if not args.allow_known_gaps:
            expected_artifacts.append((LEDGER, ledger))
        for path, expected in expected_artifacts:
            if not path.exists() or path.read_text() != expected:
                print(f"stale generated artifact: {path.relative_to(ROOT)}", file=sys.stderr)
                stale = True
        if stale:
            return 1

    for gap in gaps:
        print(f"integration gap: {gap}", file=sys.stderr)
    if gaps and not args.allow_known_gaps:
        return 2
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
