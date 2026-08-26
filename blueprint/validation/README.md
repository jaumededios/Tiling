# Blueprint signature validation

The acceptance gate uses two complementary validators:

1. `BlueprintIntegrated.lean` checks every declaration together in one exact,
   dependency-ordered environment.
2. `modules/` assigns every declaration to its frozen production file and
   builds the resulting 29-module `TranslationalTilings` target plus umbrella
   under the package's strict options.

Both are signature and boundary evidence only.  Neither supplies proofs for
bodyless blueprint theorems.

## Integrated validator

`BlueprintIntegrated.lean` is the single dependency-ordered interface check
for the blueprint.  `generate_integrated.py` extracts every `lean` fence from
the blueprint chapters, preserves the bodies of definitions, structures,
instances, examples, and proved aliases, and replaces each bodyless theorem
by a validator-only `axiom` having the same name and exact type.  The generated
module therefore checks elaboration and cross-chapter use; it proves no
mathematics and must never be imported by production code.

`declaration-coverage.tsv` is generated from the same parse.  It records the
source chapter and line, namespace, declaration kind, qualified public name,
visibility, and whether the validator copied a body or supplied an exact-type
theorem stub.  Private declarations are copied so dependent declarations
elaborate, but receive a source-local `<private:...@chapter:line>` identity
rather than a fictitious stable exported name.  Anonymous instances and
examples likewise receive source-location identifiers.

## Strict acceptance check

From the blueprint repository root, first check that both generated artifacts
are current and that the generator found no duplicate declaration, malformed
fence, untyped theorem alias, private-name leak, or namespace regression:

```bash
python3 blueprint/validation/generate_integrated.py --check
```

Then elaborate the strict artifact with the pinned Lean 4.33.0/Mathlib 4.33.0
environment.  The generated file itself sets the package's
`relaxedAutoImplicit=false`, `maxSynthPendingDepth=3`, and `maxErrors=1000`
options, so the direct command is an actual package-policy check:

```bash
cd /home/codex/Documents/Codex/2026-08-14/Tiling
lake env lean \
  /home/codex/Documents/Codex/2026-08-24/usi/blueprint/validation/BlueprintIntegrated.lean
```

As a regression against command/file option drift, also pass the same options
explicitly on the command line:

```bash
lake env lean -DrelaxedAutoImplicit=false -DmaxSynthPendingDepth=3 \
  -DmaxErrors=1000 \
  /home/codex/Documents/Codex/2026-08-24/usi/blueprint/validation/BlueprintIntegrated.lean
```

Strict generation adds no ambient `Classical.propDecidable` or
`Classical.decEq` instance.  Missing explicit instances, missing
`noncomputable`, import gaps, undefined names, and dependent-type mismatches
must therefore fail elaboration.

## Diagnostic mode

While repairing a rejected snapshot, the following command writes only
`tmp/BlueprintIntegratedDiagnostic.lean`:

```bash
python3 blueprint/validation/generate_integrated.py \
  --write --allow-known-gaps
```

Diagnostic mode omits duplicate or syntactically invalid untyped aliases and
adds local classical instances so later independent errors remain visible.
It is never an acceptance check and does not update the checked coverage
ledger.  The strict artifact under this directory is the only generated Lean
file included in a reviewed snapshot.

The exact-type `axiom` stubs in this validator are deliberately outside the
formalization's trust boundary.  The project trust audit scans production
`TranslationalTilings/` sources for axioms and separately verifies that no
production source imports `BlueprintIntegrated`.

## Module-boundary validator

The production split and direct-import DAG are frozen in
`../MODULE_LAYOUT.md`.  From the blueprint repository root, verify that the
module artifacts, ownership ledger, and hashes are current, then perform the
offline pinned Lake build:

```bash
python3 blueprint/validation/modules/generate_modules.py --check
sha256sum -c blueprint/validation/modules/generated-hashes.sha256
python3 blueprint/validation/modules/generate_modules.py --build
```

The generated package resolves a second library named
`TranslationalTilings`, uses `relaxedAutoImplicit=false` and
`maxSynthPendingDepth=3`, and imports declarations only across the direct
project edges recorded in `modules/module-map.json`.  The generator rejects
an unassigned or multiply assigned declaration, a stale ownership row, an
unknown import, or a cycle.  The build is offline: its manifest points to the
already-present pinned Mathlib dependency directories and `lake --no-cache`
disables cache downloads.

The generated sources under
`modules/BlueprintModuleValidation/` contain the same validator-only
exact-type axioms for bodyless theorems.  They must never be copied into or
imported by production.  See `modules/README.md` for the full artifact and
trust-boundary description.
