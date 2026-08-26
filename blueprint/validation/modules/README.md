# Module-boundary signature validation

This directory validates the production module contract in
`../../MODULE_LAYOUT.md`.  It is independent of the genuine production source
tree and outside the formalization trust boundary.

Run from the blueprint repository root:

```bash
python3 blueprint/validation/modules/generate_modules.py --check
python3 blueprint/validation/modules/generate_modules.py --build
```

`--check` verifies all generated text byte-for-byte, compares every
declaration with `../declaration-coverage.tsv`, proves that ownership is total
and unique, checks all module names and import targets, and topologically sorts
the direct project-import graph.  `--build` first performs that check and then
runs the pinned Lake executable on the generated target:

```bash
lake --no-cache build TranslationalTilings
```

The generated package carries the same four Lean options as the pinned
package, including `relaxedAutoImplicit = false` and
`maxSynthPendingDepth = 3`.  Its checked-in `lake-manifest.json` maps Mathlib
and every inherited package to the corresponding existing directory below
`/home/codex/Documents/Codex/2026-08-14/Tiling/.lake/packages`; no dependency
is fetched or updated.  The generator also checks the Mathlib git revision
against `db584cd6d46c92f209a44c0f1c829460d327499d` before building.

Generated artifacts are:

- `declaration-modules.tsv`: complete declaration-to-production-file ledger;
- `BlueprintModuleValidation/TranslationalTilings/**/*.lean`: the 29 planned
  module boundaries;
- `BlueprintModuleValidation/TranslationalTilings.lean`: umbrella;
- `BlueprintModuleValidation/lakefile.toml`, `lean-toolchain`, and
  `lake-manifest.json`: offline pinned validation package;
- `future-lakefile.toml`: frozen copy of the exact production package file,
  preserving `Tiling`
  and adding the second default library target;
- `generated-hashes.sha256`: hashes of all generated acceptance inputs.
- `build-report.md`: author-side command, environment, result, and principal
  hash record for the last successful module build.

Bodyless theorems are validator-only exact-type axioms.  A successful build
is interface and module evidence only, never proof evidence.  The production
audit must reject any import from
`blueprint.validation.modules`, `BlueprintModuleValidation`, or either
validator tree.
