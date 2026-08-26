# Module-boundary validation report

Date: 2026-08-24 UTC.  This is author evidence for the FLSR-2 repair, not an
independent approval and not proof evidence.

## Fixed environment

```text
pinned project commit: b6744348ec0c2ab44788000b031721b861424c2f
Lean:                  4.33.0
Mathlib:               db584cd6d46c92f209a44c0f1c829460d327499d
production modules:    29 plus one umbrella
declaration rows:      869
visibility:            858 public, 1 private, 10 anonymous
representation:        356 definitions, 56 checked bodies,
                       457 exact-type validator axioms
```

The generated Lake package carries the pinned package's four option entries,
including `relaxedAutoImplicit=false` and `maxSynthPendingDepth=3`.  Its
manifest has only absolute path packages into the existing pinned checkout.
There is no generated `.lake/packages` directory.  The build command disables
cache downloads, and its subprocess rewrites any unexpected HTTP(S) git
transport to a nonexistent local path.

## Commands and results

```bash
python3 blueprint/validation/modules/generate_modules.py --write
python3 blueprint/validation/modules/generate_modules.py --check
python3 blueprint/validation/modules/generate_modules.py --build
sha256sum -c blueprint/validation/modules/generated-hashes.sha256
cd blueprint/validation/modules/BlueprintModuleValidation
lake query TranslationalTilings
```

All commands completed successfully.  The generator reports:

```text
module validation current: 29 modules; 869 declarations; DAG acyclic
Build completed successfully (3446 jobs).
```

The first boundary build failed because `Dilation.Periodic` used
`scalarLattice` while importing only `Arithmetic`.  That was genuine evidence
that the former chapter-sized monolith concealed a dependency.  The repaired
direct edge is

```text
TranslationalTilings.Dilation.Periodic
  -> TranslationalTilings.LatticeGeometry
```

and the subsequent complete build passed.  This demonstrates why the
module-aware artifact is required in addition to the integrated monolith.

After FMS3-1 introduced the support-indexed factorization API, the next build
caught stale Chapter 05b section cuts: part of the global Chen bridge had
shifted into `QuadraticCompleteSum` without its owner import.  The ownership
cuts now follow the current Section 9 and Section 10 boundaries, keeping the
entire CRT/global finite-product bridge in `ChenCompleteSum`; the complete
rebuild then passed.  This second caught regression is further evidence that
`--check` and the actual Lake boundary build are both mandatory.

The first genuine production proof pass then exposed a third boundary defect
that exact-type axiom stubs could not reveal.  The unconditional
`chen_prime_base`, `primePower_completeSum_bound`, and
`ack_theorem_2_2_finiteProduct` wrappers require the proved
`PolynomialPrimeSumBound`, but `ChenCompleteSum` intentionally imports only
the conditional congruence/recursion layer.  Their `_of_primeBound` versions
remain in `ChenCompleteSum`; the three unconditional wrappers now have
non-contiguous ownership in `CompleteExponentialSum`, alongside
`polynomialPrimeSumBound`.  That module directly imports both the conditional
Chen layer and `PolynomialWeilBound`, so the repaired edge is acyclic and
proof-realizable.  The integrated validator and the complete 29-module build
both pass after this ownership repair.

The production quadratic proof pass exposed the analogous join requirement
for composite moduli.  `QuadraticCompleteSum` proves the linear, prime-power,
parity, and Gauss-sum local APIs without Chen, but the documented global
parity product explicitly consumes `CompleteSumFactorizationData`.  The
composite wrappers `quadratic_polynomialCompleteSum_parity_bound` and
`quadratic_polynomialCompleteSum_bound` now live in
`CompleteExponentialSum`, which is already the acyclic join of the local
quadratic branch and Chen's CRT certificate.  A generator regression enforces
both this split and the conditional/unconditional Weil split.  The complete
module build passes after the repair.

The independent PM1 review also caught that the prose-only term
`Fact.out.ne_zero` did not elaborate without an expected prime type.  The
actual `polynomialPrimeSumBound` declaration is now a checked body using
`(Fact.out : p.Prime).ne_zero`; strict integrated and module elaboration thus
test the bridge itself rather than replacing it by an axiom stub.

The production middle-prime induction then exposed that `ack_ineq_2_10`
needs the explicit upper-range hypothesis used by its child call to (2.6).
The repaired signature takes `hpB`; all terminal callers already inhabit it
in precisely that branch.  Two independent PM3 reviews approved the repair.

Production also found that Proposition 4.4's displayed proof used periodicity
of the target even though its former public signature retained only the raw
grouped decomposition.  A strict concrete countermodel falsified that old
signature.  The core theorem and paper-facing alias now both take
`SetScalarPeriodic ell E`; the uniform quantitative callback already had this
hypothesis and passes it through, leaving the terminal theorem types stable.

Finally, the production coverage audit exposed two validator defects.  The
canonical parser now recognizes attribute-prefixed declarations, so the two
`@[simp]` factorization-scalar lookup lemmas receive their own public ownership
rows rather than being hidden inside a preceding chunk.  It also verified the
exact binder order of `hasseDeriv_eval_frobenius`; the blueprint now binds the
prime explicitly after the field instance, exactly as production does.  The
honest ledger therefore contains 869 rather than 867 declarations.

The production import audit also removed the artificial
`HasseMultiplicity -> NewtonWaring` edge.  Hasse now has only its direct
Mathlib prerequisites, while `TranslationProduct` owns the direct Newton
dependency needed by its `eraseConstant` interfaces.  The generated DAG and
future lakefile encode that repaired boundary; the full offline build passes
without relying on the former transitive import.

The build emits only style warnings for generated source-location comments,
long copied signatures, and the generated `Main` header.  The three anonymous
Chapter 08 regressions use kernel `decide`; no `native_decide` warning or
native-code trust seam remains.  No module-resolution, elaboration, or cycle
error remains.

## Principal artifact hashes

```text
67ba38fdb4da7ed8058b71ef6f694f8c0f0f2ad2f212a64542973e542b34b92e  blueprint/MODULE_LAYOUT.md
f8794e06f4762d16d79699c596faf9465e18ece342b2e44df96028ac91aa914f  blueprint/validation/modules/future-lakefile.toml
1b6353443e648f701e479e37ad797e4ba29870c00d24b83b86d5fc971042aa06  blueprint/validation/modules/module-map.json
e9230f042900319ac1e1cbac42741531f3785f4536e14b7b2c96190afcab2337  blueprint/validation/modules/generate_modules.py
8bd2eaabe9c99d04808fbc81d0d7ba4a78e6bdb17bc680b5b02896e922725bc6  blueprint/validation/modules/declaration-modules.tsv
77f20a932a9a5821b698691c046802e379e1962c855bb24a7934b28f8981896c  blueprint/validation/modules/module-sources.tsv
5fbaef2d6cac20c3afa1e011a4c4cc9e27cd63ab54f6bb6a5c0e0b03d1ee0142  blueprint/validation/modules/generated-hashes.sha256
4db3951f784002a514ef1f36c0ef7d6386844ad338e119612c13991658d422d9  blueprint/validation/modules/BlueprintModuleValidation/lakefile.toml
a18a9e4a94f5d33e7cd12d6fca5e6e446cf648a2f32ec0aa6b4a5aae897f038c  blueprint/validation/modules/BlueprintModuleValidation/lake-manifest.json
abba4139f2a58521daa97ec3d7075fabd0f46a06a304a5701cff918ae395304d  blueprint/validation/modules/BlueprintModuleValidation/TranslationalTilings.lean
```

`generated-hashes.sha256` contains the umbrella, every generated module,
package metadata, source manifest, ownership ledger, module map, and generator
source.  It is the complete machine-checkable hash set; the abbreviated list
above is only a human-facing index.
