# Final independent Lean/mathlib snapshot rereview

## Verdict

**BLOCK.** This verdict is bound only to the blueprint manifest whose SHA-256 is

```text
247da8b51bf5dceb79d1d87a013e3ae973b5a758093f613d824db207f9ff8dd6
```

It is not authorization to begin production Lean.  The two P1 findings below
must be repaired in the blueprint, generated artifacts, and package plan, after
which a new manifest must receive a fresh independent review.  There are no P0
findings.  I found no independent P2 finding beyond consequences already
included in the two P1 findings.

This is a clean-room review.  Earlier approvals were not used as evidence.
Validator theorem axioms were treated only as evidence that a type elaborated
under the options actually used; they were never treated as proof evidence.

## Snapshot and environment checked

I independently verified every manifest entry before reading the snapshot:

```text
$ sha256sum blueprint/SNAPSHOT.sha256
247da8b51bf5dceb79d1d87a013e3ae973b5a758093f613d824db207f9ff8dd6  blueprint/SNAPSHOT.sha256
$ sha256sum -c blueprint/SNAPSHOT.sha256
blueprint/README.md: OK
blueprint/01-foundations.md: OK
blueprint/02-lattice-geometry.md: OK
blueprint/03-dilation-structure.md: OK
blueprint/04-counterexample.md: OK
blueprint/05a-weil-stepanov.md: OK
blueprint/05b-chen-complete-sums.md: OK
blueprint/05-polynomial-rigidity.md: OK
blueprint/06-weak-periodicity.md: OK
blueprint/07-periodic-completion.md: OK
blueprint/08-algorithms.md: OK
blueprint/09-main-results.md: OK
blueprint/10-recursive-dependency-audit.md: OK
blueprint/11-refereeing-standard.md: OK
blueprint/COMPARATOR.md: OK
blueprint/validation/README.md: OK
blueprint/validation/generate_integrated.py: OK
blueprint/validation/BlueprintIntegrated.lean: OK
blueprint/validation/declaration-coverage.tsv: OK
blueprint/reviews/resolution-log.md: OK
```

I read every manifest-listed blueprint and review file in full, including all of
`05a-weil-stepanov.md`, `05b-chen-complete-sums.md`, the corrected Chapters 7
and 9, the comparator, recursive audit, refereeing protocol, validation guide,
generator, declaration ledger, and resolution log.  I also scanned every line
and every declaration row of the generated integrated source and coverage
ledger.  The pinned executable environment was:

```text
project commit: b6744348ec0c2ab44788000b031721b861424c2f
Lean:           4.33.0 (d8b18978322de05a8f3dba51ef03cf5461676c17)
Mathlib:        db584cd6d46c92f209a44c0f1c829460d327499d
```

The pinned project worktree was not clean: `Tiling.lean` and
`Tiling/Basic.lean` were modified, and `Tiling/Geometry/`,
`Tiling/Topology/`, and `blueprint/` were untracked.  The observations below are
therefore about the exact files and commits named here, not an abstract clean
checkout.

## Mechanical and API audit

The snapshot generator freshness check passed:

```text
python3 blueprint/validation/generate_integrated.py --check
```

The documented elaboration command also passed, as did the same command with
only the package's `maxSynthPendingDepth=3` option supplied:

```text
lake env lean \
  /home/codex/Documents/Codex/2026-08-24/usi/blueprint/validation/BlueprintIntegrated.lean
lake env lean -DmaxSynthPendingDepth=3 \
  /home/codex/Documents/Codex/2026-08-24/usi/blueprint/validation/BlueprintIntegrated.lean
```

The ledger has 857 declaration rows: 846 public, one private, and ten
anonymous.  By declaration kind it contains 20 structures, 324 definitions,
seven instances, nine abbreviations, three examples, and 494 theorems.  By
validator representation it contains 353 definitions, 46 checked bodies, and
458 exact-type axiom stubs.  I found no malformed row, empty public name,
duplicate public qualified name, namespace escape, or private name exported as
a stable public name.

That is useful interface evidence, but it is deliberately not evidence that any
of the 458 bodyless theorem proofs exists.  In addition, the passing documented
command is not the actual production option check; Finding FLSR-1 explains why.

## Findings

### FLSR-1 — P1 — the strict validator bypasses `relaxedAutoImplicit=false`; 50 planned declarations do not elaborate with production options

The pinned package declares:

```toml
[leanOptions]
relaxedAutoImplicit = false
maxSynthPendingDepth = 3
```

Those Lake target options are not automatically applied by a direct
`lake env lean path/to/file.lean` invocation.  The validation guide calls that
direct command and the generated file does not contain
`set_option relaxedAutoImplicit false`.  Consequently its reported strict pass
accepts undeclared multi-character parameters which production modules reject.

The exact production-option reproduction was:

```text
$ lake env lean -DrelaxedAutoImplicit=false -DmaxSynthPendingDepth=3 \
    -DmaxErrors=1000 \
    /home/codex/Documents/Codex/2026-08-24/usi/blueprint/validation/BlueprintIntegrated.lean
exit status 1
```

It produced 112 `lean.unknownIdentifier` diagnostics at 112 source locations on
97 distinct source lines.  They comprise 93 occurrences of `ell`, eight of
`eps`, two of `line`, six cascading occurrences of `CompletionCertificate`,
and three cascading occurrences of `PaperCompletionResult`.  Mapping every
diagnostic to its enclosing declaration gives exactly the following 50-declaration
ledger (the certificate/result-name errors are downstream of declarations whose
earlier implicit parameters failed):

- Chapter 5 polynomial-rigidity, four declarations:
  `integral_ballBump_pos`, `not_equidistributed_of_avoidsBall`,
  `rational_nonconstant_coefficients_of_avoidsBall`, and
  `torsion_nonconstant_coefficients_of_avoidsBall` (`eps`).
- Chapter 6, fifteen declarations: `weakN_bound`, `weakM_bound`,
  `weakLattice_le_scalar`, `weakLattice_relativeIndex_bound`,
  `weakMultiplier_pos`, `weakMultiplier_bound`, `weak_period_mem_lattice`,
  `exists_weakArithmeticData`, `QuantitativeWeakPeriodData.lattice`,
  `QuantitativeWeakPeriodData.multiplier`,
  `QuantitativeWeakPeriodData.ValidFor`, `linePhi_sum_mod_one`,
  `linePhi_circlePolynomial`, `linePhi_pair_sup_le_one`, and
  `coset_one_dimensional_periodicity` (`ell`).
- Chapter 7, twenty-four declarations: `mem_slicePattern` (`line`), and
  `completionPairLCM`, `completionAvoidance`, `completionWedgeFactor`,
  `completionConvolutionMultiplier`, `completionPrimitiveDirection`,
  `completionDirectionContent`, `completionDilationRatio`,
  `completionSliceLCM`, `completionPartMultiplier`, `completionMultiplier`,
  `onePartDilationRatio`, `onePartCompletionMultiplier`,
  `onePartDilationRatio_spec`, `onePartDilationRatio_pos`,
  `CompletionCertificate.toPaperCompletionResult`,
  `CompletionCertificate.completedMultiplier_structural_bound`,
  `one_lt_tileCard_of_structural_parts`, `improve_onePart`,
  `convolution_part_scalarPeriodic`, `improve_weaklyPeriodic_exact`,
  `improve_weaklyPeriodic_structural`,
  `singleton_tile_periodic_completion`, and `improve_weaklyPeriodic` (`ell`).
- Chapter 9, seven declarations: `proposition_4_1_i`,
  `proposition_4_1_ii`, `proposition_4_1_iii`, `proposition_4_4`,
  `theorem_5_3`, `theorem_5_3_exact`, and
  `theorem_5_3_structural` (`ell`, with downstream certificate/result-name
  errors).

This is a public-signature and production-implementability failure, not a
tactic-style issue.  It directly affects the corrected completion API singled
out for final review.

Required repair:

1. Bind every intended parameter explicitly in its displayed declaration.  At
   minimum this means explicit `{eps : ℝ}`, `{ell : ℕ}`, and a typed `line`
   binder (with its dependent `h`/set context) at the sites above.  Check the
   intended circle center binder as well wherever the `eps` theorems use it.
2. Make the acceptance artifact enforce the package option itself, for example
   with `set_option relaxedAutoImplicit false` in generated output, or run it
   through a registered Lake target carrying the exact target options.  The
   acceptance command must reproduce all package options, not just the Lean
   executable and import path.
3. Regenerate the integrated source and declaration ledger, run the strict
   check under the pinned package options, update all source hashes, freeze a
   new manifest, and independently review the resulting parameter order and
   public types.  Merely enabling relaxed auto-implicit for the future library
   would silently change the pinned project's API policy and is not an adequate
   repair without a documented, reviewed decision.

### FLSR-2 — P1 — the proposed module root and import graph are not integrated into the pinned Lake package

The actual `lakefile.toml` has only:

```toml
defaultTargets = ["Tiling"]

[[lean_lib]]
name = "Tiling"
```

There is no `TranslationalTilings` library target or umbrella module.  The
blueprint nevertheless specifies production files and imports rooted at
`TranslationalTilings.*`.  The mismatch is observable now:

```text
$ lake query TranslationalTilings.Basic
error: unknown target `TranslationalTilings.Basic`
$ lake build TranslationalTilings
error: unknown target `TranslationalTilings`
```

The blueprint also has no complete one-to-one module/file ownership map.  Its
top-level table assigns Chapter 3 to `.Dilation` and `.Structure`, while later
chapters import the more specific, unmapped paths
`TranslationalTilings.Dilation.Periodic` and
`TranslationalTilings.Structure.Grouped`.  The displayed project imports are:

```text
TranslationalTilings.Basic
TranslationalTilings.FiniteDifference
TranslationalTilings.Arithmetic
TranslationalTilings.LatticeGeometry
TranslationalTilings.NumberTheory.PolynomialWeilBound
TranslationalTilings.NumberTheory.CompleteExponentialSum
TranslationalTilings.Analysis.PolynomialRigidity
TranslationalTilings.Structure.Grouped
TranslationalTilings.Dilation.Periodic
TranslationalTilings.WeakPeriodicity
TranslationalTilings.PeriodicCompletion
TranslationalTilings.Counterexample
TranslationalTilings.Algorithms
```

No actual file plan resolves all of those imports, their lower number-theory and
analysis modules, chapter declarations split between sibling modules, or the
umbrella/default build target.

The integrated validator cannot detect this problem.  In
`generate_integrated.py`, lines 126–130 retain only imports whose names start
with `Mathlib` and discard every project import.  It then concatenates all
chapters into one dependency-ordered monolith.  Thus its pass tests neither
project-module resolution nor per-file visibility, import minimality, cycles,
or the claimed module boundaries.

Required repair: choose and document exactly one production layout before
authoring proof files.  The cleaner option, consistent with the blueprint's
deliberate rejection of the measurable `Tiling.Prototile` abstraction, is a
second independent library root:

```toml
defaultTargets = ["Tiling", "TranslationalTilings"]

[[lean_lib]]
name = "Tiling"

[[lean_lib]]
name = "TranslationalTilings"
```

Add a `TranslationalTilings.lean` umbrella and an explicit source manifest such
as:

```text
TranslationalTilings/Basic.lean
TranslationalTilings/FiniteDifference.lean
TranslationalTilings/Arithmetic.lean
TranslationalTilings/LatticeGeometry.lean
TranslationalTilings/Dilation/Periodic.lean
TranslationalTilings/Structure/Grouped.lean
TranslationalTilings/NumberTheory/PolynomialWeilBound.lean
TranslationalTilings/NumberTheory/CompleteExponentialSum.lean
TranslationalTilings/Analysis/PolynomialRigidity.lean
TranslationalTilings/WeakPeriodicity.lean
TranslationalTilings/Slicing.lean
TranslationalTilings/PeriodicCompletion.lean
TranslationalTilings/Algorithms.lean
TranslationalTilings/Counterexample.lean
TranslationalTilings/Main.lean
```

The source manifest must expand the documented lower Stepanov, Chen, and
analysis modules and assign every displayed public declaration exactly one
home.  Its direct import graph must preserve the advertised direction:
foundations/arithmetic first; counterexample independent of structure;
number theory independent of tilings; analysis above number theory; weak
periodicity above analysis and grouped structure; completion above dilation and
weak periodicity; algorithms and `Main` downstream.  Validate each planned
module separately and then `lake build TranslationalTilings` with the exact
package options.

The alternative is to place files below `Tiling/TranslationalTilings/` and
rename every production import to `Tiling.TranslationalTilings.*` (or choose a
documented `Tiling.*` hierarchy).  That is a materially different public module
API and must be reflected consistently in every blueprint file, comparator,
audit, validator, and build command.  Keeping namespace
`TranslationalTilings` does not require keeping the same module root, but the
module-root choice cannot remain implicit.

## Independent mathematical and library-suitability conclusions

Subject to the two elaboration/integration blockers above, I did not identify a
new mathematical-statement blocker in the frozen design.

- The paper dependency chain is recursively decomposed.  The Stepanov layer
  supplies Newton–Waring, orbit/minimal-polynomial, Artin–Schreier, Hasse,
  linear-system, translation-product, and root-alignment prerequisites.  The
  Chen layer supplies stationary recurrence, endpoint estimates, CRT,
  low-degree linear/quadratic cases including the 2-primary branches, and the
  effective finite global factor.  These are genuine proof obligations, not
  citations hidden behind an opaque certificate.
- The separation between finite convolution/algebra, lattice geometry,
  dilation/grouping, analytic-number-theory rigidity, weak periodicity,
  completion, and computation is appropriate for reuse.  The blueprint's
  decision not to reuse the existing measurable `Tiling.Prototile` API is
  justified: that abstraction has a different carrier and theorem boundary
  from finite `Finset (Fin d → ℤ)` translational tilings.  This design decision
  does not, however, solve the Lake module-root issue in FLSR-2.
- The corrected Theorem 5.3 API is mathematically honest.  `PaperCompletionResult`
  stores the paper-facing periodic completion, the general multiplier bound,
  and the separate component-convolution conclusion.  The exact
  `CompletionCertificate` is restricted to `1 < F.card` by
  `improve_weaklyPeriodic_exact`.  The structural theorem derives that
  hypothesis from `2 ≤ numberOfParts ≤ F.card - 1`; it does not smuggle a new
  public cardinality assumption into the paper-facing result.
- The singleton branch translates the periodic target and uses multiplier one,
  rather than promising the false exact construction.  The checked-body theorem
  `completion_singleton_bound_regression` verifies the numerical core at
  `k=4096`: the advertised old local and total bounds are strictly below the
  exact singleton values.  This is a substantive regression, not merely prose.
- The computational layer uses finite Boolean tables and executable positive
  searches, provides an explicit HNF-style lattice-period wire format and
  `LineSelection`, distinguishes empty and singleton cases, and states exact
  unit-cost recurrences before closed bounds.  The empty-tile test returns the
  documented `(false, 17)` value, the chameleon regression is represented, and
  the cost model is explicitly unit-cost arithmetic rather than bit complexity.
- The complete-sum API handles modulus one, constant, linear, quadratic,
  odd-prime-power, 2-adic, mixed-even, and actual-degree-padding cases instead
  of applying the degree-at-least-three induction vacuously.  The completion and
  algorithm layers likewise treat zero/empty and singleton boundaries
  explicitly.

These conclusions concern the suitability and mathematical content of the
blueprint.  They do not prove the 458 stubbed theorem bodies, and therefore do
not independently certify that production will be sorry-free.  A later
production audit must scan the new library for `sorry`, `admit`, declarations of
new axioms/opaque certificates, and imports of `BlueprintIntegrated`.  If the
desired trust claim is repository-wide rather than limited to the new library,
the pre-existing `sorry` at `Tiling/Geometry/Plate.lean:125` must also be removed
or the trust scope must be stated explicitly.

## Preserve during repair

The following should not be weakened while resolving the blockers:

- keep `PaperCompletionResult` distinct from the stronger exact
  `CompletionCertificate`;
- keep the direct singleton construction and the checked `k=4096` regression;
- keep the structural derivation of `1 < F.card` from the part-count bounds;
- keep project number theory independent of tiling modules and keep the
  counterexample independent of the structure theorem;
- keep executable `Bool` predicates separate from proof-valued specifications,
  and retain the exact HNF wire format and the stated unit-cost scope;
- keep validator theorem stubs outside the production trust boundary.

## Re-review gate

A successor snapshot is eligible for unconditional approval only after all of
the following pass:

1. every intended parameter in the 50-declaration error ledger is explicit;
2. the generated validator enforces all pinned package options and elaborates
   with Lean 4.33.0/Mathlib `db584cd6d4`;
3. the chosen library/module root, every source-file home, the complete direct
   import DAG, umbrella module, and default Lake target are documented;
4. every planned production module separately elaborates through Lake, and the
   whole chosen target builds;
5. generated artifacts, declaration ledger, comparator, audit, resolution log,
   and hashes are regenerated and frozen under a new manifest;
6. independent referees review that new manifest rather than carrying forward
   this report's nonblocking mathematical observations as an approval.

Until then, the manifest identified at the top of this report remains
**BLOCKED**.
