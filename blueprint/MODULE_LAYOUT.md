# Production module and Lake-package contract

This document froze the production-module boundary before proof files were
authored; the completed implementation instantiates that contract.  The
formalization is a second Lean library named
`TranslationalTilings`; it does not live below the existing measurable
`Tiling` hierarchy.  The mathematical namespace and the module root therefore
agree, while the dirty `Tiling` sources remain untouched.

## Exact production `lakefile.toml`

The production milestone applies only this patch to the pinned package's
existing target declarations.  All existing package options and the `Tiling`
library remain unchanged.

```diff
-defaultTargets = ["Tiling"]
+defaultTargets = ["Tiling", "TranslationalTilings"]

 [[lean_lib]]
 name = "Tiling"
+
+[[lean_lib]]
+name = "TranslationalTilings"
```

The new root file is `TranslationalTilings.lean`.  It imports
`TranslationalTilings.Main`; that transitive closure contains every module in
the manifest below.  The required production acceptance commands are:

```bash
lake query TranslationalTilings
lake build TranslationalTilings
lake build Tiling TranslationalTilings
```

The `lakefile.toml` is not changed during blueprint authoring.  In particular,
no current change below `Tiling/` is overwritten, moved, or made an accidental
dependency of the new library.

## Exact source and direct-project-import manifest

There are exactly 29 production modules, plus the umbrella.  An import in the
right column is direct; all omitted dependencies are reached transitively.
Mathlib imports are conservatively inherited from the owning blueprint
chapter in the pre-proof validator.  Production proofs may minimize those
Mathlib imports with `lake shake`, but may not add a project edge that violates
this DAG without updating and re-refereeing this contract.

| # | Production source | Direct project imports |
|---:|---|---|
| 1 | `TranslationalTilings/Basic.lean` | none |
| 2 | `TranslationalTilings/FiniteDifference.lean` | `TranslationalTilings.Basic` |
| 3 | `TranslationalTilings/Arithmetic.lean` | `TranslationalTilings.Basic` |
| 4 | `TranslationalTilings/LatticeGeometry.lean` | `TranslationalTilings.Arithmetic` |
| 5 | `TranslationalTilings/Dilation/Periodic.lean` | `TranslationalTilings.FiniteDifference`, `TranslationalTilings.LatticeGeometry` |
| 6 | `TranslationalTilings/Structure/Grouped.lean` | `TranslationalTilings.Dilation.Periodic`, `TranslationalTilings.LatticeGeometry` |
| 7 | `TranslationalTilings/Counterexample.lean` | `TranslationalTilings.Basic`, `TranslationalTilings.FiniteDifference`, `TranslationalTilings.LatticeGeometry` |
| 8 | `TranslationalTilings/NumberTheory/Stepanov/NewtonWaring.lean` | none |
| 9 | `TranslationalTilings/NumberTheory/Stepanov/ArtinLSeries.lean` | `TranslationalTilings.NumberTheory.Stepanov.NewtonWaring` |
| 10 | `TranslationalTilings/NumberTheory/Stepanov/ArtinSchreier.lean` | none |
| 11 | `TranslationalTilings/NumberTheory/Stepanov/HasseMultiplicity.lean` | none |
| 12 | `TranslationalTilings/NumberTheory/Stepanov/TranslationProduct.lean` | `TranslationalTilings.NumberTheory.Stepanov.ArtinSchreier`, `TranslationalTilings.NumberTheory.Stepanov.HasseMultiplicity`, `TranslationalTilings.NumberTheory.Stepanov.NewtonWaring` |
| 13 | `TranslationalTilings/NumberTheory/Stepanov/AdditivePointCount.lean` | `TranslationalTilings.NumberTheory.Stepanov.TranslationProduct` |
| 14 | `TranslationalTilings/NumberTheory/Stepanov/ReciprocalRoots.lean` | `TranslationalTilings.NumberTheory.Stepanov.AdditivePointCount`, `TranslationalTilings.NumberTheory.Stepanov.ArtinLSeries` |
| 15 | `TranslationalTilings/NumberTheory/PolynomialWeilBound.lean` | `TranslationalTilings.NumberTheory.Stepanov.ReciprocalRoots` |
| 16 | `TranslationalTilings/NumberTheory/FiniteCyclicPhase.lean` | none |
| 17 | `TranslationalTilings/NumberTheory/PolynomialCongruence.lean` | `TranslationalTilings.NumberTheory.FiniteCyclicPhase` |
| 18 | `TranslationalTilings/NumberTheory/ChenCompleteSum.lean` | `TranslationalTilings.NumberTheory.PolynomialCongruence` |
| 19 | `TranslationalTilings/NumberTheory/QuadraticCompleteSum.lean` | `TranslationalTilings.NumberTheory.FiniteCyclicPhase` |
| 20 | `TranslationalTilings/NumberTheory/CompleteExponentialSum.lean` | `TranslationalTilings.NumberTheory.ChenCompleteSum`, `TranslationalTilings.NumberTheory.QuadraticCompleteSum`, `TranslationalTilings.NumberTheory.PolynomialWeilBound` |
| 21 | `TranslationalTilings/Analysis/CirclePolynomial.lean` | `TranslationalTilings.FiniteDifference`, `TranslationalTilings.NumberTheory.CompleteExponentialSum` |
| 22 | `TranslationalTilings/Analysis/Equidistribution.lean` | `TranslationalTilings.Analysis.CirclePolynomial` |
| 23 | `TranslationalTilings/Analysis/FejerSeparator.lean` | `TranslationalTilings.Analysis.Equidistribution` |
| 24 | `TranslationalTilings/Analysis/PolynomialRigidity.lean` | `TranslationalTilings.Analysis.CirclePolynomial`, `TranslationalTilings.Analysis.Equidistribution`, `TranslationalTilings.Analysis.FejerSeparator` |
| 25 | `TranslationalTilings/WeakPeriodicity.lean` | `TranslationalTilings.Analysis.PolynomialRigidity`, `TranslationalTilings.Structure.Grouped` |
| 26 | `TranslationalTilings/Slicing.lean` | `TranslationalTilings.Dilation.Periodic`, `TranslationalTilings.LatticeGeometry` |
| 27 | `TranslationalTilings/PeriodicCompletion.lean` | `TranslationalTilings.Slicing`, `TranslationalTilings.WeakPeriodicity` |
| 28 | `TranslationalTilings/Algorithms.lean` | `TranslationalTilings.PeriodicCompletion` |
| 29 | `TranslationalTilings/Main.lean` | `TranslationalTilings.Algorithms`, `TranslationalTilings.Counterexample` |
| umbrella | `TranslationalTilings.lean` | `TranslationalTilings.Main` |

The two independent roots have no edge in either direction.  Number theory
has no tiling import.  Analysis depends only on number theory and the generic
finite-difference adapter.  The counterexample does not import dilation,
grouping, weak periodicity, or completion.  Algorithms and `Main` are the only
application leaves.

## Declaration ownership

The complete declaration-to-file manifest is generated at
`validation/modules/declaration-modules.tsv`.  It has one row for every Lean
declaration displayed in Chapters 01--09, including private declarations,
anonymous instances, and examples.  Its last two columns give the unique
production module name and source path.  The module generator rejects an
unassigned declaration, two matching ownership rules, a disagreement with the
integrated declaration ledger, a missing import target, or an import cycle.

The split is mathematical rather than merely chapter-sized:

- Chapter 01 separates finite convolution/periodicity from differences.
- Chapter 02 separates arithmetic/norms from lattice geometry.
- Chapter 03 separates dilation from grouped structural decomposition.
- Chapter 05a follows the eight Stepanov seams listed above.  The auxiliary
  linear system in `HasseMultiplicity` is independent of the Newton--Waring
  phase encoding.  `TranslationProduct` consumes both seams directly, making
  the actual dependency explicit without creating a cycle.
- Chapter 05b separates finite cyclic phases, congruence/stationary algebra,
  the conditional Chen recursion, quadratic sums, and the terminal
  Weil-backed specializations.  The proposition `PolynomialPrimeSumBound`
  lives in `FiniteCyclicPhase`; `ChenCompleteSum` exports only the
  `_of_primeBound` recursion.  Its proof `polynomialPrimeSumBound` and the
  unconditional wrappers `chen_prime_base`,
  `primePower_completeSum_bound`, and
  `ack_theorem_2_2_finiteProduct` live in
  `CompleteExponentialSum`, whose direct imports contain both the conditional
  Chen theorems and `PolynomialWeilBound`.  This non-contiguous ownership is
  necessary: placing any unconditional wrapper in `ChenCompleteSum` would
  require a Weil theorem absent from that module's dependency closure.
  The same terminal join owns
  `quadratic_polynomialCompleteSum_parity_bound` and
  `quadratic_polynomialCompleteSum_bound`: their proof consumes both the
  local prime-power quadratic API and Chen's support-indexed CRT certificate.
  `QuadraticCompleteSum` itself remains the independent local/prime-power
  branch and therefore imports only `FiniteCyclicPhase`.
- Chapter 05 separates circle-polynomial algebra, equidistribution, the Fejer
  separator, and final rigidity.
- Chapter 07 separates slicing from completion certificates and bounds.

This ownership is part of the public API freeze.  Moving an exported
declaration changes its import-level API even when its namespace and type stay
the same, so such a move requires a new validator run and snapshot review.

## Boundary validation and trust

`validation/modules/` contains a second, module-aware signature validator.
It shares only the Markdown extraction semantics with the integrated
validator.  It then assigns declarations to production homes, emits all 29
module files and the umbrella, writes the complete ownership ledger, checks
the DAG, and builds the generated `TranslationalTilings` Lake target.

Definitions, structures, instances, abbreviations, examples, and theorem
declarations with checked bodies are copied.  A bodyless theorem becomes an
exact-type validator-only `axiom`.  Consequently this test establishes module
resolution, import visibility, declaration ownership, option fidelity, and
acyclicity; it establishes no theorem proof.  Generated modules are under
`BlueprintModuleValidation/`, outside the production tree, and may
never be imported by production.

The nested validation package has an explicit path manifest for Mathlib and
all of Mathlib's already-present dependencies in the pinned checkout.  Its
build runs with cache downloads disabled and does not execute `lake update`.
Thus validation neither contacts the network nor creates a second dependency
resolution.  The authoritative commands are documented in
`validation/modules/README.md`.
