# Recursive dependency and mathlib audit

This file is the checklist used before implementation and again before the
final trust audit.  A prerequisite is "covered" only after its exact Mathlib
statement has been checked in the pinned version or a project module proves it.

## Dependency tree

```text
Paper main results
|- finite convolution tiling API
|  |- Finset sums, indicators, representation counts                [Mathlib]
|  `- translation and linear-equivalence transport                  [project]
|- lattice geometry
|  |- determinants, Cramer, subgroup index                           [Mathlib + adapters]
|  |- dimension-generic content and primitive common multiples       [project]
|  |- planar SL(2,Z) normalization                                   [project]
|  `- bounded avoidance vector and lcm bounds                        [project]
|- dilation and structure
|  |- group algebra Frobenius mod p                                  [project over Mathlib]
|  |- Fermat, prime factorization, lcm                               [Mathlib]
|  |- explicit Folner-box boundary estimate                          [project]
|  `- compact product / ultrafilter ray limits                       [Mathlib + adapter]
|- higher-level counterexample
|  |- sqrt(2) irrational, floor/fract                                [Mathlib]
|  `- concrete cancellation and finite-difference contradiction      [project]
|- weak periodicity
|  |- repeated finite differences                                    [project shared]
|  |- circle polynomial representation                               [project]
|  `- polynomial rigidity
|     |- Fourier characters and Haar measure on AddCircle            [Mathlib]
|     |- Weyl criterion and van der Corput                            [project]
|     |- residue-class splitting for higher torsion coefficients      [project]
|     |- rational coefficient denominators                            [project]
|     |- Newton/falling-factorial integral normalization              [project]
|     |- repeated normalized complete sums                            [project]
|     |- fixed-character prime polynomial estimate                    [Chapter 05a]
|     |  `- Stepanov auxiliary polynomial + multiplicity/root count   [project + Mathlib]
|     |- A--C--K/Chen complete rational sums                          [Chapter 05b]
|     |  |- integral phase <-> Polynomial Z <-> ZMod character bridge [project]
|     |  |- exact stationary residue-class recurrences (2.3)--(2.14) [project]
|     |  |- CRT, primitive-content transport, degrees one and two     [project + Mathlib]
|     |  `- degree padding and finite product of local factors        [project]
|     `- explicit Fejer separator                                     [project]
|- weak-to-periodic conversion
|  |- finite quotient-fiber assignment to directional parts                [project]
|  |- slicing via dilation ray limits                                 [project reuse]
|  |- finite canonical line-pattern representative                   [project]
|  |- singleton-tile completion by a multiplier-one target translate [project]
|  |- exact one-part completion and certificate rebasing              [project]
|  |- exact multi-part `CompletionCertificate` under `1<|F|`          [project]
|  |- singleton-safe `PaperCompletionResult` with component clause    [project]
|  |- structural derivation `2≤m≤|F|-1 ⇒ 1<|F|`                 [project]
|  `- disjointness from level-one nonnegativity                       [project]
`- algorithms
   |- finite tori, Boolean tables and checks                         [Mathlib + project]
   |- checked HNF wire format and proof-side finite-index coverage    [project]
   |- proof-free bounded tuple `Fintype`                              [project]
   |- finite-strip chameleon criterion                                [project]
   |- commutative counted `Finset.fold`                               [project]
   `- line-support geometry                                           [project]
```

## Exact pinned-Mathlib reuse map

| Need | Reused declaration or representation | Pinned import |
|---|---|---|
| One-period functions | `Function.Periodic` and its additive laws | `Mathlib.Algebra.Ring.Periodic` |
| Finite differences | `fwdDiff`, iterates, Gregory--Newton lemmas; project backward adapter | `Mathlib.Algebra.Group.ForwardDiff` |
| Finite convolution algebra | `AddMonoidAlgebra`, `Finsupp.single`, finite sums | `Mathlib.Algebra.MonoidAlgebra.Basic` |
| Finite lcms and gcds | `Finset.lcm`, `Finset.gcd`, divisibility lemmas | `Mathlib.Algebra.GCDMonoid.FinsetLemmas` |
| Small-prime product | root `primorial` and its prime-divisor/bound API | `Mathlib.NumberTheory.Primorial` |
| Euclidean norm | `WithLp.toLp 2`, `EuclideanSpace` | `Mathlib.Analysis.InnerProductSpace.PiL2` |
| Scalar subgroup index | nsmul range/index API | `Mathlib.GroupTheory.IndexNSmul` |
| Determinant algebra | adjugate identities; project 2D Cramer specialization | `Mathlib.LinearAlgebra.Matrix.Adjugate` |
| Compact products | compact Pi types and ultrafilter limits | `Mathlib.Topology.Compactness.Compact` |
| Additive circle | `AddCircle`, `fourier`, `AddCircle.haarAddCircle` | `Mathlib.Analysis.Fourier.AddCircle` |
| Rational torsion | `AddCircle.addOrderOf_coe_rat`, rational-point characterization | `Mathlib.Topology.Instances.AddCircle.Defs` |
| Polynomial content | `Polynomial.Content` | `Mathlib.RingTheory.Polynomial.Content` |
| Finite additive characters | `ZMod.stdAddChar`, character sums | `Mathlib.Analysis.Fourier.ZMod` |
| Finite search | `Fintype.piFinset`, `Finset.univ`, commutative `Finset.fold` | `Mathlib.Data.Fintype.Pi` |

All listed imports were accepted by the pinned Lean/Mathlib toolchain.  The
project still owns the adapters and every substantive theorem not named in the
second column; similarity to a Mathlib name is not counted as reuse.
`TranslationalTilings.FiniteDifference` is the sole owner of the project
backward-difference adapter; analytic modules import it rather than redeclaring
the constants.

## Public abstraction boundaries

The following are standalone reusable concepts and deserve public modules:

- finite-tile convolution on an additive group;
- subgroup/scalar/weak periodicity and explicit decompositions;
- dimension-generic commensurability/content/primitive decomposition and
  common-multiple bounds;
- planar wedge, Cramer inclusion, and `SL(2,Z)` normalization;
- discrete difference elimination for sums of periodic functions;
- fixed-character polynomial sums over prime fields and Chen complete sums;
- circle polynomial rigidity with an explicit period bound;
- periodic-set codes and finite-torus convolution.

The following stay application-specific:

- the Greenfeld-Tao counterexample sign/carry/tile;
- `QuantitativeWeakPeriodData` with the paper's particular q-N-M-L choices;
- slicing lcm for a particular tile and direction;
- chameleon slices and representative tuples.

## Do-not-refactor decisions

1. Do not reuse the neighboring measurable Euclidean `Tiling.Prototile` API.
   It models almost-everywhere disjoint measurable supports in normed groups,
   whereas this paper needs exact integer-valued finite convolution and
   higher-level tilings.  An adapter would add dependencies without sharing a
   theorem.
2. Do not model arbitrary convolution of two infinite functions.  Every use in
   the paper has a finite tile factor, and `tileConv` makes totality and
   computability immediate.
3. Do not make `WeaklyPeriodic` merely an existential equality of indicator
   sums.  The disjoint part sets and periods are later transformed separately.
4. Do not quotient directions by commensurability in the public API.  Concrete
   integer representatives and their norm bounds are part of Theorem 1.4.
5. Do not use classical choice to manufacture search orderings.  Export
   Boolean algorithms over fixed `Fintype` payloads with `= true iff`
   specifications; a derived `Decidable` theorem may be provided downstream.

## Quantitative audit

Every hidden constant in the paper is realized as an explicit function of the
allowed parameters:

| Paper notation | Closed Lean source |
|---|---|
| `q <<_|F| ell` | `indicatorDilationModulus`, root `primorial`, `Nat.lcm` |
| `e_tilde=O_|F|(1)` | `avoidanceVector`, l1 norm `<=|F|+1` |
| Lemma 4.2 constant | `stechkinNatConstant d = 2^(10*(d+1)^8)` |
| `Q_m=O_m(1)` | `weakRigidityPeriod m`, with `weakRigidityPeriod m ∣ weakRigidityPeriod c` only when passing to the cardinality cap |
| weak lattice index constant | `weakPeriodIndexConstant`, `weakPeriodIndexBound` |
| weak multiplier constant | `weakPeriodMultiplierConstant`, `weakPeriodMultiplierBound` |
| completion `N,N_j,C_j,s_j,L_j,M` | the six `completion*` definitions and `CompletionCertificate`, whose constructor requires `1<c` |
| general Theorem 5.4 result | singleton-safe `PaperCompletionResult`; `weakCompletionPeriodBound` with explicit `m` dependence; separate component-convolution field |
| structural Theorem 5.4 constant | `structuralCompletionPeriodBound` under `2≤m≤c-1`, which derives `1<c` before invoking the exact constructor |
| one-part completion | `onePartCompletionMultiplier`, its bound, and certificate rebasing |
| algorithm period cap | `periodicTilingPeriodBound` |
| arithmetic operation cap | `planarTileSearchCost`, `planarTileSearchExponent` |

The final comparator must show both the exact expression and the simplified
paper exponent for every row.

The completion audit must also retain the negative domain regression.  With
`c=1`, `D=0`, `m=2`, a permitted empty part of direction `(4096,0)`, and a
second part of direction `(0,1)`, the exact frozen construction has local
factor `4096^2` and total multiplier `4096^3`, whereas the old advertised
bounds are `48*4096` and `48^2*4096^2`.  The theorem
`completion_singleton_bound_regression` checks both strict failures.  Hence no
future refactor may remove `1<c` from the exact constructor merely because the
weaker paper-facing existential result is singleton-safe.

## Trust audit commands

Before implementation, the strict integrated signature check runs against the
pinned Lean 4.33.0/Mathlib 4.33.0 checkout:

```bash
python3 blueprint/validation/generate_integrated.py --check
cd /home/codex/Documents/Codex/2026-08-14/Tiling
lake env lean \
  /home/codex/Documents/Codex/2026-08-24/usi/blueprint/validation/BlueprintIntegrated.lean
cd /home/codex/Documents/Codex/2026-08-24/usi
python3 blueprint/validation/modules/generate_modules.py --check
python3 blueprint/validation/modules/generate_modules.py --build
```

The generator rejects malformed Lean fences, duplicate public names, untyped
theorem aliases, proof placeholders, source `axiom`/`opaque` commands, and
vacuous `:= True` declarations.  The strict generated file adds no global
classical instances.  Its bodyless theorem declarations are exact-type
validator stubs, so its `axiom` commands are not project assumptions and the
module must never be imported by production code.

The module-aware validator is a second non-production artifact.  It maps all
declaration rows to the exact 29-file manifest in `MODULE_LAYOUT.md`, rejects
cycles and unresolved project imports, and compiles each boundary plus the
umbrella under the package options.  Its offline Lake manifest points to the
already-present pinned dependency directories and its build disables cache
downloads; it performs no dependency update.

The final repository check runs, at minimum:

```bash
lake build Tiling TranslationalTilings
if rg -n '\bsorry\b|\badmit\b|^\s*axiom\b|^\s*opaque\b' \
    TranslationalTilings; then exit 1; fi
if rg -n '^\s*import .*(BlueprintIntegrated|BlueprintModuleValidation)' \
    TranslationalTilings; then exit 1; fi
lake env lean scripts/PrintAxioms.lean
```

`PrintAxioms.lean` prints axioms for all paper-facing declarations.  Standard
Lean axioms such as quotient soundness, propext, and classical choice are
reported but are not proof gaps.  Any project-defined axiom or opaque theorem
is a failure.

## Blueprint review questions

Mathematical reviewers must check:

1. Are the paper statements reproduced with correct quantifier order,
   especially independence from `A` in Theorem 1.4?
2. Are all four recorded source errata correctly separated from blueprint
   repairs?
3. Does Lemma 4.2 retain the exact exponent `1-1/d`, with a degree-only
   constant and a complete Weil/Chen recursive proof?
4. Are all divisions in q-N-M-L known to be exact?
5. Do singleton/empty tiles and targets behave correctly?
6. Does the chameleon iff proof cover every tiling and prove both directions?

Lean reviewers must check:

1. Do all displayed definitions and signatures elaborate in pinned mathlib?
2. Are proof-relevant certificates minimal and downstream-friendly?
3. Can dependent finite searches synthesize `Fintype` and `DecidableEq`, and
   do all Boolean paths avoid `Finset.toList`, arbitrary sets, and quotient
   choice?
4. Are imports directed from general to specialized with no cycles?
5. Are there existing Mathlib declarations that subsume project helpers?
6. Does the planned polynomial-rigidity representation fit AddCircle's actual
   API and topology?

All reviewers also apply the independent, adversarial acceptance protocol in
`11-refereeing-standard.md`.  In particular, a successful build cannot excuse
a vacuous statement, an assumption that contains the intended result, or a
duplicated Mathlib declaration.
