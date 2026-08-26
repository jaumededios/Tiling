# Lean 4 / Mathlib suitability re-review

## Snapshot, method, and verdict

This is an independent Tau-Ceti-style and `referee-lean-library` re-review of
the corrected blueprint snapshot identified by `blueprint/SNAPSHOT.sha256` on
2026-08-24.  I read the README, Chapters 01--11, `COMPARATOR.md`, the resolution
log, every current `tmp/Blueprint*.lean` validator, and the relevant pinned
Mathlib sources.  `sha256sum -c blueprint/SNAPSHOT.sha256` succeeds for every
listed file.

The pinned environment is:

```text
Lean 4.33.0, commit d8b18978322de05a8f3dba51ef03cf5461676c17
Mathlib db584cd6d46c92f209a44c0f1c829460d327499d
```

All nine validators compile in that environment (the algorithm validator uses
the generated `BlueprintCompletion.olean`).  This is useful evidence for the
isolated fragments, but Findings L27--L28 explain why it is not evidence that
the Markdown API itself elaborates as one library.

**Verdict: REJECT.**  The snapshot is not yet a sound frozen specification for
proof implementation.  Three displayed public theorems are false (L24--L26),
the signature evidence is materially unfaithful and is not part of the hashed
snapshot (L27), the proposed module graph has an actual duplicate-declaration
collision (L28), and the two largest recursively required developments are
still described rather than specified (L29--L30).  These are P0/P1 blockers.
Do not begin the proof implementation from this snapshot.  The verdict is
snapshot-specific; a corrected snapshot must be independently re-reviewed.

Priorities are P0 = false result/specification, P1 = implementation or
integration blocker, P2 = material API/maintainability defect, and P3 = polish.

## Findings

### L24 (P0) — the backward/forward difference bridge has the wrong sign

**Risk.**  The public bridge used to reuse Mathlib's finite-difference results
is false, so any proof transported through it has the opposite sign.

**Location and evidence.**  `blueprint/01-foundations.md:244-246` states

```lean
backwardDiff h f = fun x => -fwdDiff h f (x - h)
```

but `backwardDiff h f x = f x - f (x-h)`.  Pinned
`Mathlib/Algebra/Group/ForwardDiff.lean:42-46` defines
`fwdDiff h f n = f (n+h)-f n`, hence

```text
fwdDiff h f (x-h) = f x - f (x-h) = backwardDiff h f x.
```

For `G=R=Int`, `h=1`, and `f=id`, the displayed equality says `1=-1`.
`tmp/BlueprintFoundations.lean:161-163` faithfully typechecks the same false
proposition as a `def`; it does not prove it.

**Concrete fix.**  Remove the negation and preferably rename the theorem to
`backwardDiff_eq_fwdDiff_translate`:

```lean
theorem backwardDiff_eq_fwdDiff_translate {G R : Type*}
    [AddCommGroup G] [AddCommGroup R] (h : G) (f : G → R) :
    backwardDiff h f = fun x ↦ fwdDiff h f (x - h)
```

Add the `Int` identity-function regression before downstream reuse.

### L25 (P0) — normalized complete-sum repetition is false at `Q = 0`

**Risk.**  A public arithmetic transport lemma used in the rigidity proof is
not total on its stated domain.

**Location and evidence.**  `blueprint/05-polynomial-rigidity.md:432-438`
assumes `0 < Q'`, `Q' | Q`, and `P.PeriodicWith Q'`, but not `0 < Q`.
Divisibility does not imply positivity because every positive `Q'` divides
zero.  Take the zero circle polynomial, `Q=0`, and `Q'=1`.  The left normalized
sum is zero (the interval is empty and `(0 : ℂ)⁻¹=0`), while the right
normalized sum is one.  The validator repeats the same omission at
`tmp/BlueprintPolynomial.lean:203-206`.

**Concrete fix.**  Add `(hQ : 0 < Q)`.  If the intended API only repeats the
exact common denominator, specialize the theorem further so positivity follows
from `commonDenominator_pos`; still retain a total low-level lemma with both
positive hypotheses.

### L26 (P0) — the unconditional grouped-direction cardinality bound is false

**Risk.**  The canonical direction API exports a false size theorem and the
classifier depends on this bound to justify finite indices and quantitative
exponents.

**Location and evidence.**  `blueprint/06-weak-periodicity.md:73-74` states

```lean
theorem groupedDirectionCount_le (F : Finset Plane) :
  groupedDirectionCount F ≤ F.card - 1
```

with no `0 ∈ F` hypothesis.  For the singleton `F={![1,0]}`, the image of
`F.erase 0` has cardinality one, while `F.card-1=0`.  The adjacent positivity
and direction-law theorems correctly require `hzero`; this theorem must do the
same.  It is absent from `tmp/BlueprintWeak.lean`, so the validator did not even
typecheck its exact binder shape.

**Concrete fix.**  State

```lean
theorem groupedDirectionCount_le {F : Finset Plane} (hzero : 0 ∈ F) :
  groupedDirectionCount F ≤ F.card - 1
```

and add a separate unconditional bound `groupedDirectionCount F ≤ F.card` if
useful.  Update every consumer to pass the normalization proof explicitly.

### L27 (P1) — the validators do not faithfully validate the blueprint

**Risk.**  The comparator and resolution log use compilation as the acceptance
evidence, but the files compile altered, vacuous, or partial APIs.  False and
integration-invalid Markdown declarations therefore pass the gate.

**Location and evidence.**  `blueprint/COMPARATOR.md:129-149` says the
validators show that the corrected API elaborates, and
`blueprint/reviews/resolution-log.md:22` relies on eight signature validators.
In the reviewed files:

- `tmp/BlueprintCompletion.lean:43` defines
  `PairwiseIncommensurable _ := True`; this is a literal vacuous placeholder.
  Its `avoidanceVector` is the constant `![1,0]` at line 45, its dilation and
  weak bounds are unrelated toy formulas at lines 51 and 58, and its Euclidean
  diameter is zero at line 60.
- `tmp/BlueprintWeak.lean:45,58,60,123,130-131` similarly replace the
  avoidance vector, dilation modulus, rigidity period, scalar lattice, and
  Euclidean geometry.  Its `GroupedStructureDecomposition` at lines 92-99
  omits nearly all characteristic laws in the Markdown structure.
- `tmp/BlueprintAlgorithms.lean:11,17-18,20-21` replaces canonical direction
  count/directions and the weak bound with constants/toy formulas.  It imports
  the fake `BlueprintCompletion` namespace rather than the planned project
  modules.
- `tmp/BlueprintPolynomial.lean:78-85` introduces `localStechkinConstant` and
  `paperStechkinConstant`, which are absent from the corrected Markdown, and
  validates a theorem using the latter instead of the exported
  `stechkinNatConstant`.  It also redeclares the finite-difference API instead
  of importing the project adapter.
- The validators use separate namespaces such as
  `TranslationalTilingsBlueprintPolynomial`, so they cannot detect collisions
  in the intended `TranslationalTilings` namespace.  Most theorem "checks" are
  proposition-valued definitions, which establish only that an altered formula
  is a `Prop`, not that it is true.
- There is no `BlueprintMain.lean`.  Chapter 08 has 117 displayed declarations
  but its validator has no exact `_statement` wrappers (only two proved
  positivity theorems); Chapters 06 and 07 have only three and five wrappers
  respectively.  Counterexample has three.  Many public declarations in every
  layer are omitted.

Most importantly, none of `tmp/Blueprint*.lean` is listed in
`blueprint/SNAPSHOT.sha256`.  The evidence can change without changing the
identified snapshot.

**Concrete fix.**  Replace the isolated copies with a single integration
validator in the exact intended namespace and module dependency graph.  Lower
layers must be imported, never restubbed.  Paste every displayed public
definition verbatim and every exact theorem type with the same binders and
typeclasses; no `True`, toy body, or renamed formula is permitted.  A generated
declaration-name ledger should fail on omissions.  Add the validators and their
import graph to the snapshot hash.  Compilation remains an elaboration check,
not a truth check.

### L28 (P1) — duplicate declarations and inconsistent module ownership prevent integration

**Risk.**  Even after replacing every proof by a legitimate theorem body, the
proposed files cannot coexist under the public namespace.

**Location and evidence.**  Chapter 01 exports `backwardDiff` and
`backwardDiffIter` at `blueprint/01-foundations.md:215-220`.  Chapter 05
redeclares the same fully qualified names at
`blueprint/05-polynomial-rigidity.md:367-373`.  Chapter 06 then imports both
the structure path (which depends on `FiniteDifference`) and polynomial
rigidity.  The isolated validator namespaces hide the duplicate-name error.

The module table at `blueprint/README.md:24-31` owns declarations in
`.Difference`, `.Dilation`, and `.Structure`, whereas the chapters and imports
use `.FiniteDifference`, `.Dilation.Periodic`, and `.Structure.Grouped`
(`01:3-4`, `06:7-8`, `07:6-8`).  The actual dependency boundary and file
placement are therefore not frozen.

**Concrete fix.**  Put the generic backward adapter and Newton primitives in
one lower `TranslationalTilings.FiniteDifference` module.  Import that module
from polynomial rigidity and delete the Chapter 05 redeclarations.  Choose one
exact module path for every declaration, update the README/import blocks, and
make the integration validator follow that graph.

### L29 (P1) — the complete-exponential-sum prerequisite is still not recursively specified

**Risk.**  The largest new mathematics needed for Lemma 4.2 remains a research
program in prose.  A sorry-free implementation cannot start without changing
or inventing the blueprint's objects and intermediate theorems.

**Location and evidence.**  Chapter 05 now gives a precise final Weil-bound
statement at lines 535-542, but lines 547-557 merely list homogenization,
projective closure, an Artin--Schreier curve, Frobenius trace, a zeta numerator,
functional equation, divisor/intersection pairings, and a root bound.  None of
the curves, point counts, zeta data, trace maps, pairings, or intermediate
theorem signatures is written in Lean.  The claimed
`NumberTheory/PolynomialCongruence.lean` submodule at lines 559-564 has no API.

Likewise the prime-power proof at lines 566-594 describes proof-local branch
state, derivative valuations, splitting-field roots, a recurrence, and four
terminal cases without giving an exact state type, recurrence theorem,
termination measure, valuation lemmas, or branch-sum bound.  The validator only
checks the final propositions at `tmp/BlueprintPolynomial.lean:336-349`.
Pinned Mathlib supplies finite fields, polynomials, characters, Gauss sums, and
valuations, but no polynomial additive-character Weil bound or this
stationary-phase descent; Chapter 05 itself acknowledges the gap at lines
54-62.

**Concrete fix.**  Before proof work, add blueprint chapters (or complete
submodule sections) for the Artin--Schreier prime estimate and Chen
prime-power descent.  They must give every new data definition in Lean and the
exact intermediate theorem signatures in dependency order, including the
termination/branch invariant and the theorem that connects point count to the
character sum.  Then compile those exact signatures and obtain specialist
mathematical and Lean re-review.  A citation plus six prose bullets is not a
recursive formalization plan at this scale.

### L30 (P1) — arbitrary-generator HNF conversion is not formalized

**Risk.**  The algorithm does not accept the paper input format claimed by the
comparator, and the missing normalization/coset transport is itself a
substantial executable prerequisite.

**Location and evidence.**  `blueprint/08-algorithms.md:102-107` defines only
an already-normalized Hermite-form record `(a,0),(b,c)` with `a,c>0`.  Lines
186-189 explicitly say the public format starts *after* Hermite normalization.
No raw nonsingular generator-matrix code, quotient-bit encoding, normalization
algorithm, termination measure, or preservation theorem exists.  Nevertheless
`COMPARATOR.md:56` calls this an arbitrary finite-index period-lattice input,
and Chapter 08 lists Hermite reduction as an implementation prerequisite at
lines 778-786.

Pinned Mathlib does contain abstract, noncomputable Smith-normal-form data,
for example `Submodule.smithNormalFormOfLE` and `Submodule.smithNormalForm` at
`Mathlib/LinearAlgebra/FreeModule/PID.lean:519,538`.  Those are not an
executable two-dimensional HNF conversion and do not transport the input bit
table.

**Concrete fix.**  Either:

1. define an arbitrary-generator input type and an executable two-dimensional
   HNF routine, then prove determinant/nondegeneracy, generated-lattice
   equality, coset-code transport, decoded-set equality, termination, and the
   advertised cost; or
2. explicitly scope Theorem 6.2's machine input to pre-normalized HNF data and
   remove every claim that this is the paper's arbitrary-generator input.

The first option is required if the comparator is to remain as written.

### L31 (P2) — the cost trace is annotation-based and misses its own branch convention

**Risk.**  The Boolean decision functions are executable, but the stated cost
bound is not yet connected to a defined operational semantics.

**Location and evidence.**  Chapter 08 says one unit is charged for each
Boolean branch and residue/arithmetic operation at lines 193-198, yet
`planarTilePeriodCheckCounted` at lines 321-329 charges nothing for the
successful `if hM : 0 < M` branch.  More generally `PeriodicSetCode.memCounted`
and `LatticePeriodicSetCode.scalarEntryCounted` return a chosen numeral next to
an uninstrumented computation (`08:157-160,257-259`).  Thus their specification
theorems can be proved by reflexivity regardless of actual operations.

The HNF conversion is also lazy: `toScalarCode.bits` recomputes `C.memBool` on
each lookup, but downstream `PeriodicSetCode.memCounted` charges only `d+1`,
not the declared 12-unit HNF entry cost.  No eagerly materialized table or
conversion-aware decision path connects `latticeInputConversionCost` to
`nonOnePeriodicTilingDecisionLatticeInput`.

**Concrete fix.**  Either define this explicitly as an oracle-level symbolic
cost model and weaken the wording, or instrument primitive arithmetic/table
operations and prove first-projection correctness plus a recurrence for the
second projection.  Charge the `hM` branch consistently.  For lattice input,
materialize the scalar table once and charge it, or propagate the 12-unit
lookup through the decision procedure.

### L32 (P2) — public characteristic API, documentation, and Markdown structure remain incomplete

**Risk.**  The data structures are substantially improved, but clients still
lack stable extensionality/simplification interfaces and the resolution log
overstates what was repaired.

**Location and evidence.**  The resolution log at line 35 says characteristic
and extensionality APIs are listed in the owning chapters.  There is no `[ext]`
declaration or named structure extensionality theorem anywhere in Chapters
01--09.  Most public structures/definitions also have no Lean docstring plan.
`CirclePolynomial.FunctionConstant` and
`IntegralPolynomialPhase.HasExactDegree` (`05:88-89,173-179`) are not consumed
by any displayed theorem, so their intended role is not frozen.  Finally,
Chapter 05 has an unmatched Markdown fence: `end TranslationalTilings` at line
840 is followed by an unmatched fence at line 841.

**Concrete fix.**  Add exact extensionality and characteristic lemmas for
coefficient records, periodic codes, decompositions, and line selections;
mark the intended `[simp]` facts; document every paper-facing/public
declaration.  Consume or remove the two unused predicates.  Repair the fence
and correct the resolution-log claim.

## Recheck of original L1--L23 findings

| Original finding | Re-review status |
|---|---|
| L1 empty tile | Repaired: main level-one statements require nonempty input or separate the degenerate branches. |
| L2 one-dimensional period | Repaired: `universalPeriod1D` is the required product with `Finset.lcm`. |
| L3 slicing diagonal | Repaired: `slicingPairs` filters `wedge ≠ 0`; positivity is total. |
| L4 Euclidean norm | Repaired: `WithLp.toLp 2` is used and the exact product bound is stored directly. |
| L5 constant coefficient | Repaired: torsion/rationality and the common denominator quantify only positive indices. |
| L6 unconstrained component theorem | Repaired: `DirectionalTilingDecomposition` stores target periodicity and tiling. |
| L7 `dilate 0` | Repaired with `F.Nonempty` plus a total empty-case theorem. |
| L8 modulus-one congruence | Repaired with `Nat.ModEq`. |
| L9 imports | Direct Mathlib imports compile, but project module paths remain inconsistent (L28). |
| L10 elaboration defects | The displayed replacements are individually plausible/validator-tested. |
| L11 circle/separator definitions | The earlier undefined and ill-typed names were replaced; AddCircle shapes compile. |
| L12 literal completeness | Literal Markdown `...`, comment bodies, and undefined public names were removed, but recursive mathematical completeness remains blocked by L29--L30 and validator coverage by L27. |
| L13 polynomial recursion | **Unresolved** at the Weil/Artin--Schreier and prime-power levels (L29). |
| L14 finite differences | Mostly specified, but the bridge regressed to a false sign and is duplicated (L24, L28). |
| L15 quantitative data | Closed bounds and exact certificate fields are now present; symbolic cost semantics still need L31. |
| L16 direction-from-tile | Repaired with an explicit integer multiplier. |
| L17 executable finite data | Repaired in shape: `Fin` tables and the dependent `RepresentativeTupleCode` synthesize `DecidableEq`/`Fintype` in Lean 4.33.0. |
| L18 classifier specification | Definitions and theorem types are now substantially explicit, but the algorithm validator does not validate them and the HNF front end is absent (L27, L30). |
| L19 direct duplication of lcm/primorial | Repaired: root `primorial` and `Finset.lcm` are reused. |
| L20 Mathlib seams | Reuse map now names the pinned finite-difference, subgroup-index, WithLp, AddCircle, polynomial-content, character, and finite-Pi APIs. |
| L21 bundle design | Hard results are now paired with `Nonempty` existence theorems rather than merely assumed by consumers; extensionality/characteristic API remains incomplete (L32). |
| L22 paper API/comparator | Comparator is much more detailed, but its elaboration-evidence claim is false and Main has no validator (L27). |
| L23 placement/imports | **Unresolved**: exact module paths and ownership disagree, and duplicate declarations create a collision (L28). |

## Focused suitability ledger

### Boolean tables and dependent finiteness

The core type choices are suitable.  `BoxResidue d q := Fin d → Fin q` has an
unconditional finite instance, `PeriodicSetCode` stores a positive period, and
the Boolean-table count `2^(q^d)` has the expected edge behavior even at
`q=0`.  `RepresentativeTupleCode` at `08:465-470` successfully derives both
`DecidableEq` and `Fintype` under the pinned compiler.  Its payload is proof-free.
These shapes are approved, subject to exact integration validation and the
classifier proof obligations.

### Exact arithmetic certificates

`WeakArithmeticData` and `CompletionCertificate` now expose the claimed
`q,N,M,Q,Lambda,L` and `N_j,C_j,s_j,L_j,M` equalities/positivity/divisibility
facts.  Their hard fields are not vacuous assumptions in the final API because
`exists_weakArithmeticData` and `improve_weaklyPeriodic` must prove
`Nonempty` from the mathematical hypotheses.  Natural division is confined to
contexts where certificate fields prove the multiplication identity.  This
architecture is suitable.  L25 is a separate missing positivity hypothesis in
the complete-sum transport, not a defect in these bundles.

### AddCircle and Mathlib reuse

The `Torus := AddCircle (1 : ℝ)` representation, `fourier 1`,
`AddCircle.haarAddCircle`, rational/torsion API, metric-ball avoidance, and
real half-circle lifts all elaborate in the pinned environment.  The direct
imports exist.  Exact reusable seams include:

- `fwdDiff` at `Mathlib/Algebra/Group/ForwardDiff.lean:46`;
- `Finset.lcm` and its API in `Mathlib/Algebra/GCDMonoid/Finset.lean`;
- root `primorial` in `Mathlib/NumberTheory/Primorial.lean`;
- `AddSubgroup.index_range_nsmul` at `Mathlib/GroupTheory/IndexNSmul.lean:38`;
- `span_fourier_closure_eq_top` at
  `Mathlib/Analysis/Fourier/AddCircle.lean:245`;
- `Submodule.smithNormalForm` only as noncomputable abstract algebra, not as
  the missing executable HNF routine.

No further obvious direct Mathlib replacement was found for the project-local
Weil/Chen or classifier results.

### Placeholder and declaration ledger

The corrected Markdown has no literal declaration ellipsis, `sorry`, `admit`,
project `axiom`, or `opaque` declaration.  References to those words in trust
audit prose are not placeholders.  The validators do contain the vacuous
`PairwiseIncommensurable := True` described in L27.

Displayed declaration counts versus exact proposition-wrapper counts in the
current validators are:

| Chapter | Displayed declarations | Exact-style `_statement` wrappers |
|---|---:|---:|
| 01 Foundations | 51 | 22 |
| 02 Geometry | 59 | 14 |
| 03 Dilation/structure | 28 | 11 |
| 04 Counterexample | 25 | 3 |
| 05 Polynomial rigidity | 91 | 32 |
| 06 Weak periodicity | 60 | 3 |
| 07 Completion | 44 | 5 |
| 08 Algorithms | 117 | 0 |
| 09 Main | 28 | no validator |

The counts are not intended as proof-coverage percentages: validators also
repeat some definitions.  They demonstrate that the current evidence cannot
serve as a declaration-by-declaration ledger.

## Acceptance blockers

Approval requires, at minimum:

1. repair and regression-test L24--L26;
2. replace the validators as specified in L27 and hash them with the snapshot;
3. remove the duplicate declarations and freeze one exact import graph (L28);
4. recursively blueprint the Weil/Artin--Schreier and Chen developments (L29);
5. either implement/specify arbitrary-generator HNF conversion or narrow the
   comparator and public input claim (L30);
6. disposition L31--L32, then obtain independent mathematical and Lean
   approval of the same new snapshot.

Until those items are resolved, successful compilation of the current
validators must not be used to authorize Lean proof implementation.
