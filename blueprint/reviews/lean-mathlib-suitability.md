# Lean 4 / Mathlib suitability review

## Snapshot, standard, and verdict

This is an independent, read-only Tau-Ceti-style review of the unversioned
blueprint snapshot in `/home/codex/Documents/Codex/2026-08-24/usi` on
2026-08-24.  The directory is not a Git repository and contains no Lean source
files or Lake project.  I inspected every displayed declaration in
`blueprint/01-foundations.md` through `blueprint/10-recursive-dependency-audit.md`,
the README, and the review protocol in `blueprint/11-refereeing-standard.md`.
I also checked the proposed interfaces against the pinned Mathlib checkout at

```text
/home/codex/Documents/Codex/2026-08-14/Tiling/.lake/packages/mathlib
```

whose commit is `db584cd6d46c92f209a44c0f1c829460d327499d`
(`master-2026-08-10`, the supplied Lean/Mathlib 4.33-era snapshot).

**Verdict: BLOCK.  This snapshot is not suitable as the frozen specification
for a Lean implementation.**  It contains false exported statements, invalid
imports, declarations which demonstrably do not elaborate, 61 literal `...`
occurrences (including incomplete declaration signatures and bodies), undefined public names, noncomputable objects
presented as executable algorithms, direct duplication of pinned Mathlib APIs,
and public bundles which omit or hide their characteristic laws.  Lean work
must not start from these signatures.  Resolve every P0/P1 below, record P2/P3
dispositions, generate a signature-only Lean file, and independently re-review
the *entire corrected snapshot*.  This verdict does not carry over to a later
snapshot.

Priorities are: P0 = invalidates a claimed mathematical result or the
specification; P1 = blocks elaboration or a sorry-free implementation; P2 =
material API/reuse/maintenance defect; P3 = localized polish.

## Findings

### L1 (P0) — the main level-one theorem is false for the empty tile

**Risk.**  The advertised main result admits a direct counterexample, so the
paper-facing API is unsound even before considering its proof.

**Location and evidence.**  `blueprint/09-main-results.md:36-40` states
`theorem_1_3_i` without `F.Nonempty`, while the theorem it proposes to call,
`level_one_plane_weaklyPeriodic` at `blueprint/06-weak-periodicity.md:198-200`,
does require nonemptiness.  With `F = ∅` and `E = ∅`, `Tiles F A E` holds for
every `A`, and `E` is scalar-periodic.  Taking any non-weakly-periodic `A`
(including the intended counterexample set) refutes the conclusion.  The
README's claim that the empty case is handled does not repair the statement.

**Concrete fix.**  Add `(hF : F.Nonempty)` to the exact paper-facing theorem
and pass it to the lower theorem, or replace all bare `Finset` tile parameters
by a documented nonempty finite-tile structure.  Add the empty-tile example as
a regression theorem and correct the faithfulness note.

### L2 (P0) — `universalPeriod1D` uses an invalid period

**Risk.**  The lower Corollary 3.3 theorem is false and internally disagrees
with the paper-facing statement.

**Location and evidence.**  `blueprint/03-dilation-structure.md:203-205`
defines the period as `Nat.lcm q n`; `blueprint/09-main-results.md:135-142`
correctly prints the paper's product `q * n`.  The proof only supplies a
multiple of every `q * |f|`, namely `q * lcm_f |f|`; `lcm q n` need not have
this property.  For `F = {0,2}` and the period-four set of residues `{0,1}`,
`tileConv F 1_A` is constant, `q = 6`, and `n = 2`.  The blueprint's period is
6, which is not a period of `A`; 12 is.

**Concrete fix.**  Define

```lean
def universalPeriod1D (ell : ℕ) (F : Finset ℤ) : ℕ :=
  indicatorDilationModulus ell F.card *
    (F.erase 0).lcm Int.natAbs
```

and prove the required divisibilities.  Make the lower theorem and comparator
refer to this single definition.

### L3 (P0) — diagonal pairs force `slicingLCM` to be zero

**Risk.**  The purported positive slicing period is always zero for a
nonempty tile, making the periodicity conclusion vacuous and breaking Lemma
5.1, Corollary 5.2, completion, and every downstream finite search.

**Location and evidence.**  `Commensurable` at
`blueprint/02-lattice-geometry.md:127-130` requires both integer multipliers to
be nonzero.  Consequently `Commensurable 0 h` is false for nonzero `h`.
`slicingLCM` at `blueprint/07-periodic-completion.md:59-62` ranges over all of
`F ×ˢ F`, including `(f,f)`, and inserts
`Int.natAbs (wedge h (f-f)) = 0`.  Mathlib's lcm with zero is zero, contradicting
`slicingLCM_pos` at line 83.

**Concrete fix.**  Filter by the exact determinant condition instead of the
current relation:

```lean
def slicingLCM (F : Finset Plane) (h : Plane) : ℕ :=
  ((F ×ˢ F).filter fun ff => wedge h (ff.1 - ff.2) ≠ 0).lcm
    (fun ff => Int.natAbs (wedge h (ff.1 - ff.2)))
```

or use off-diagonal unordered pairs.  State the divisibility theorem under a
nonzero-wedge hypothesis and prove positivity before any use.  If
`Commensurable` remains, document that it deliberately excludes zero and do
not use it as linear dependence.

### L4 (P0) — `euclideanNorm` is the supremum norm, not the Euclidean norm

**Risk.**  The exact Euclidean comparator and a displayed norm inequality are
false under the proposed definition.

**Location and evidence.**  `blueprint/02-lattice-geometry.md:66-67` defines
`euclideanNorm x := ‖fun i => (x i : ℝ)‖`.  The ordinary Pi norm is the sup
norm.  The imported pinned file explicitly defines Euclidean space as
`PiLp 2` at `Mathlib/Analysis/InnerProductSpace/PiL2.lean:113`.  Thus
`l1Norm_le_sqrt_dim_mul_euclideanNorm` fails already for the all-ones vector in
dimension four: it asserts `4 ≤ 2`.

**Concrete fix.**  Use an explicit `PiLp 2` value, for example

```lean
noncomputable def euclideanNorm (x : Lattice d) : ℝ :=
  ‖(WithLp.toLp 2 (fun i : Fin d => (x i : ℝ)) : EuclideanSpace ℝ (Fin d))‖
```

and restate every comparator theorem against that definition.  Separately
prove the coefficient-one Euclidean direction-product estimate; generic norm
equivalence cannot supply that exact clause.

### L5 (P0) — circle-polynomial rationality includes the constant coefficient

**Risk.**  The avoidance theorem and the denominator-annihilation theorem are
false.  This invalidates the rigidity pipeline.

**Location and evidence.**  `CirclePolynomial.IsRational` at
`blueprint/05-polynomial-rigidity.md:58-60` quantifies over every coefficient,
while the paper only constrains nonconstant coefficients.
`rational_coefficients_of_avoidsBall` at lines 168-170 is refuted by a
constant polynomial at a nontorsion circle point avoiding a disjoint ball.
Likewise `coeff_zsmul_commonDenominator` at lines 182-185 cannot annihilate an
arbitrary constant coefficient.  The expression
`(q : ℝ) • (1 : Torus)` is also not a rational-point embedding: `AddCircle 1`
has neither the required real scalar action nor this intended `1`.

**Concrete fix.**  Use finite additive order as the working predicate and
restrict it to positive indices:

```lean
def CirclePolynomial.HasTorsionNonconstantCoeffs
    (P : CirclePolynomial d) : Prop :=
  ∀ i : Fin (d + 1), 0 < (i : ℕ) → IsOfFinAddOrder (P.coeff i)

def CirclePolynomial.HasRationalNonconstantCoeffs
    (P : CirclePolynomial d) : Prop :=
  ∀ i : Fin (d + 1), 0 < (i : ℕ) →
    ∃ q : ℚ, P.coeff i = ((q : ℝ) : Torus)
```

Restrict the denominator and its annihilation lemma to nonconstant
coefficients, and explicitly show that the constant cancels from
`P (n+Q) - P n`.  Reuse the pinned
`AddCircle.addOrderOf_coe_rat` and
`AddCircle.isOfFinAddOrder_iff_exists_rat_eq_div` at
`Topology/Instances/AddCircle/Defs.lean:608,658`.

### L6 (P0) — `convolution_part_scalarPeriodic` has no hypotheses which make it true

**Risk.**  The completion module exports an arbitrary periodicity conclusion
from a mere partition certificate.

**Location and evidence.**  The prose at
`blueprint/07-periodic-completion.md:189-192` says the bundle freezes a target
tiling equation.  Its actual definition at lines 154-166 contains no `Tiles`
field and no target-periodicity field; indeed `E` is a phantom parameter.
Nevertheless `convolution_part_scalarPeriodic` at lines 197-204 has neither
`Tiles F A E` nor `SetScalarPeriodic ell E`.  A horizontal-periodic half-plane
as one part and an empty second part satisfies the displayed partition data,
but convolution with `{0}` is not scalar-periodic.

**Concrete fix.**  Prefer a pure decomposition structure independent of
`F,E`, and add exact hypotheses `(hE : SetScalarPeriodic ell E)` and
`(htile : Tiles F A E)` to the theorem.  Alternatively add those laws as
fields and remove redundant theorem hypotheses downstream.  Define the
currently undeclared `completionConvolutionBound` before stating the result.

### L7 (P0) — `dilate_zero` is false on an allowed input

**Risk.**  A basic public normalization theorem is false.

**Location and evidence.**  `blueprint/03-dilation-structure.md:83` states
`dilate 0 F = {0}`.  By the definition at lines 56-57, `dilate 0 ∅ = ∅`.

**Concrete fix.**  State
`dilate_zero (hF : F.Nonempty) : dilate 0 F = {0}` and add the exact empty
case, or state an `if F.Nonempty then {0} else ∅` formula.

### L8 (P1) — remainder equality makes the dilation theorem vacuous modulo one

**Risk.**  The API does not faithfully express congruence and loses valid
degenerate cases.

**Location and evidence.**  The hypotheses at
`blueprint/03-dilation-structure.md:121,130` use `r % modulus = 1`.  When the
modulus is one, the left side is zero for every `r`, although every `r` is
congruent to one modulo one.

**Concrete fix.**  Use
`Nat.ModEq (dilationModulus ...) r 1` and the analogous indicator statement.
Only derive a remainder form under a proved `1 < modulus` hypothesis.

### L9 (P1) — the import lists do not exist against the pinned checkout

**Risk.**  The proposed modules fail before declaration elaboration, and a
critical Weyl prerequisite is incorrectly presented as if supplied by
Mathlib.

**Location and evidence.**  Direct filesystem checks of the pinned source
gave the following results.

| Blueprint import | Result | Exact replacement/action |
|---|---:|---|
| `Mathlib.Data.Nat.Prime.Finset` (02:7) | missing | `Mathlib.NumberTheory.Primorial`, or `PrimeCounting` only if its API is actually used |
| `Mathlib.Topology.Algebra.Order.Compact` (03:8) | missing | `Mathlib.Topology.Order.Compact` |
| `Mathlib.Data.Real.Irrational` (04:6) | missing | `Mathlib.NumberTheory.Real.Irrational` |
| `Mathlib.Data.Real.Sqrt` (04:7) | deprecated route | `Mathlib.Analysis.Real.Sqrt` |
| `Mathlib.NumberTheory.WeylCriterion` (05:8) | missing | remove; formalize the exact criterion/prerequisites named in L13 |
| `Mathlib.Data.Rat.Den` (05:10) | missing | `Mathlib.Data.Rat.Lemmas` |
| `Mathlib.Tactic.NativeDecide` (08:8) | missing | remove; import `Mathlib.Computability.RE` for the computability API |

The declarations also require direct imports not currently listed:
`Mathlib.Algebra.GCDMonoid.FinsetLemmas`,
`Mathlib.Algebra.Group.ForwardDiff`, `Mathlib.Data.Fintype.Pi`,
`Mathlib.Data.Finset.SymmDiff` (plus `open scoped symmDiff`),
`Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar`,
`Mathlib.GroupTheory.IndexNSmul`, and `Mathlib.Computability.RE`.

**Concrete fix.**  Replace the import blocks now and validate each proposed
module with an import-only Lean file.  A nonexistent conditional “search
target” is not an import and the Weyl development must be added to the
recursive dependency graph.

### L10 (P1) — several closed-looking foundation/arithmetic declarations do not elaborate

**Risk.**  These are not proof holes; their terms or assumptions are rejected
by Lean 4.33.

**Location and evidence.**  Minimal pinned-toolchain probes established:

- `tileIndicator` (`01:53-54`) is declared computable but uses the
  noncomputable `Finsupp` additive instance through `Finset.sum`.
- `PeriodicOn` (`01:72-74`) assumes only `[Add G]`, while `AddSubgroup G`
  requires additive group structure.
- `finsetLCM := s.fold Nat.lcm 1` (`02:49`) has the wrong `Finset.fold`
  application and does not elaborate.
- `avoidanceVector` (`02:146-151`) invokes a nonexistent `Finset.find`; the
  displayed `.choose` is applied to the range rather than a witness and
  cannot return a `Plane`.
- `folnerBox` (`03:64-66`) uses `Finset.univ.pi`, whose result is a dependent
  membership-indexed function, not `Fin d → ℤ`.
- `rayAverage` (`03:68-72`) calls the noncomputable `setIndicator` in a plain
  `def`.
- the Frobenius theorem (`03:88-91`) casts a `ℤ`-valued `Finsupp` directly to
  `AddMonoidAlgebra (ZMod p) ...`; no such coercion exists.
- `alpha := Real.sqrt 2` and `carry` (`04:73-80`) require a noncomputable
  section.
- `CirclePolynomial.eval`, `IsConstant`, and `IsRational` (`05:49-60`) leave
  `i` untyped.  Because `(i : ℕ)` occurs first, elaboration infers `i : ℕ`,
  then fails against `coeff : Fin (d+1) → Torus`.
- `Set.Icc (0 : Torus) (1/2 : Torus)` (`05:273`) is ill-typed: `AddCircle`
  has no intended linear order or these arithmetic operations.
- `convolutionEquivalent` (`07:92-94`) omits the `[AddCommGroup G]` instance
  required by `tileConv`.
- `tileSlice` (`07:52-54`) filters using membership in an arbitrary
  `AddSubgroup` without a computable `DecidablePred`; it cannot be a plain
  executable `def` as presented.

**Concrete fix.**  In order: mark `tileIndicator` noncomputable or construct
it with `Finsupp.onFinset`; require `[AddGroup G]`; delete the lcm wrapper or
use `s.lcm id`; define `avoidanceVector` as the least element of a proved
nonempty filtered range and return `![1,t]`; use
`Fintype.piFinset`; mark analytic/set-based definitions noncomputable; define
a coefficient-generic `tileIndicatorR` or apply
`AddMonoidAlgebra.mapRingHom`; type every binder explicitly; represent the
half-circle as the quotient image/lift of the real interval or use a ball;
add the missing group instance.

### L11 (P1) — circle-polynomial and separator APIs remain ill-typed or undefined

**Risk.**  The central rigidity module cannot be translated without changing
its public mathematical interface.

**Location and evidence.**  Beyond L5/L10:

- `nonconstantDenominators` (`05:62-65`) ends with `...`; pinned
  `Finset.filterMap` at `Data/Finset/Image.lean:596` requires an injectivity
  proof, so this is not a harmless omitted tactic.
- `circlePhase` (`05:73-74`) needs the direct `CircleAddChar` import and a
  noncomputable section.
- `TrigSeparator` (`05:241-249`) stores an arbitrary `eval` function plus an
  equality proof instead of defining evaluation from `coeff`, and references
  the undefined `separatorCoefficientBound`.
- the proposed `fejerSeparator` is analytic/noncomputable despite the claim
  that it is an executable object.
- the rigidity proof refers to undefined `P.smul k`; the relevant operation
  should be an exact `zsmul`/`k • P` definition.
- `complete_exponential_sum_paper_form` (`05:288-290`) uses a natural `Q` with
  a real exponent without casting and has an incomplete binder list.
- the counterexample formula (`04:128-158`) knowingly equates a rational
  indicator expression with a real expression.

**Concrete fix.**  Replace `filterMap` by a positive-index filter followed by
`Finset.lcm`; make `CirclePolynomial` and `TrigSeparator` have computed
evaluation methods and add extensionality based on coefficients; define
`CirclePolynomial.zsmul`, separator degree and coefficient bound with exact
closed formulas; mark analytic constructions noncomputable while keeping only
their numerical bounds executable; insert every cast in the real-valued
counterexample theorem.  Freeze these exact corrected declarations in an
elaboration-only file before proof work.

### L12 (P1) — the blueprint is not definition- or signature-complete

**Risk.**  Quantifier order, dependencies, typeclasses, and the hardest proof
obligations are hidden precisely where the user required literal Lean.  A
later “implementation correction” could silently change the mathematics.

**Location and evidence.**  There are literal declaration ellipses throughout
01, 02, 05, 06, 07, 08, and 09.  The complete ledger is in Appendix A.  Named
but nowhere defined public dependencies include `polynomialSeq`,
`separatorCoefficientBound`, `completionConvolutionBound`,
`ImplementsWithinArithmeticOps`, `PeriodicSetCode.univ`, `AllowedPatterns`,
`assembleLinePatterns`, `referencePattern`, `decodeLinePattern`,
`referenceSlice`, and `ProducedByTuple`.  Comment-only bodies are used for
`rigidityPeriodBound`, all quantitative weak/completion bounds, all finite
enumerations and Boolean classifiers.  `eliminate_periodic_summands` even has
an unbound `lhs` in its conclusion (`01:220-229`).

**Concrete fix.**  Replace every ellipsis and comment-body with literal Lean;
give every public theorem its complete binders and conclusion; define every
public name before first use.  In particular, state the exact composite
finite-difference operator in `eliminate_periodic_summands`, not just its
intended outcome, and replace the undefined `polynomialSeq` with a precise
Newton/monomial representation.  No declaration in Appendix A may remain
schematic at the acceptance gate.

### L13 (P1) — the polynomial-rigidity recursion is not recursively decomposed

**Risk.**  Mathlib does not contain the claimed Weyl module, while the
blueprint omits the substantive proofs needed for Lemmas 4.2/4.3 and shifts a
strictly weaker or vacuous result under a paper number.

**Location and evidence.**  `05:145-177` leaves van der Corput and the
non-leading-nontorsion case implicit.  `05:203-236` gives no checked recurrence
for the claimed complete-sum power saving, including denominator collapse and
constant-difference cases.  `05:277-283` omits the denominator of `kP`, the
repeat-average lemma, and the branch in which `kP` is constant.
`05:285-303` replaces the paper's `Q^(1-1/d)` Lemma 4.2 by
`Q^(1-1/2^d)` while `09:149-150` aliases it as `lemma_4_2`; its sketched
`∃ C` occurs after the individual polynomial and is therefore vacuous as a
uniform big-O statement.  Coefficientwise nonconstancy also need not imply
that the induced circle-valued function is nonconstant (integer-valued
polynomial identities modulo one are a counterexample pattern).

**Concrete fix.**  Add exact reusable declarations for residue-class Cesaro
averages, leading-nontorsion van der Corput, removal of higher torsion
coefficients, complete cyclic correlations, denominator/gcd behavior of
differences and integer characters, repeated period averages, and the
resulting recursion.  Either formalize the paper's exact Stechkin exponent
with `∃ C, ∀ P Q, ...`, or stop claiming Lemma 4.2/full-paper coverage and
give the weaker theorem a different name.  State nonconstancy in the exact
primitive phase data needed by the bound.

### L14 (P1) — the finite-difference core is replaced by an undefined predicate and ellipsis

**Risk.**  Proposition 4.1 and the periodic-completion differentiation step
cannot be proved through the proposed foundation API.

**Location and evidence.**  `iteratedDifference_eq_zero_iff_polynomialSeq`
(`01:211`) references no definition of `polynomialSeq`.
`bounded_real_of_iteratedDifference_eq_zero_is_constant` (`01:218`) has no
signature.  `eliminate_periodic_summands` (`01:220-229`) does not specify the
directions, operator, indices, or left-hand side.  The consumers
`linePhi_sum_mod_one`, `linePhi_circlePolynomial`, pair-supremum, and coset
rigidity at `06:157-196` all hide their hypotheses behind `...`.

**Concrete fix.**  Reuse and adapt pinned
`Mathlib/Algebra/Group/ForwardDiff.lean:46` (`fwdDiff`) and its iteration and
Gregory--Newton lemmas.  Define the blueprint's backward difference as an
explicit translate/sign adapter and prove characteristic simp lemmas.  State
an exact Newton-series or `CirclePolynomial` conversion theorem.  For
elimination, explicitly define the list of differences
`e - b_i • period_i`, the fold/composition over all unwanted summands, and
the equality on each target summand.  Then write every Proposition 4.1/4.4
consumer without ellipses.

### L15 (P1) — the quantitative data are not exact and some advertised bounds are vacuous

**Risk.**  Sections 4--6 cannot feed an executable search, and the displayed
asymptotic theorem does not express a degree-four exponent.

**Location and evidence.**  `groupedTileDirections`,
`weakPeriodIndexBound`, and `weakPeriodMultiplierBound` at `06:97-112`, and
`weakCompletionPeriodBound`/`periodicTilingPeriodBound` at `07:168-176`, have
comment bodies.  `completionConvolutionBound` is undeclared.  The exact
divisibility behind `(Q_m*M^2*N*q)/ell` and the `m=1` branch are not frozen.
`periodicTilingPeriodBound_polynomial` (`07:220-223`) permits
`exponent card ≤ C card * card^4`; because `C` itself depends arbitrarily on
`card`, this is no `O(card^4)` restriction.  The same defect propagates to the
main comparator's `C₃ : ℕ → ℕ`.

**Concrete fix.**  Introduce a concrete arithmetic record containing exact
`q,N,M,Q_m,Λ,L`, divisibility proofs, and the two coset-period membership
facts.  Add a completion record containing every `k_j`, primitive `h'_j`,
slice lcm, `q_j`, `L_j`, and actual output period; derive closed majorants from
those records.  State the polynomial exponent using one global natural
constant (or, preferably, the explicit polynomial), e.g.
`∃ c_exp, ∀ n, exponent n ≤ c_exp * n^4`.  Handle diameter zero with explicit
branches or `max 1 diameter`.

### L16 (P1) — Theorems 3.2/1.4 weaken integer-multiple data to commensurability

**Risk.**  The public certificate omits proof-relevant integer data promised
by the paper, and later slicing algorithms need those multipliers.

**Location and evidence.**  `GroupedStructureDecomposition.direction_from_tile`
(`03:184-185`) and `QuantitativeWeakPeriodData.direction_from_tile`
(`06:122-125`) say only `Commensurable (direction j) f`.
The paper-facing declarations at `09:60-62,83-86` repeat the weaker condition.
Commensurability allows `f` to be a multiple of the direction rather than the
direction being the stated integer multiple of a tile vector.

**Concrete fix.**  Store an explicit multiplier with the orientation used by
the paper:

```lean
direction_from_tile : ∀ j,
  ∃ f ∈ F, f ≠ 0 ∧ ∃ z : ℤ, direction j = z • f
```

or a positive natural multiplier after choosing signs.  Use it directly in
the primitive-direction and line-period data.

### L17 (P1) — the algorithm layer is not executable as typed

**Risk.**  The claimed decision procedures, computability theorem, and finite
enumeration cannot be compiled or evaluated, even with proof holes filled.

**Location and evidence.**  In `blueprint/08-algorithms.md`:

- `PeriodicSetCode` (`08:26-30`) has a dependent `ZMod period` field but no
  usable derived/canonical `DecidableEq`, `Encodable`, or `Primcodable` plan.
- a proof `period_pos` does not install the `[NeZero period]` instance required
  for `Fintype (Fin d → ZMod period)`.
- `encodePeriodicSet` (`08:38-41`) takes an arbitrary `Set` with no
  `DecidablePred`; it cannot be an executable encoder.
- `periodicCandidates` and both Boolean bodies (`08:49-58`) are comments.
- `PeriodicRepresentativeTuple.linePeriod` (`08:151`) may be zero;
  `linePatternCandidates 0` (`08:162-163`) attempts `Finset.univ` over
  `ZMod 0`, which is not the intended finite cyclic type.
- `representativeTuples` (`08:178-182`) purports to enumerate structures with
  unbounded naturals, arbitrary directions and residue sets, and an infinite
  pointwise proof field.  Proof irrelevance does not manufacture such proofs
  or a finite ambient type.
- quotient choice in the proposed slice API and arbitrary `Set` fields leak
  classical noncomputability into the Boolean path.
- `Nat.exp` (`08:113`, `09:111`) is not the intended Lean operation; use
  natural exponentiation or an explicitly cast real exponential.

**Concrete fix.**  Use positive periods (`ℕ+` or a local installed `NeZero`),
proof-free raw records over a fixed finite `SearchData`, canonical arrays or
bitvectors indexed by residue vectors, and Boolean filters whose `= true ↔`
specifications are proved separately.  Make arbitrary-set encoding explicitly
noncomputable and keep it outside the algorithm, or accept decidable
membership.  Enumerate only bounded positive periods/directions, then attach
proof certificates after filtering.  Define `ComputablePred` against pinned
`Mathlib.Computability.RE` and provide an actual `Primcodable` encoding.

### L18 (P1) — the chameleon classifier has no domain, assembly, coverage, or cost semantics

**Risk.**  Theorem 6.2 and the advertised operation bound are currently names
for omitted mathematics rather than algorithms.

**Location and evidence.**  `lineClass : ...`, the Boolean bodies, and
`representativeTuples` are incomplete at `08:165-182`.
`AllowedPatterns`, `assembleLinePatterns`, `ProducedByTuple`,
`referencePattern`, `referenceSlice`, and `decodeLinePattern` used at
`08:200-224` are undefined.  No finite-strip/no-aliasing theorem relates a
line convolution to a residue-torus check.  No coverage theorem shows that
every tiling is produced by a listed tuple.  `ImplementsWithinArithmeticOps`
at `08:108,117` is only prose, and the cost treats membership in a `Finset` as
constant-time while ignoring candidate generation, lifting, and reductions.

**Concrete fix.**  Define primitive longitudinal/transverse coordinates,
the exact finite line-class type, positive line periods, a proof-free pattern
assignment, assembly/decoding, and the finite strip checked.  Prove Boolean
soundness/completeness, tuple enumeration coverage, the two-chameleon support
lemma, and all empty/singleton branches.  For complexity, separate the
mathematical `Finset` specification from an array/bitvector implementation,
define the small-step or recurrence cost semantics first, and prove it counts
the displayed program.

### L19 (P1) — two project helpers directly duplicate pinned Mathlib APIs

**Risk.**  This violates the user's “as much Mathlib as possible” requirement
and creates incompatible parallel lemmas at a central arithmetic seam.

**Location and evidence.**  `finsetLCM` (`02:49`) duplicates
`Finset.lcm`, defined at
`Mathlib/Algebra/GCDMonoid/Finset.lean:48`, with
`Finset.dvd_lcm`, `Finset.lcm_dvd`, and `Finset.lcm_eq_zero_iff` at lines
61-110; `Finset.lcm_dvd_prod` is already at
`Algebra/GCDMonoid/FinsetLemmas.lean:28`.  `smallPrimeProduct` (`02:45-46`)
is exactly `Nat.primorial`, defined at
`Mathlib/NumberTheory/Primorial.lean:40`, with positivity and divisibility APIs
at lines 56-66 and `Nat.Prime.dvd_primorial_iff` at line 93.

**Concrete fix.**  Delete both wrappers and use `(s.lcm id)` and
`Nat.primorial` directly.  If paper-facing notation genuinely improves
readability, use reducible abbreviations and do not recreate Mathlib theorem
families.

### L20 (P2) — several other substantial Mathlib seams are missed

**Risk.**  The proposed proof graph needlessly rebuilds difficult generic
machinery or cites a less direct theorem, increasing proof and maintenance
risk.

**Location and evidence.**  Exact pinned candidates are:

- scalar-lattice index: `AddSubgroup.index_range_nsmul` at
  `Mathlib/GroupTheory/IndexNSmul.lean:38`; the determinant theorem mentioned
  in 02 requires explicit bases (`CardQuotient.lean:98,106`) and is not the
  direct result;
- finite differences: `fwdDiff` and its iterates/Newton results at
  `Mathlib/Algebra/Group/ForwardDiff.lean:46ff`;
- Cramer: `Matrix.mulVec_cramer` at
  `Mathlib/LinearAlgebra/Matrix/Adjugate.lean:284`;
- finite function enumeration: `Fintype.piFinset` at
  `Mathlib/Data/Fintype/Pi.lean:32`;
- AddCircle Fourier density:
  `span_fourier_closure_eq_top` at
  `Mathlib/Analysis/Fourier/AddCircle.lean:245`;
- rational/torsion and density on AddCircle:
  `Defs.lean:608,658` and
  `Topology/Instances/AddCircle/DenseSubgroup.lean:55`;
- the counterexample's irrationality:
  `irrational_sqrt_two` at
  `Mathlib/NumberTheory/Real/Irrational.lean:145`;
- coefficient change for monoid algebra:
  `AddMonoidAlgebra.mapRingHom` at
  `Mathlib/Algebra/MonoidAlgebra/MapDomain.lean:322`.

**Concrete fix.**  Revise the dependency audit to name these exact
declarations and the thin adapters required by the project's signs/types.
Only prove project-local mathematics after a compile-tested attempt to use
these APIs.

### L21 (P2) — public bundled data are overconstrained in some places and unconstrained in others

**Risk.**  Hard obligations can be smuggled into constructors, while arbitrary
fields obscure characteristic equality and prevent robust extensionality or
finite enumeration.

**Location and evidence.**  `StructureDecomposition.isRayAverageClusterPoint`
(`03:160-162`) is a proof-irrelevant `Prop` field unused downstream; it burdens
every public constructor without characterizing the public object clients use.
Conversely, `groupedTileDirections` (`06:97-102`) returns only a sigma of
`m` and directions and contains none of the claimed coverage,
nonzeroness, pairwise, multiplier, or bound laws.  `TrigSeparator.eval`
(`05:245`) is arbitrary data constrained later by a proof field.
`DirectionalTilingDecomposition` has phantom `F,E` and omits their characteristic
tiling laws (L6).  `PeriodicRepresentativeTuple.convolution_sum` (`08:156-159`)
hides the central infinite correctness obligation in a proof field of an
object which is then claimed enumerable.

**Concrete fix.**  Split private construction certificates from minimal public
results.  Derive evaluation from coefficients.  Replace the sigma by a named
certificate containing all exact laws or return `QuantitativeWeakPeriodData`
directly.  Keep raw finite-search records proof-free; attach soundness after a
Boolean check.  Add `[ext]` lemmas for coefficient/residue/part data and
characteristic membership/evaluation lemmas before downstream use.

### L22 (P2) — the paper-facing aliases, documentation, and comparator are not a stable public API

**Risk.**  Duplicate theorem names add no mathematical interface and can drift
from the canonical results; consumers lack documented normalization and
characteristic lemmas.

**Location and evidence.**  `09-main-results.md` proposes aliases such as
`theorem lemma_3_1 := dilation_prime` and `theorem theorem_5_3 := ...` while
claiming they “expand to full types.”  They do not freeze a new type and many
targets are incomplete or inequivalent (L2, L13).  Most proposed public
declarations in 01-08 have no Lean docstring plan.  `CardControlledLE`
(`09:25-26`) is unused.  There is no exact, generated comparator object/table
which records assumption-by-assumption bridges, despite the user's request to
build one before proof work.

**Concrete fix.**  Prefer one canonical theorem per fact with a docstring
naming the paper number; use aliases only if their exact, explicitly written
type is intentionally a supported API.  Delete unused `CardControlledLE`.
Add membership/evaluation/simp lemmas for `addCoset`, indicators, codes,
slices, and decompositions, and extensionality lemmas for all public data.
Generate the comparator from exact checked declarations, with columns for
paper hypotheses, Lean hypotheses, norm convention, constant dependence,
edge cases, and bridge theorem.  Re-review it before any proof begins.

### L23 (P3) — module placement and import discipline need a final pass after signatures stabilize

**Risk.**  The current target-module list will accumulate broad imports and
paper-specific facts in foundational modules, making dependency direction and
linting brittle.

**Location and evidence.**  `Basic` proposes metric imports but its exact
foundational definitions need none; arithmetic, geometry, analytic
equidistribution, and computability imports are not yet isolated by actual
Lean dependencies.  Generic bounded-difference and AddCircle polynomial facts
are currently mixed with tiling-specific consumers.  The project has no Lean
files, so no import or placement claim has been validated.

**Concrete fix.**  After the corrected signature-only build, split generic
finite-difference, AddCircle-polynomial, lattice arithmetic, and executable
coding modules below the tiling modules.  Use `#min_imports`/import minimization
and the project linter.  This is not a request for speculative abstraction;
move only declarations with at least two consumers or a genuinely generic
statement.

## Appendix A — exhaustive literal-placeholder and missing-definition gate

Every item below violates the blueprint rule that displayed public
definitions and signatures be literal Lean.  Line numbers refer to this
snapshot.

| File | Incomplete declaration/signature |
|---|---|
| 01 | `tileConv_apply` 126; `tileConv_zero/add/sub/smul` 129-132; `tileConv_translate` 134; `tileConv_indicator_eq_card` 137; `tilesAtLevel_iff_representation_count` 141; `scalarPeriodic_iff_periodicOn` 148; `setScalarPeriodic_iff_membership` 151; `finiteIndex_periodic_scalarPeriodic` 154; `tiles_translate_tile` 166 |
| 01 | `difference_add`, `difference_comm`, `difference_tileConv` 196-198; `lineRestriction_difference` 208; `iteratedDifference_eq_zero_iff_polynomialSeq` 211; `bounded_real_of_iteratedDifference_eq_zero_is_constant` 218; `eliminate_periodic_summands` 220-229 (including unbound `lhs`) |
| 02 | `l1Norm_nonneg` 103; `diameter_norm_equivalence` 114; `avoidanceVector` 146-151; `primitive_decomposition_unique` 201; `lcm_wedges_bound` 219-221 (also an unbound/unspecified bound parameter) |
| 05 | `nonconstantDenominators` 62-65; `rigidityPeriodBound` 103-106; `vanDerCorput_cesaro` 145-148; `complete_exponential_sum_paper_form` 288-290; `polynomials_only_fail_to_equidistribute_when_periodic` 293-295 |
| 06 | `groupedTileDirections` 97-102; `weakPeriodIndexBound` 103-106; `weakPeriodMultiplierBound` 109-112; `linePhi_sum_mod_one` 157-159; `linePhi_circlePolynomial` 161-165; `linePhi_pair_sup_le_one` 167-170; `coset_indicator_periodic_one_of_grouped` 172-178; `theorem_1_4_euclidean` 188-196 |
| 07 | `slicingLCM` 59-62; `slicePattern` 64-66; `tileSlice_eq_empty_iff` 81; `tileSlice_translate` 82; `weakCompletionPeriodBound` 168-171; `periodicTilingPeriodBound` 173-176; `quantitative_periodic_tiling_euclidean` 225-230 |
| 08 | `encodePeriodicSet` 38-41; `tilesPeriodicTargetBool` 49-53; `periodicCandidates` 55-58; `encodePeriodicSet_toSet` 69; `planarTileDecision` 87-90; `equivalentLinePatternBool` 165-170; `hasChameleonSlice` 172-176; `representativeTuples` 178-182; `tiling_iff_from_periodic_representatives` 198-206; `hasChameleonSlice_eq_true_iff` 208-214 |
| 09 | `theorem_1_3_i` proof body 40; the lower results to which paper aliases point remain schematic as listed above |

Undefined names which must become exact declarations, not prose:

```text
polynomialSeq
separatorCoefficientBound
CirclePolynomial.smul / zsmul
completionConvolutionBound
PeriodicSetCode.univ
ImplementsWithinArithmeticOps
AllowedPatterns
assembleLinePatterns
referencePattern
referenceSlice
decodeLinePattern
ProducedByTuple
```

## Appendix B — displayed-declaration elaboration coverage

This table records the result of checking every displayed declaration family.
“Plausible” means only that its *shape* can be made to elaborate after the
named import/noncomputability fixes; it is not proof approval.

| Blueprint file | Declaration families | Result in this snapshot |
|---|---|---|
| 01 Foundations | `Lattice`, `Plane`, `Line`, `setIndicator`, `tileConv`, tiling predicates, scalar/set periodicity, `addCoset`, weak/one/cosetwise periodicity | Shapes plausible; `tileIndicator` and `PeriodicOn` fail (L10); most public characteristic lemmas are schematic (L12); finite-difference core blocked (L14) |
| 02 Lattice geometry | dilation modulus, norms/diameters, wedge, commensurability, generated/scalar lattices, primitive vectors | `finsetLCM` fails and duplicates Mathlib; prime product duplicates Mathlib; Euclidean norm false; avoidance vector and several public theorems incomplete; scalar index should use `index_range_nsmul` |
| 03 Dilation/structure | `dilate`, bounds, Følner/ray objects, structure bundles, grouped bundle, universal period | `folnerBox`, `rayAverage`, Frobenius cast fail; `dilate_zero` and universal period are false; congruence is vacuous at modulus one; structures otherwise shape-plausible after noncomputability/import fixes |
| 04 Counterexample | tile, irrational slope, carry, Boolean-cube set, cancellation vectors | Concrete finite tile shape plausible; analytic definitions require `noncomputable section`; displayed indicator identity has a rational/real type mismatch; exact irrational/density imports must change |
| 05 Polynomial rigidity | circle polynomial, evaluation, torsion/denominator, equidistribution, sums, separator, rigidity | Central predicates/signatures are false or ill-typed (L5, L10-L13); imports missing; most proof-critical definitions are placeholders |
| 06 Weak periodicity | rigidity lcm, direction/bound data, quantitative certificate, `linePhi` | Certificate shape is plausible but direction law is too weak; all construction/bounds and every Proposition 4.1/4.4 bridge are incomplete |
| 07 Completion | direction subgroup, slicing, slice/equivalence, directional/periodic certificates | `slicingLCM` is zero; slice representation is incomplete and representative-dependent; `convolutionEquivalent` misses an instance; directional bundle/theorem is unconstrained; all bounds incomplete |
| 08 Algorithms | periodic codes, torus convolution, periodic search, planar decision/cost, representative/chameleon classification | `torusTileConv` is plausible with installed `NeZero`; all surrounding encodings/enumerations/classifiers are incomplete or noncomputable as typed (L17-L18) |
| 09 Main results | paper aliases and Euclidean/complexity comparators | Main level-one theorem false; Corollary 3.3 conflicts with lower definition; Lemma 4.2 alias is not faithful; every alias inherits lower blockers; exact comparator has not been frozen |

## Appendix C — acceptance checklist for the corrected snapshot

The next review should receive, at minimum:

1. an import-only and signature-only Lean build against the exact pinned
   commit, with no `sorry`, `admit`, `...`, synthetic placeholders, or
   undefined names;
2. repaired empty/singleton/zero-period cases and regression examples for L1,
   L2, L3, L7, and L8;
3. exact nonconstant-torsion polynomial APIs, the full recursively decomposed
   analytic/number-theoretic chain, and either the actual paper Lemma 4.2 or a
   corrected scope claim;
4. closed computable quantitative functions and proof-free finite search data,
   followed by Boolean specification theorems and a defined cost semantics;
5. a Mathlib-reuse ledger naming the exact pinned declarations in L19-L20;
6. characteristic `[simp]`/membership/evaluation lemmas, extensionality
   principles, docstrings, and the exact paper-to-Lean comparator;
7. two independent approvals of the same corrected snapshot, as required by
   `blueprint/11-refereeing-standard.md`.

Until then, successful elaboration of isolated fragments would not be evidence
that the blueprint says the paper's mathematics.
