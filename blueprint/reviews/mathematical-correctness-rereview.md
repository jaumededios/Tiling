# Mathematical-correctness re-review of the corrected blueprint

## Snapshot and verdict

**Verdict: REJECT.**

This verdict applies only to the snapshot whose manifest is
`blueprint/SNAPSHOT.sha256` with SHA-256
`e428270de372f935f6f101fe873ecc40ee1463b45f2c113d112060ba2facd1fb`.
I ran `sha256sum -c blueprint/SNAPSHOT.sha256` immediately before writing this
report; every listed file matched.  A corrected snapshot must receive a fresh
review.  I did not use the first report's verdict as evidence.

I read every manifest-listed chapter, `README.md`, `COMPARATOR.md`, and
`reviews/resolution-log.md`, and compared the numbered statements and proposed
proof routes with `tmp/arxiv/structure_tilings.tex` (arXiv:2010.03254v3).  I
also checked the pinned Mathlib definition of `fwdDiff` and searched the pinned
library for the algebraic-curve prerequisites claimed by Chapter 5.

The corrected snapshot makes substantial progress.  In particular, the
paper's exact q--N--M--Q--L arithmetic in Chapter 6 and the
N--N_j--C_j--s_j--L_j--M completion arithmetic in Chapter 7 now agree at the
formula level.  Nevertheless, the snapshot contains four elementary false
public theorems, a false public cost theorem, an integrated declaration
collision, and several still-unexpanded recursive prerequisites.  Any one of
the P0 findings below blocks a sorry-free implementation.

## Blocking findings

### M19 (P0) — the backward/forward-difference adapter has the wrong sign

**Risk.** A displayed public theorem is false, and Chapters 5--7 say that their
Newton and elimination proofs reuse it.  Signature-only validation cannot
detect this.

**Location and evidence.** `01-foundations.md`, lines 244--246, states

```lean
backwardDiff h f = fun x ↦ -fwdDiff h f (x - h).
```

Pinned Mathlib defines `fwdDiff h f n = f (n+h)-f n` in
`Mathlib/Algebra/Group/ForwardDiff.lean`, line 46.  Consequently

```text
fwdDiff h f (x-h) = f x - f (x-h) = backwardDiff h f x,
```

with no minus sign.  For the concrete instance `G=R=ℤ`, `h=1`, and
`f(x)=x`, the blueprint's left side is `1` and its right side is `-1`.

**Concrete correction.** Rename the theorem to `backwardDiff_eq_fwdDiff` (or
keep the name only after renaming it accurately) and remove the unary minus:

```lean
theorem backwardDiff_eq_fwdDiff ... :
  backwardDiff h f = fun x ↦ fwdDiff h f (x - h)
```

Then audit every downstream rewrite for the sign convention.

### M20 (P0) — `commonDenominator_pos` is false without torsion hypotheses

**Risk.** The common-denominator API contains a false public theorem.  This is
a regression in the repaired denominator layer related to old M3.

**Location and evidence.** `05-polynomial-rigidity.md`, lines 100--105, defines
`commonDenominator` as the `Finset.lcm` of `addOrderOf` over positive-index
coefficients.  Lines 409--410 assert unconditionally

```lean
theorem commonDenominator_pos (P : CirclePolynomial d) :
  0 < P.commonDenominator.
```

For a degree-one polynomial whose linear coefficient has infinite additive
order in `AddCircle 1`, `addOrderOf` is zero.  The singleton lcm is then zero,
so the conclusion is false.  The prose at line 440 discusses only the empty
family and misses this case.

**Concrete correction.** Require
`hP : P.HasTorsionNonconstantCoeffs`, or state a precise equivalence describing
when the lcm is positive.  All downstream calls that arise from avoidance
already have the torsion hypothesis, so this repair need not weaken the paper
result.

### M21 (P0) — normalized repetition of a complete sum is false at `Q=0`

**Risk.** The exact denominator-transport bridge used in the claimed proof of
Lemma 4.3 is false on its stated domain.

**Location and evidence.** `05-polynomial-rigidity.md`, lines 432--437, assumes
`0<Q'`, `Q' ∣ Q`, and `P.PeriodicWith Q'`, but does not assume `0<Q`.
Divisibility permits `Q=0`.  Take the zero polynomial, `Q=0`, and `Q'=1`.
The left side is zero because inversion and the empty sum at zero both give
zero; the right side is the normalized one-term sum, equal to one.

**Concrete correction.** Add `hQ : 0 < Q`.  Equivalently, replace the bare
divisibility input by positive repetition data `Q = r*Q'` with `0<r`.  Record
the positivity chain at every call site.

### M22 (P0) — the unconditional canonical-direction count bound is false

**Risk.** A public theorem used to justify the finite direction type is false
for a singleton not containing zero.  This is exactly a singleton edge case.

**Location and evidence.** `06-weak-periodicity.md`, lines 35--39, counts
canonical directions in `F.erase 0`.  Lines 73--74 assert for every `F`

```lean
groupedDirectionCount F ≤ F.card - 1.
```

For `F={![1,0]}`, the left side is one and the right side is zero.

**Concrete correction.** Either state the unconditional sharp bound
`groupedDirectionCount F ≤ (F.erase 0).card`, or add `hzero : 0 ∈ F` to
the displayed theorem and derive the subtraction formula under that
hypothesis.  Keep an explicit regression for the nonzero singleton.

### M23 (P0) — the counted planar-search cost is false for the empty tile

**Risk.** `corollary_1_6` exports the false inequality, so the paper-facing
conjunction in `09-main-results.md`, lines 84--95, is false even though the
Boolean decision itself handles the empty tile correctly.

**Location and evidence.** The definitions are in `08-algorithms.md`, lines
240--249 and 321--344; the claimed inequality is at lines 361--362.  For
`F=∅`, the closed period cap is one.  At `M=1`:

1. the empty tile count costs `1`;
2. the target lookup costs `3` in dimension two;
3. the point check costs `5` and the one-point `countedAll` costs `7`;
4. generation costs `2` and there are two Boolean tables, so the inner
   `countedAny` costs `1 + 2*(7+2+1) = 21`;
5. the outer `countedAny` therefore costs `1+21+1 = 23`.

But `planarTileSearchCost ∅` is `22`: its summand charges the inner fold's
initializer but only one, rather than both, of the inner/outer combining costs.
Thus `planarTileDecisionCounted_cost ∅` is false.

**Concrete correction.** Increase each outer-period summand by one (so the
terminal `+1` becomes the two fold overheads), or change the counted-fold
initialization convention and rederive all trace lemmas.  Add an evaluated
empty-tile regression before re-exporting Corollary 1.6.

### M24 (P1) — the sharp Lemma 4.2 proof is still shifted into undeveloped algebraic geometry and stationary phase

**Risk.** The exact statement of paper Lemma 4.2 is now present, but the
blueprint still does not contain all mathematical content needed to prove it
without an axiom.  This keeps old M9 and M13 open at the proof-dependency level.

**Location and evidence.** `05-polynomial-rigidity.md`, lines 536--564, proposes
to prove the prime Weil bound by constructing an Artin--Schreier curve, its
zeta numerator and functional equation, a divisor/intersection pairing, and a
root bound.  Lines 568--620 compress the prime-power stationary-phase descent,
splitting-field valuation argument, four terminal cases, and the asserted
`chenLocalFactor` into prose.  `10-recursive-dependency-audit.md`, lines 36--38,
merely labels these as project prerequisites.  A search of the pinned Mathlib
tree found no algebraic-curve zeta, Riemann--Roch, divisor-intersection, or
Hasse--Weil API that supplies steps 3--5.

This is not just a matter of writing a long Lean proof from a complete
blueprint.  The blueprint has not defined the curve or its smooth projective
model, genus, divisors, zeta/L-function, Frobenius action, or the additive-
character eigenspace whose trace gives one selected character sum.  Counting
points on `Y^p-Y=f(X)` directly gives a sum over nontrivial additive
characters, not automatically the single character sum displayed at lines
536--542.  The required eigenspace argument is absent.  Likewise, the claimed
prime-power recurrence has no exact recursion, invariant, or proved local-
factor inequality that a formalizer could follow.

**Concrete correction.** Expand this into a separately reviewed prerequisite
blueprint.  It must state every definition and intermediate theorem for either
(a) a genuine Artin--Schreier L-function/eigenspace proof of the prime bound,
followed by an exact stationary-phase recursion, or (b) another published
route that really yields the uniform exponent `1-1/d`.  State the recursion,
termination measure, valuation invariants, all four terminal inequalities, and
the product bound giving `stechkinNatConstant`.  A six-step description of a
Weil-conjectures proof is not sufficient under the recursive-completeness
standard.

### M25 (P1) — Theorem 3.2 is dimension-generic, but its primitive grouping machinery is only planar

**Risk.** The paper-labelled Theorem 3.2 is stated for arbitrary `Z^d`, while a
necessary construction has not been defined or proved in that generality.
This leaves old M8 repaired at the output-field level but not at the proof
level.

**Location and evidence.** `03-dilation-structure.md`, lines 225--230, states
`exists_groupedStructureDecomposition` for arbitrary `d`.  Its proof at lines
265--269 says to write every vector as its integer content times one primitive
vector.  However `vectorContent`, `primitivePart`, and `IsPrimitive` in
`02-lattice-geometry.md`, lines 144--150, are defined only for `Plane` by taking
the gcd of two coordinates.  No dimension-generic content, primitive-part, or
common-direction theorem appears in Chapters 2, 3, or 10.

**Concrete correction.** Add the `Fin d` gcd/content construction and prove:
positive content for a nonzero vector, coordinate divisibility, primitive
decomposition, uniqueness up to the chosen orientation, common-multiple
construction for a commensurability class, and the coefficient-one l1 and
Euclidean product bounds.  Alternatively restrict the theorem to dimension
two, but that would no longer formalize paper Theorem 3.2.

### M26 (P1) — the advertised arbitrary-generator HNF input conversion is not implemented or specified

**Risk.** The HNF-to-scalar membership conversion is mathematically correct,
but the blueprint claims more than it supplies.  The missing step is explicitly
listed as a recursive prerequisite and is necessary to justify the comparator's
claim that the theorem accepts the paper's pair-of-generators input convention.

**Location and evidence.** `08-algorithms.md`, lines 102--107, starts from an
already normalized lattice generated by `(a,0)` and `(b,c)`.  The definitions
at lines 110--179 correctly encode that HNF lattice and prove scalar-lattice
inclusion and set preservation.  But lines 186--189 dismiss normalization of a
nonsingular arbitrary generator matrix as a “standard terminating Euclidean
algorithm”; there is no raw-generator input type, normalization function,
termination theorem, preservation of the subgroup/coset table, or total
conversion-cost theorem.  Nevertheless line 785 promises “Hermite-form
period-lattice reduction”, while `COMPARATOR.md`, lines 56 and 101, describes
the result as exact for the paper's general period-lattice input.

The function `scalarEntryCounted` is also only a constant-cost wrapper for one
entry.  There is no counted table-conversion fold whose cost is
`latticeInputConversionCost`, so the total-cost assertion at lines 181--184 is
not currently a theorem.

**Concrete correction.** Either (a) make normalized HNF code the explicitly
chosen public input encoding and remove every claim to convert arbitrary stored
generators, while proving that this encoding covers every finite-index planar
lattice, or (b) define a raw nonsingular two-generator code and an executable
HNF conversion, including unimodular transformation, subgroup and bit-table
preservation, termination, and counted cost.  The paper-facing comparator must
say exactly which option is formalized.

### M27 (P0) — Chapter 5 redeclares the Chapter 1 finite-difference constants

**Risk.** The planned module graph cannot be integrated: two modules declare
the same fully qualified constants in namespace `TranslationalTilings`.  The
separate signature validators avoid the conflict by using validator-specific
namespaces, so their successful elaboration is not evidence for integration.
This keeps old M18 open.

**Location and evidence.** `01-foundations.md`, lines 215--220, declares
`TranslationalTilings.backwardDiff` and `backwardDiffIter`.  Chapter 5 opens the
same namespace at line 72 and redeclares both names at lines 368--373.  Chapter
6 imports both the polynomial-rigidity and structure developments, so the two
declarations must coexist in one environment.

**Concrete correction.** Remove the Chapter 5 copies, import
`TranslationalTilings.FiniteDifference`, and use the Chapter 1 definitions.
Then compile a single import-all validator, not only isolated validators.

### M28 (P2) — the counterexample tile injectivity argument describes a false recovery step

**Risk.** The theorem that the tile has eight elements is true, but the written
proof route cannot be followed as stated.

**Location and evidence.** `04-counterexample.md`, lines 139--143, says that
the second coordinate modulo two recovers the third Boolean bit.  Every second
coordinate is `2*t₁-2*t₃`, hence is zero modulo two and recovers nothing.

**Concrete correction.** Use the first coordinate modulo two to recover `t₂`.
Then use `t₁-t₃ ∈ {-1,0,1}` from half the second coordinate; in the zero
case, subtract the known `t₂` from the first coordinate to distinguish
`t₁=t₃=0` from `t₁=t₃=1`.

### M29 (P1) — the Theorem 1.5 proof route omits the conversion from cosetwise data to a directional partition

**Risk.** Theorem 1.4 does not directly return the input structure consumed by
Theorem 5.3.  The omitted construction is also needed by the Section 6
classifier.  As written, the Chapter 7 proof route jumps across a type-level and
mathematical gap.

**Location and evidence.** Theorem 1.4 returns
`QuantitativeWeakPeriodData.ValidFor`, i.e. `CosetwisePeriodic`, at
`06-weak-periodicity.md`, lines 327--330 and 443--477.  Theorem 5.3 consumes a
`DirectionalTilingDecomposition` with global disjoint parts, their union, and
tiling fields at `07-periodic-completion.md`, lines 145--160 and 345--349.
Nevertheless lines 431--435 say that Theorem 1.4 “supplies a directional
decomposition” without defining the finite quotient-fiber assignment that
turns the per-coset existential direction into those parts.  The only displayed
constructor is later in `08-algorithms.md`, lines 686--694, in a module that
already imports periodic completion and therefore cannot discharge Chapter
7's dependency.

The one-direction branch is also only described in one sentence; no exact
certificate/bound theorem connects Corollary 5.2 to
`periodicTilingPeriodBound` in that branch.

**Concrete correction.** Move a reusable constructor below periodic
completion's dependency boundary.  It should choose a direction for each
finite quotient fiber, group fibers by that choice, and prove global
disjointness, union, directional periodicity, and preservation of the tiling.
State a one-part completion lemma with its exact multiplier and bound, then use
that lemma and Theorem 5.3 in the three empty/singleton/one-part/multi-part
branches of Theorem 1.5.

### M30 (P1) — the exported Theorem 5.3 bound is not the paper's printed `O_|F|` bound on its stated domain

**Risk.** The exact completion algebra is correct, but the comparator labels the
quantitative theorem exact/strengthened without exporting the printed
cardinality-only hidden constant.

**Location and evidence.** Paper Theorem 5.3 states

```text
M <<_|F| H^(m+r) diam(F)^(m*r),  r=|F|(|F|-1)/2.
```

The blueprint's `weakCompletionPeriodBound` at
`07-periodic-completion.md`, lines 189--195, contains
`completionLocalConstant(tileCard,numberOfParts)^numberOfParts`, hence an
additional explicit dependence on `m`.  `DirectionalTilingDecomposition` has
no `m ≤ |F|-1` field.  The proof itself chooses an avoidance vector of size
`O_m(1)` (lines 351--363), so the current proof route does not establish a
hidden constant depending only on `|F|` for arbitrary input decompositions.

This may reflect an implicit intended-use restriction in the paper: the
decomposition supplied by Theorem 1.4 has `m≤|F|-1`.  It is not one of the four
source typos recorded by the snapshot, and the blueprint must not silently
change the quantifiers.

**Concrete correction.** Export both statements honestly: a general
`m`-dependent completion theorem, and a paper-facing cardinality-only bound
under the structural hypothesis `m≤F.card-1`; or provide a new proof that
removes the `m`-dependent constant on the currently stated domain.  Update the
comparator to distinguish the source's implicit restriction if that is the
chosen resolution.

## Re-check of the original M1--M18 findings

The following statuses are based on this snapshot, not copied from the old
verdict.

| Old finding | Snapshot-specific result |
|---|---|
| M1 | **Resolved.** `F.Nonempty` is explicit in Theorem 1.3(i), and the empty-target behavior is discussed. |
| M2 | **Resolved.** `universalPeriod1D` is the product `q*n`, and the `{0,2}` regression distinguishes it from an lcm. |
| M3 | **Original issue resolved, denominator layer still blocked.** Rationality/torsion now excludes the constant coefficient, but M20 finds a new false unconditional positivity theorem. |
| M4 | **Resolved.** `slicingPairs` filters `wedge≠0`; empty/singleton lcms are one. |
| M5 | **Resolved.** `DirectionalTilingDecomposition` stores target periodicity and the tiling identity. |
| M6 | **Resolved.** `dilate_zero` assumes nonemptiness and the empty iff theorem covers the total definition. |
| M7 | **Resolved.** Dilation congruences use `Nat.ModEq`, including modulus one. |
| M8 | **Statement repaired, proof dependency incomplete.** The integer-multiple field is exact, but M25 identifies the missing arbitrary-dimensional primitive construction. |
| M9 | **Not resolved for implementation.** The exact exponent is stated, but M24 shows that the sharp theorem's recursive proof is still not blueprinted. |
| M10 | **Vacuity repaired, exported cost still false.** The exponent is now closed and cubic/quartic-bounded; M23 breaks the counted Corollary 1.6 at `F=∅`. |
| M11 | **Partially resolved.** Displayed APIs are far more complete, but M24, M26, and M29 remain major omitted prerequisites. |
| M12 | **Core finite enumeration resolved.** Tuple payloads are genuine finite Boolean data and the multiplier is tested positive.  The general-generator input claim remains M26. |
| M13 | **Not resolved.** Equidistribution and denominator transport are substantially improved, but the uniform sharp complete-sum proof remains the unexpanded M24. |
| M14 | **Formula-level resolved.** `CompletionCertificate` exposes `N_j,C_j,s_j,L_j,M` and both component/final clauses.  M30 remains a paper-facing hidden-constant mismatch. |
| M15 | **Resolved.** Metric balls and real half-circle lifts replace an ordered interval on `AddCircle`. |
| M16 | **Resolved.** Direct coefficient-one Euclidean individual and product bounds are stored. |
| M17 | **Resolved in the stated disjointness arguments.** Theorem 1.3, completion, classification, and assembly name nonempty tiles.  M23 is a different empty-input cost defect. |
| M18 | **Not resolved in the integrated module graph.** Isolated signatures elaborate, but M27 is a duplicate fully qualified declaration. |

## Numbered-paper-result audit

- **Theorem 1.3(i).** The nonempty-tile clarification is mathematically
  necessary and faithful to the paper's use of “tile”.  The scalar-period and
  singleton reductions are sound.  Its proposed implementation is still
  downstream of M19, M24, M25, and M27.
- **Theorem 1.3(ii) / Lemma 2.1.** The construction, cancellations, level-four
  convolution, and finite-difference obstruction match the paper.  Only the
  auxiliary injectivity prose in M28 is wrong.
- **Theorem 1.4.** The quantifier order is correct and genuinely stronger: the
  canonical directions, lattice, and multiplier can be chosen from `F,ell`
  before `E,A`.  The exact `q,N,M,Q,L` definitions, divisibility
  `ell | q`, identity `ell*L=Q*M^2*N*q`, lattice membership in both branches,
  relative-index exponent `2(c-1)^2`, and multiplier exponent `c(c-1)` check
  out.  M22 affects an overgeneral public helper, and M24/M25 block its proof.
- **Theorem 1.5.** The closed exponent
  `(c-1)(c^2+c-1)` is the sum of the weak exponent and the completion exponent;
  the displayed algebra is correct.  Empty target, empty tile under the
  existential premise, and singleton tile can be handled as described.  M29
  leaves the actual directional-partition and one-part branches underspecified.
- **Lemma 3.1 (all parts), Theorem 1.7, Corollary 3.3.** The corrected
  `Nat.ModEq`, oscillation factor two, nonempty dilation-zero case, and product
  universal period agree with the paper.  Theorem 3.2 alone retains M25.
- **Proposition 4.1.** The mod-one sum, degree `m-2` (with a separate `m=1`
  branch), and pair-supremum argument are faithful.  The shared finite-
  difference adapter must be corrected per M19/M27.
- **Lemmas 4.2 and 4.3.** Quantifier order and the printed exponent are now
  correct; the constant coefficient is properly excluded from rationality.
  M20--M21 invalidate two public denominator lemmas, and M24 remains the
  decisive recursive-proof blocker.
- **Proposition 4.4.** The two branches and exact advertised multiplier
  `Q*M^2*N*q*h_j` are sound.  The source's fixed-`b_i` typo is correctly changed
  to varying `b_j`.
- **Lemma 5.1 / Corollary 5.2.** Filtering nonzero wedges repairs the old zero-
  lcm problem.  The period `q*k*s`, slice-by-slice convolution equality, and
  primitive-line representative construction agree with the paper.
- **Theorem 5.3.** The exact identities
  `N_j=N*|eTilde∧h_j|`, `q_j=(ell*N_j)C_j`,
  `L_j=|eTilde∧h_j|C_j k_j s_j`, and `M=N*∏L_j` are correct.  The
  nonempty-tile disjointness proof is valid.  M30 concerns the remaining
  mismatch in the advertised hidden constant.
- **Corollary 1.6.** Boolean soundness/completeness and the finite candidate
  space are plausible, but the exported counted inequality is refuted by M23.
- **Theorem 6.2.** For an already normalized scalar or HNF target code, the
  finite tuple, finite-strip chameleon test, arbitrary line-selection
  classification, and two-chameleon/at-most-one dichotomy follow the paper's
  proof.  Empty target and singleton tile lead to the correct negative answer.
  M26 prevents the stronger claim that arbitrary stored generator data have
  been converted and costed.

## Paper typos versus blueprint errors

The four source errata listed in `README.md`, lines 56--65, are genuine and are
handled correctly:

1. Lemma 3.1(ii)'s proof needs coprimality, not `r=1 mod q`.
2. Theorem 3.2 is dimension-generic despite one `Z^2` prose slip.
3. Proposition 4.4 equation (23) needs indexed `b_j`.
4. Section 6 has harmless malformed affine-line notation.

The nonempty meaning of “tile” is a formalization clarification, not a paper
error.  Findings M19--M29 are blueprint errors or omissions, not paper typos.
M30 is best treated as an implicit-domain/source-proof issue that the
formalization must expose explicitly; it must not be silently added to the
errata ledger without resolving the quantifier mismatch.

## Final acceptance decision

**REJECT this snapshot.**  The minimum mathematical acceptance gate is:

1. correct M19--M23 and M27 and add executable counterexamples/regressions;
2. expand and independently review the complete-sum prerequisites in M24;
3. supply the arbitrary-dimensional grouping proof in M25;
4. resolve the exact input-domain claim in M26;
5. add the directional-partition/one-part completion bridge in M29; and
6. reconcile Theorem 5.3's printed `O_|F|` quantifiers as in M30.

After those changes, regenerate `SNAPSHOT.sha256` and re-review the new
snapshot.  The present report does not approve any later edits.
