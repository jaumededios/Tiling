# Quantitative and algorithms audit

## Snapshot and scope

This is a read-only audit of the live, unversioned blueprint snapshot (the
workspace is not a Git repository).  I compared `blueprint/01`--`10` with
`tmp/arxiv/structure_tilings.tex`, concentrating on the arithmetic in Sections
4--6 and on whether the proposed Section 6 objects are genuinely executable.
The relevant source passages are Theorem 1.4 (TeX 259--271), Corollary 3.3
(534--538), Proposition 4.4 and its final calculation (636--703), Lemma 5.1
through Theorem 5.3 (720--801), and Theorem 6.2 (833--878).

Priorities use `P0` for a false/inconsistent specification, `P1` for a gap that
blocks the intended formalization, `P2` for a bounded but important API or
faithfulness repair, and `P3` for a low-impact improvement.

I applied an adversarial clean-room standard to every algorithmic claim: a
procedure counts only if it is a closed executable `Bool` over finite encoded
data; every enumeration must have proved completeness and soundness; all
bounds must be computable uniformly from the stated parameters; no existential
certificate may be smuggled in as an input; and a cost theorem must count the
displayed implementation under an explicitly defined model.  Classical
`Decidable` instances and finiteness-in-principle do not pass this standard.

## Findings

### Q1 (P0): `slicingLCM` is zero with the current commensurability definition

`02-lattice-geometry.md` defines `Commensurable u v` using *two nonzero*
integer coefficients.  Consequently `0` is not commensurable with a nonzero
`h`.  But `07-periodic-completion.md` defines `slicingLCM` by ranging over all
of `F × F`, including every diagonal pair `(f,f)`.  On such a pair the
difference is zero, the test reports it as incommensurable with `h`, and the
value inserted into the lcm is

```text
|h wedge (f-f)| = 0.
```

Since `Nat.lcm 1 0 = 0`, `slicingLCM_pos` is false for every nonempty `F`.
The advertised output period `q*k*s` then becomes zero and no longer supplies
a finite two-dimensional period.  This breaks Lemma 5.1, Corollary 5.2,
periodic completion, and every finite representative search.

Concrete fix: make commensurability mean integer linear dependence, allowing
one coefficient to be zero,

```lean
def Commensurable (u v : Lattice d) : Prop :=
  ∃ a b : ℤ, (a, b) ≠ (0, 0) ∧ a • u = b • v
```

or, more locally and more executably, define `slicingLCM` by filtering exactly
on `wedge h (f-f') ≠ 0`.  Use unordered off-diagonal pairs (or prove that
ordered duplicates do not matter), set the empty lcm to `1`, and prove every
inserted value positive before `slicingLCM_pos`.

### Q2 (P0): `universalPeriod1D` does not state Corollary 3.3 and is false in general

The paper's universal period is `q*n`, where `q` is the dilation modulus and
`n = lcm_{f≠0} |f|`.  `03-dilation-structure.md` instead defines

```lean
Nat.lcm q n
```

while `09-main-results.md` correctly prints `q * n`.  The structure proof only
shows that a common period is a multiple of every `q*f`, hence it supplies
`q*n`, not `lcm q n`.

This is not merely a weaker-proof issue.  Take `F={0,2}`, `ell=2`, and let
`A` be the integers congruent to `0` or `1` modulo `4`.  Then
`1_F * 1_A = 1`, so the convolution is `2 Z`-periodic.  Here `q=6` and `n=2`.
The proposed `lcm(q,n)=6` is not a period of `A`, whereas the paper's
`q*n=12` is.

Concrete fix: define `universalPeriod1D := q * n`, make the lower theorem and
the paper-facing declaration share that definition, and retain separate
lemmas `ell ∣ q`, `|f| ∣ n`, and therefore `q*|f| ∣ q*n`.

### Q3 (P0): the claimed exact quantitative/computable layer still consists of placeholders

The executable constants on which Sections 4--6 depend have no definitions:

- `rigidityPeriodBound` in `05-polynomial-rigidity.md`;
- `weakPeriodIndexBound` and `weakPeriodMultiplierBound` in
  `06-weak-periodicity.md`;
- `weakCompletionPeriodBound`, `periodicTilingPeriodBound`, and the referenced
  but undeclared `completionConvolutionBound` in
  `07-periodic-completion.md`;
- the central bodies and dependent types of `representativeTuples`,
  `equivalentLinePatternBool`, and the classification theorem in
  `08-algorithms.md`.

This contradicts the blueprint's own completion rule that every public
definition be written in Lean before implementation.  In particular,
`halfCirclePeriodBound`, hence `Q_m`, is not computable until the exact
rigidity formula and its proof are present.  The half-circle theorem is also
sketched using `Set.Icc` on `AddCircle`, which has no compatible global linear
order; the already chosen ball-avoidance formulation should be used instead.

Concrete fix: add definitions, not comments, for every bound and expand every
public signature.  Prefer executable arithmetic-data records containing the
actual `q`, `N`, `M`, `Q`, `Lambda`, and exact quotients together with
divisibility proofs.  Define the uniform bounds by majorizing those records.
Do the same for completion before any algorithm consumes a period cap.

### Q4 (P1): the Euclidean comparator changes two non-asymptotic clauses of Theorem 1.4

The paper states the coefficient-one bound

```text
||h_j||_2 <= diam_2(F)^(|F|-1)
```

and says that each `h_j` is an **integer multiple** of an element of
`F \ {0}`.  The machine theorem stores an `l1` bound, while
`theorem_1_4_euclidean` prints the coefficient-one Euclidean bound as though it
followed by norm equivalence.  Norm equivalence introduces a factor depending
on `|F|`; that factor can be absorbed in the index and `L` big-O bounds, but
not in this explicitly coefficient-one direction bound.  Both the grouped
structure field and the main theorem also weaken “integer multiple” to mere
`Commensurable`.

Concrete fix: on each commensurability class write `f=k_f v` with primitive
`v`, take `h=lcm(k_f)v`, and prove directly in both norms
`||h||_2 <= ∏_f ||f||_2` (use `||v||_2 >= 1`).  Store
`h = n • f` for a positive natural `n`, not just commensurability.  Norm
equivalence may still be used for the clauses whose constants are hidden.

### Q5 (P1): periodic completion lacks the exact multipliers needed by Section 6

Theorem 5.3's proof is described only through existential `N_j`/`M_j` and
cardinality-controlled constants.  That is enough for a qualitative theorem,
but not for `representativeTuples`, which must know a concrete full period for
each `A'_j`.

With the blueprint's avoidance vector and directions, one can make the source
calculation completely explicit.  For example, set

```text
N       = lcm_{i<j} |h_i wedge h_j|
r_j     = |e_tilde wedge h_j|
ell_j   = ell * N * r_j
q_j     = indicatorDilationModulus ell_j |F|
h_j     = k_j h'_j,  with h'_j primitive
s_j     = slicingLCM F h'_j
R_j     = q_j * k_j * s_j.
```

Then `1_F*1_{A_j}` is `ell_j Z^2`-periodic, and the replacement `A'_j`
is `R_j Z^2`-periodic.  Since `ell*N ∣ q_j`, the paper's quotient
`L_j = (q_j/(ell*N))*k_j*s_j` is exact and `R_j=ell*N*L_j`.
A common output period is `ell*N*lcm_j L_j` (bounded by the paper's
`ell*N*∏_j L_j`).

Concrete fix: export this data as a computable `CompletionData` structure and
make both Theorem 5.3 and Section 6 consume it.  Do not derive an enumerator
from a theorem that merely says some bounded `N_j` exists.

### Q6 (P0): `representativeTuples` is not a finite executable enumeration as typed

`PeriodicRepresentativeTuple` contains arbitrary natural numbers, arbitrary
period codes, and the proof field

```lean
convolution_sum : ∀ x : Plane, ...
```

The proposed `Finset (PeriodicRepresentativeTuple F E)` has no displayed
finite ambient type and cannot enumerate proofs of an infinite pointwise
statement.  Proof irrelevance can make equality of already constructed
certificates convenient; it does not manufacture the proofs needed to create
the candidates.  Moreover, the tuple redundantly searches `m`, directions,
line periods, and representative periods, although the paper first computes
all of these uniformly and searches only the periodic subsets.

Concrete fix: compute one fixed structural/completion datum `S(F,E.period)`.
Define a proof-free raw tuple

```lean
structure RawRepresentativeTuple (S : SearchData F E) where
  residues : (j : Fin S.m) -> Finset (Fin 2 -> ZMod (S.R j))
```

enumerate its finite product, and filter it with a Boolean finite-torus
equation.  Attach the `convolution_sum` theorem only after proving the Boolean
specification.  This yields exactly `∏_j 2^(R_j^2)` raw tuples and gives a
real completeness proof.

### Q7 (P1): the proposed line-pattern/chameleon checker has no correct finite domain yet

`linePatternCandidates k := Finset.univ.powerset` needs `0<k`; for `k=0`,
`ZMod k` is not the required finite cyclic pattern space.  Neither
`PrimitiveDirection` nor `PeriodicRepresentativeTuple` currently records
positivity of `linePeriod` or the equation `h_j=k_j h'_j`.

More importantly, a slice supported on one affine line is not doubly
periodic.  Its convolution equality cannot simply be checked “on a common
residue torus” without a proved no-aliasing construction.  For a representative
of scalar period `R_j`, primitive `h'_j` gives exactly `R_j` transverse line
classes.  For one class, equality of the reference slice and a `k_j`-periodic
candidate can be checked on:

- the finitely many transverse offsets occurring among translates by `F`;
- longitudinal residues modulo `lcm R_j k_j`.

Equivalently, an auxiliary transverse modulus larger than the tile width may
be used, but its no-wrap theorem must be stated.

Concrete fix: use the `SL(2,Z)` normalization (or a Bezout longitudinal and
wedge transverse coordinate), encode line classes by `ZMod R_j`, require
`0<k_j`, and define the exact finite strip checked by
`equivalentLinePatternBool`.  Prove its `= true iff` theorem before defining
`hasChameleonSlice`.

### Q8 (P1): the chameleon iff needs its coverage and edge hypotheses made explicit

The mathematical criterion in TeX 865--877 is sound in the nondegenerate
setting, but the blueprint currently states it without the conditions that
make the proof work.  It needs:

1. a coverage theorem that every tiling is `ProducedByTuple` for one of the
   finitely enumerated valid tuples;
2. `F.Nonempty` when level-one convolution is used to infer that all assembled
   parts (including two replacement slices) are disjoint;
3. the exact theorem that a nonzero sum of two nontrivial periodic functions
   supported on affine lines in incommensurable directions has no nonzero
   period;
4. multiplication of a hypothetical period by the scalar period of the
   periodic background before applying that support theorem;
5. explicit branches for `F.card=0`, `F.card=1`, and `E=∅` if the Lean API
   intentionally strengthens the paper by dropping its “`F` tiles `E`” input
   precondition.

For instance, if `F=∅` and `E=∅`, every set tiles `E`; non-one-periodic
tilings exist, but the `F\{0}` direction construction is empty.  This case
cannot pass through the advertised positive `m` classification.

Concrete fix: define `ProducedByTuple` fully, prove coverage and assembly in
separate directions, prove the support lemma, and make the final Boolean
theorem a short consequence.  Either restore the paper's tilability
hypothesis or implement and specify all degenerate branches.

### Q9 (P1): several “Boolean” definitions still leak classical or noncomputable choices

The intended executable path currently uses:

- `if Commensurable ...` rather than a decidable wedge test;
- quotient representatives/`Quot.out` in `slicePattern`;
- structures with `Set`-valued fields and infinite equality proofs;
- `encodePeriodicSet` on an arbitrary `Set` without a `DecidablePred`;
- an undeclared `ComputablePred` wrapper instead of a displayed Boolean
  program/specification pair.

Using `Classical.propDecidable` can make these expressions elaborate, but it
does not make them executable in the sense demanded by the blueprint.

Concrete fix: keep `encodePeriodicSet` explicitly `noncomputable` or add a
decidable-membership argument, and keep it out of algorithms.  In executable
code use coordinates, `ZMod`, Boolean wedge equality, proof-free residue
arrays/bitvectors, and Boolean filters.  Every Boolean must have a local
`b = true iff P` theorem; the final decidability theorem should be derived
from `nonOnePeriodicTilingDecision` directly.

### Q10 (P1): the operation-count theorem does not count the displayed Lean algorithm

`periodicCandidateCheckCost n M = n*M^2` matches the paper only if candidate
membership is an O(1) lookup in a Boolean table and loop/comparison overhead is
absorbed.  The proposed candidate is a `Finset`; its evaluator membership is
not constant time.  Constructing and traversing `Finset.powerset`, lifting
codes to lcm periods, residue reductions, and even the `M^2` loop when
`n=0` are absent from the exact cost.  Thus the undefined
`ImplementsWithinArithmeticOps` statement cannot hold for the code as shown.

Concrete fix: separate the mathematical `Finset` specification from a
costed implementation over `Array Bool`/bitvectors indexed by the finite
torus.  Define the small-step or recurrence cost semantics first.  A safe
per-candidate cost has the form `(c0+c1*n)*M^2+c2`, plus an explicit candidate
generation cost.  Then prove the exact sum bound and only afterwards simplify
it to, for positive card-dependent functions,

```text
C1(n) * 2^(C2(n) * D^(C3(n) * n^4)).
```

This is a clearer natural-number counterpart of the paper's exponential than
the currently unexplained `Nat.exp`.  State separately that the model charges
unit cost for integer arithmetic, exactly as the paper does; it is not a claim
about Lean evaluator wall-clock time.

### Q11 (P2): the scalar-period input format is acceptable, but its relation to the paper input is missing

`PeriodicSetCode` represents a scalar-periodic target, whereas the paper's
input format stores generators for an arbitrary finite-index period lattice
and occupied cosets.  Every such input can be converted computably to a scalar
period (for example using the lattice index/determinant), so this is not a
mathematical loss.  The conversion and its size/cost are not in the blueprint.

Concrete fix: add a finite-lattice periodic-set input code and a verified
conversion to `PeriodicSetCode`, or say explicitly that Theorem 6.2 is stated
for an equivalent normalized input format and give the computable conversion
theorem.  Keep the Section 4/5 data quantified before `E,A`: the blueprint's
stronger dependence only on `F` and the chosen scalar `ell` is supported by
the source proof and is a good API decision.

### Q12 (P2): the core `q,N,M,L` choices are faithful, but the exact divisibility API must be frozen

Apart from the failures above, the Section 4 choices match the TeX:

| Quantity | Required exact definition/fact |
|---|---|
| `q` | `lcm ell (product of primes <= 2|F|)`; `ell ∣ q` and `q/ell <= productSmallPrimes` |
| `N` | lcm of positive `|h_i wedge h_j|`, `i<j`; `N Z^2 <= <h_i,h_j>` |
| `M` | lcm of positive `|e_tilde wedge h_j|`; each denominator divides `M` |
| `Lambda` | `<q*N*e_tilde, q*N*M*h_1>`; contained in `ell Z^2` |
| `Q_m` | lcm of `1..halfCirclePeriodBound(m-2)`, hence divisible by every returned rigidity period |
| `L` | `(Q_m*M^2*N*q)/ell`, with exactness supplied by `ell ∣ q` |

The two coset-rigidity branches also need named membership proofs:
`M^2*N*q*h_j ∈ Lambda` in the supremum-one branch and
`Q_m*M*N*q*h_1 ∈ Lambda` in the rigidity branch; multiplying gives the
common advertised `Q_m*M^2*N*q*h_j`.  The `m=1` case must branch before any
off-diagonal lcm or `m-2` rigidity degree is used.

Concrete fix: make these exact definitions and divisibility lemmas public in
one arithmetic-data record.  The bound functions and comparator should be
derived from that record, so Section 6 cannot accidentally enumerate a period
that is only bounded existentially.

## Rubric summary

- **Mathematical intent:** not clear (`Q1`, `Q2`, `Q4`, `Q8`).
- **Reusable seams:** the proposed exact arithmetic-data and periodic-code
  seams are good, but completion/search data are not yet realized (`Q5`,
  `Q6`).
- **Public API/theorem shape:** not clear because integer-multiple and
  Euclidean clauses were weakened or changed (`Q4`).
- **Module/dependency direction:** clear; algorithms are correctly downstream
  of structure and completion.
- **Mathlib integration:** no quantitative finding beyond the need to avoid a
  nonexistent order on `AddCircle` and to keep classical set encoders out of
  executable code (`Q3`, `Q9`).
- **Proof architecture:** not clear at the completion/classification boundary
  (`Q5`--`Q8`).
- **Cost and durability:** not clear (`Q9`, `Q10`).
- **Refactor risk:** low now because no Lean files exist; repair the blueprint
  before declarations freeze the wrong interfaces.

## Verdict

**Reject the blueprint for implementation in its current state.**  The
Section 4 `q,N,M,L` spine is recognizable and mostly faithful, and the
quantifier order correctly captures independence from the tiling `A`.
However, `Q1` and `Q2` are concrete false specifications, while `Q3`, `Q6`,
and `Q10` mean the advertised computable algorithms and operation bound do not
yet exist even at blueprint level.

Minimum re-review gate: resolve `Q1`--`Q10`, replace every quantitative and
algorithmic ellipsis by elaboratable Lean, provide the exact completion/search
records, and prove the finite Boolean specifications.  `Q11`--`Q12` should be
closed before the comparator is frozen.
