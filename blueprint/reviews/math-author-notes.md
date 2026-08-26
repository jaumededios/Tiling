# Mathematical author notes for repairs owned by other chapters

These are implementation-ready handoffs produced after the mathematical
correctness re-review.  They are author notes, not an approval.  Chapters 5,
6, and 8 were deliberately not edited in this task because other agents own
them.

## 1. Chapter 5: shared finite differences and denominator positivity

`TranslationalTilings.FiniteDifference` in Chapter 1 is the unique owner of
`backwardDiff` and `backwardDiffIter`.  Remove the duplicate definitions at
`05-polynomial-rigidity.md`, lines 368--373, add the project import, and use the
correct adapter:

```lean
import TranslationalTilings.FiniteDifference

theorem backwardDiff_eq_fwdDiff {G R : Type*}
    [AddCommGroup G] [AddCommGroup R] (h : G) (f : G → R) :
  backwardDiff h f = fun x ↦ fwdDiff h f (x - h)
```

The common denominator is positive only when every positive-index coefficient
has finite additive order.  The corrected declaration is:

```lean
theorem commonDenominator_pos
    (P : CirclePolynomial d) (hP : P.HasTorsionNonconstantCoeffs) :
  0 < P.commonDenominator
```

The normalized repetition lemma must exclude `Q=0`:

```lean
theorem normalized_completeSum_repeat
    (P : CirclePolynomial d) (Q Q' : ℕ)
    (hQ : 0 < Q) (hQ' : 0 < Q') (hdiv : Q' ∣ Q)
    (hperiod : P.PeriodicWith Q') :
  (Q : ℂ)⁻¹ * completeSum P Q =
    (Q' : ℂ)⁻¹ * completeSum P Q'
```

Every rigidity call has `Q=P.commonDenominator`, so `hQ` is supplied by the
corrected positivity theorem after avoidance proves torsion.  Add regressions
for a nontorsion linear coefficient and for `P=0,Q=0,Q'=1`.

## 2. Chapters 2--3 / Chapter 6: arbitrary-dimensional primitive grouping

The dimension-generic Theorem 3.2 needs a dimension-generic content API.
Chapter 2 now generalizes the existing names rather than introducing a second,
parallel planar API:

```lean
def vectorContent {d : ℕ} (h : Lattice d) : ℕ :=
  (Finset.univ : Finset (Fin d)).gcd fun i ↦ Int.natAbs (h i)

def primitivePart {d : ℕ} (h : Lattice d) : Lattice d :=
  if h = 0 then 0 else fun i ↦ h i / (vectorContent h : ℤ)

def IsPrimitive {d : ℕ} (h : Lattice d) : Prop :=
  h ≠ 0 ∧ vectorContent h = 1

theorem vectorContent_pos {h : Lattice d} (hh : h ≠ 0) :
  0 < vectorContent h

theorem vectorContent_dvd_coord (h : Lattice d) (i : Fin d) :
  (vectorContent h : ℤ) ∣ h i

theorem primitive_decomposition {h : Lattice d} (hh : h ≠ 0) :
  (vectorContent h : ℤ) • primitivePart h = h ∧
    IsPrimitive (primitivePart h)

theorem primitive_decomposition_unique
    {h v : Lattice d} {k : ℕ} (hh : h ≠ 0) (hk : 0 < k)
    (hv : IsPrimitive v) (hdecomp : h = (k : ℤ) • v) :
  k = vectorContent h ∧ v = primitivePart h

theorem integer_multiple_of_primitive_of_commensurable
    {u v : Lattice d} (hu : u ≠ 0) (hv : IsPrimitive v)
    (huv : Commensurable u v) :
  ∃ z : ℤ, z ≠ 0 ∧ u = z • v
```

For grouping, the exact reusable class lemma should be:

```lean
theorem exists_commonMultiple_of_pairwise_commensurable
    {C : Finset (Lattice d)} (hC : C.Nonempty)
    (hne : ∀ f ∈ C, f ≠ 0)
    (hcomm : ∀ u ∈ C, ∀ v ∈ C, Commensurable u v) :
  ∃ h : Lattice d,
    h ≠ 0 ∧
    (∀ f ∈ C, ∃ z : ℤ, z ≠ 0 ∧ h = z • f) ∧
    l1Norm h ≤ ∏ f ∈ C, l1Norm f ∧
    euclideanNorm h ≤ ∏ f ∈ C, euclideanNorm f
```

Proof route: choose one `f₀∈C`, take its primitive part `v`, and use
commensurability plus primitive-coordinate gcd one to write every `f∈C` as
`z_f•v` with `z_f≠0`.  Let `L=lcm_f |z_f|` and `h=L•v`.  Then
`h=(L/z_f)•f`, with the sign of `z_f` retained in the integer quotient.  The
lcm is bounded by the product of the contents.  Since a nonzero primitive
integer vector has l1 and Euclidean norm at least one,

```text
||h|| = L ||v|| ≤ ∏_f (|z_f| ||v||) = ∏_f ||f||.
```

Apply the lemma to every commensurability class in Theorem 3.2.  Multiplying
the per-class inequalities gives both coefficient-one product bounds.

The planar canonical count declaration in Chapter 6 also needs one of these
two corrected shapes:

```lean
theorem groupedDirectionCount_le_erase (F : Finset Plane) :
  groupedDirectionCount F ≤ (F.erase 0).card

theorem groupedDirectionCount_le
    {F : Finset Plane} (hzero : 0 ∈ F) :
  groupedDirectionCount F ≤ F.card - 1
```

The nonzero-singleton regression `F={![1,0]}` must show why the old
unconditional subtraction statement is unavailable.

## 3. Chapter 8: canonical triangular/HNF input coverage

The algorithm owner selected checked `LatticePeriodicSetCode` as the public
wire format.  There is therefore no raw-generator conversion algorithm and no
conversion cost in the formal API.  To prove that this choice loses no
mathematical target covered by the paper, Chapter 8 should export the following
proof-side coverage result (now present under this name):

```lean
theorem exists_latticePeriodicSetCode_of_finite_quotient
    (Λ : AddSubgroup Plane) [Finite (Plane ⧸ Λ)]
    (E : Set Plane) (hE : SetPeriodicOn Λ E) :
  ∃ C : LatticePeriodicSetCode,
    C.periodLattice = Λ ∧ C.toSet = E
```

For its private HNF-basis lemma, put `q=Λ.index`.  Finiteness of the quotient
gives `q•e₀,q•e₁∈Λ`, so the sets of positive horizontal coordinates and
positive second coordinates occurring in `Λ` are nonempty.  Let `a` be the
least positive integer with `(a,0)∈Λ`, and let `c` be the least positive
second coordinate of a vector in `Λ`.  Choose `(b₀,c)∈Λ` and replace it by
`(b,c)=(b₀,c)-⌊b₀/a⌋(a,0)`, giving `0≤b<a`.  Euclidean division and the
minimalities of `c` and `a` show, successively, that every `(x,y)∈Λ` has
`c∣y` and that the remaining horizontal coordinate is divisible by `a`.
This proves equality with the displayed generated subgroup; the reverse
inclusion is immediate.

For the exported theorem, take this HNF basis and define the bit at `(i,j)` to be
membership of `![(i:ℤ),(j:ℤ)]` in `E`.  This construction is
noncomputable because `E` is an arbitrary mathematical set, but it is used only
to prove coverage, never by the Boolean classifier.  The HNF division formula
in `LatticePeriodicSetCode.memBool` writes every point as its box residue plus
an element of `Λ`; `hE` therefore proves `C.toSet=E`.

This resolves the input issue by choosing a normalized encoding, not by
claiming a raw pair-of-generators routine.  Chapter 9 should export only the
HNF-input theorem, and the comparator and dependency audit should contain no
raw-conversion or raw-conversion-cost claim.

## 4. Chapter 7 repairs completed by this author pass

Chapter 7 now states:

- the quotient-fiber conversion from `QuantitativeWeakPeriodData.ValidFor` to
  `DirectionalTilingDecomposition`;
- exact one-part completion data and its multiplier bound;
- certificate rebasing from base `ell*L₀` to `ell`;
- an honest general `m`-dependent Theorem 5.3 bound; and
- a structural `m≤|F|-1` bound whose hidden constant depends only on `|F|`.

These declarations are deliberately below Chapter 8 so the classifier can
reuse them without a dependency cycle.
