# Quantitative and algorithms re-review

## Snapshot and verdict

This is a snapshot-specific re-review of the specification pinned by
`blueprint/SNAPSHOT.sha256`.  `sha256sum -c blueprint/SNAPSHOT.sha256` succeeds
for every listed file.  The SHA-256 digest of the manifest itself is

```text
e428270de372f935f6f101fe873ecc40ee1463b45f2c113d112060ba2facd1fb
```

**Verdict: REJECT.**  The mathematical quantitative formulas and the finite
classification/search spaces have been repaired convincingly, but the public
counted-cost theorem in Chapter 8 is false for this snapshot.  In addition,
candidate-generation and HNF-conversion costs are asserted by manually added
numbers rather than obtained from counted executable definitions.  Those are
clean-room algorithm blockers: the final formalization could not prove the
advertised operation-count interface without changing the specification.

The verdict concerns the pinned snapshot only.  It is not a rejection of the
mathematical classification or decidability construction.

## Scope and audit standard

I checked Chapters 2--10, the comparator, the resolution log, and the public
API against the exact `q,N,M,Q,L` and `N_j,C_j,s_j,L_j,M` formulas, all closed
exponents, finite Boolean-table encodings, `Finset.fold` counting conventions,
candidate and tuple enumeration, strip/chameleon completeness, line selection,
normalization, triangular/HNF lattice conversion, and degenerate inputs.  Under
the Tau Ceti clean-room standard, a decision procedure counts as executable
only when its data and search are finite and computational; a classical
`Decidable` instance, a hidden existential witness, or a proof-only encoding
does not suffice.  A cost theorem must count the displayed executable program,
not an informal surrogate.

## Blocking findings

### RQ1 — P0: `planarTileDecisionCounted_cost` is false by one operation per tested period

**Risk.**  This is a false public theorem statement, so the Chapter 8 algorithm
cannot be formalized sorry-free as specified.

**Location and evidence.**  In `blueprint/08-algorithms.md:240-249`,
`countedAny` is defined by

```lean
s.fold countedOr (false, 1) p
```

with `countedOr x y := (x.1 || y.1, x.2 + y.2 + 1)`.  Consequently

```text
cost (countedAny s p) = 1 + sum x in s, (cost (p x) + 1).
```

For a fixed period, `planarTilePeriodCheckCounted` supplies callback cost
`checkCost + generationCost`, hence its cost is

```text
1 + 2^(M^2) * (checkCost + generationCost + 1).
```

The outer `countedAny` then adds both its own initial `1` and another `+1` for
combining each period result.  Its exact cost is therefore

```text
1 + sum M in Icc 1 B,
  (2^(M^2) * (generationCost + checkCost + 1) + 2).
```

But `planarTileSearchCost` at `blueprint/08-algorithms.md:339-345` has only
`+1` at the end of each summand; the false public theorem is at lines 361--362.

There is a small explicit counterexample.  Let `F = ∅`.  The current cap gives
`B = 1`; for `M = 1` there are two candidates.  With the Chapter 8 definitions,
`q = 1`, `d = 2`, `generationCost = 2`, and the periodic-candidate check costs
`7`.  Thus the inner fold costs `1 + 2 * (7 + 2 + 1) = 21`, and the outer fold
costs `1 + 21 + 1 = 23`.  The stated `planarTileSearchCost` evaluates to `22`.

**Concrete repair.**  Replace the terminal `+1` in every per-period summand of
`planarTileSearchCost` by `+2`, prove the exact two-level fold identity first,
and then redo the closed upper bound from that corrected identity.  Add the
empty-tile, `B=1` calculation as a Lean regression example.

### RQ2 — P1: candidate-generation cost is not the cost of an executable counted generator

**Risk.**  Even after RQ1 is fixed, the operation count does not yet certify the
displayed search.  A manually added number can hide enumeration, allocation,
or decoding work, so the claimed complexity theorem is not implementation
honest.

**Location and evidence.**  At `blueprint/08-algorithms.md:61-67`, candidates
are presented extensionally as `Finset.univ` over a Boolean table.  There is
no counted candidate enumerator.  Instead, at lines 292--301 and 321--329,
`periodicCandidateGenerationCost q d := q^d + 1` is added to every callback of
`planarTilePeriodCheckCounted`.  No theorem relates this number to a program
that constructs or successively yields all `2^(M^2)` tables.  The prose also
says that list constructors are included, although no list-producing counted
definition occurs.  Likewise, `commonCodePeriod := Nat.lcm ...` is outside the
counted trace.

There is a second local mismatch with the declared primitive model.  The model
charges one unit for each Boolean branch or integer comparison, while
`periodicTilingPointCounted` at `blueprint/08-algorithms.md:268-272` contains

```lean
decide (lhs.1 = if rhs.1 then 1 else 0)
```

but adds only one unit for the whole branch-plus-comparison expression.  A
large asymptotic upper bound may absorb this on many inputs; that does not make
the stated counted trace faithful to its own primitive rules.

**Concrete repair.**  Choose and state one precise model, then implement it.
The cleanest route is a counted recursive enumerator for bit vectors of length
`M^2`, with soundness, no-duplicates/completeness, and a proved generation-cost
bound; fold the counted candidate checker over its output.  Count `Nat.lcm`,
table decoding, branches, comparisons, constructors, and folds according to
the announced primitives.  Alternatively, explicitly declare candidate
enumeration and normalization arithmetic to be atomic oracle/preprocessing
operations and weaken/rename the theorem accordingly.  In either route, the
cost must be derived from the actual counted definition rather than injected
as an unattached callback surcharge.

## Nonblocking findings requiring specification cleanup

### RQ3 — P2: lattice conversion has correct mathematics but no aggregated counted implementation

**Risk.**  The HNF-input decision result is credible, but the advertised
conversion cost is not presently attached to an executable conversion trace.
This becomes a blocker if `latticeInputConversionCost` is retained as a public
cost guarantee.

**Location and evidence.**  `blueprint/08-algorithms.md:148-160` defines
`LatticePeriodicSetCode.scalarEntryCounted` and the closed number
`latticeInputConversionCost := 12 * P^2`.  However, `toScalarCode` is an
uncounted function, and there is no `toScalarCodeCounted` table fold with a
theorem equating or bounding its cost by `latticeInputConversionCost`.

The conversion itself is sound.  For generators `(a,0)` and `(b,c)`, membership
is normalized using division by `c`; the scalar period is `a*c`; and
`a*c e1 = c(a,0)` and `a*c e2 = a(b,c) - b(a,0)`, so `a*c Z^2` lies in the
input lattice.  Conversely the lattice generators preserve the scalar table
by the conversion definition.  The code accepts any nonsingular triangular
basis with positive diagonal, not canonical HNF because no condition such as
`0 ≤ b < a` is imposed.  This does not harm correctness, but “triangular
lattice code” would be more exact unless a canonical range condition is added.

**Concrete repair.**  Define `toScalarCodeCounted` as a counted fold over the
`(a*c)^2` entries and prove its value is `toScalarCode` and its cost is at most
the stated bound.  Either add the canonical HNF shear condition or rename the
input format.  If conversion cost is deliberately outside the main cost model,
say so and remove the unattached numerical guarantee.

### RQ4 — P2: singleton and empty-target branches need explicit final-proof routing

**Risk.**  The program behaves correctly on these cases, but the Chapter 8
proof plan jumps to a classifier whose stated hypothesis is `1 < F.card`.
Without an explicit branch, the Lean implementation plan has a small but real
proof gap.

**Location and evidence.**  The final correctness theorem at
`blueprint/08-algorithms.md:743-754` assumes `F.Nonempty`, whereas both the
chameleon iff and line-selection classification at lines 634--699 assume more
than one tile point.  After the exactly-once normalization, a singleton becomes `{0}`.
Its only tiling complement is the target itself, which is already periodic by
the input code, so “there exists a non-one-periodic complement” is false.  The
algorithm also returns false because there are no directions/chameleons.  An
empty target with nonempty tile similarly has only the empty complement; the
finite representative and strip tests are vacuous.  Empty tiles occur only in
the more general corollary/cost APIs, not in the promised main theorem, but are
already relevant to RQ1.

**Concrete repair.**  Split the correctness proof before invoking the
classifier into `F.card = 1` and `1 < F.card`, and state the empty-target lemma
used by either branch.  Document `F = ∅` separately for the unrestricted
decision/counting API and retain it as a test case.

## Exact quantitative audit

The following repaired formulas agree with the paper argument and their stated
bounds.  I found no remaining hidden existential choice in them.

| Quantity | Pinned definition / bound | Audit |
|---|---|---|
| `q` | `indicatorDilationModulus ell c` | `ell ∣ q`; explicit and computable. |
| `N` (weak rigidity) | LCM of nonzero pair wedges | The diagonal-zero bug is removed; empty LCM is `1`; `N ≤ D^((c-1)(c-2))`. |
| `M` (avoidance) | LCM of avoidance factors | `M ≤ (c+1)^c D^(c-1)`. |
| `Q` | `weakRigidityPeriod c` | Explicit finite product/LCM quantity, used uniformly. |
| weak scalar `L` | `Q * M^2 * N * (q / ell)` | Exact identity is frozen in `WeakArithmeticData`; divisibility is justified by `ell ∣ q`. |
| weak lattice index | constant `4^(4c)(c+1)^(c+1)`, exponent `D^(2(c-1)^2)` | Exponent algebra closes. |
| weak multiplier | constant `Q(c+1)^(2c)4^(2c)`, exponent `D^(c(c-1))` | Exponent algebra closes. |
| completion `N` | `completionPairLCM` | `N ≤ H^(m-1)`. |
| `N_j` | `N * r_j`, with `r_j` the wedge factor | Exact; `r_j ≤ (m+1)‖h_j‖`. |
| `C_j` | `indicatorDilationModulus (ell*N_j) c / (ell*N_j)` | Quotient is integral and computable. |
| `s_j` | slicing LCM in the primitive direction | Uses corrected nonzero-wedge factors and correct one-dimensional universal period `q*n`. |
| `L_j` | `r_j * C_j * k_j * s_j` | Exact; bound `(m+1)4^(2c)‖h_j‖^(r+1)D^r`, including `r=0` via `k_j ≤ ‖h_j‖`. |
| completion `M` | `N * ∏j L_j` | Exact; `M ≤ local^m H^(m+r)D^(mr)`. |
| final period exponent | `(c-1)(c^2+c-1)` | Correctly obtained by substituting the completion estimates; bounded by `3(c+1)^4`. |
| search exponent | `4 * periodicTilingExponent c` | Bounded by `12(c+1)^4`; independent of a complement witness. |

The corrected one-dimensional universal period is `q*n`, where `n` is the LCM
of the nonzero absolute tile offsets.  The former `lcm q n` error is gone, and
the `F={0,2}, ell=2` regression now rules it out.  Euclidean norm changes are
also normalized exactly once through `WithLp.toLp 2`, with coefficient-one
product and individual-factor estimates instead of an unjustified norm
comparison.

## Executability and classification audit

- `PeriodicSetCode` and the lattice input code are proof-free finite Boolean
  tables.  The noncomputable encoder of an arbitrary set is explicitly
  proof-side only and is not consumed by the decision program.
- The main algorithm consumes only `F` and a finite code for `E`.  The
  existential tiling complement in the correctness theorem is a promise, not
  an input witness; no witness is smuggled into the program.
- `RepresentativeTupleCode` is a genuine finite type: weak multipliers are
  bounded `Fin` data and each representative is a finite period table.
  Validation is a Boolean check on a finite fundamental box.  With
  `P = ell * B!`, every positive multiplier up to the cap divides `P`, so the
  enumeration is complete for the uniform theorem and sound even for extra
  syntactic candidates.
- The strip checker ranges over every `f0 ∈ F` and residues modulo
  `lcm(k,P)`.  Its same/different predicates cover all tile support points on
  the line.  The outer `P × P` representative box covers line types modulo the
  target period.  Thus the chameleon Boolean is extensionally equivalent to
  the mathematical chameleon condition, assuming the stated finite-box
  validation lemmas.
- `LineSelection` is intentionally an infinite mathematical object used after
  the finite chameleon decision; it is not passed to the algorithm.  The
  existence of a nonperiodic selection is therefore proof-side and does not
  compromise executability.
- Translation normalization is applied exactly once: choose the tile anchor,
  replace `F` by `F-a`, pull the target back by `a`, and leave the complement
  unchanged.  This preserves the one-periodicity predicate and avoids the
  previous double-shift risk.
- No classical `Decidable` instance is used as the computational content of
  the final decision theorem.  The residual problems concern the counted cost
  wrapper, not Boolean decidability or finite-search completeness.

## Disposition of the prior Q findings

| Prior finding | Status in this snapshot | Evidence |
|---|---|---|
| Q1: diagonal wedges polluted slicing LCM | **Resolved** | `slicingPairs` filters `wedge ≠ 0`; empty LCM is `1`. |
| Q2: universal one-dimensional period used `lcm` | **Resolved** | It is now the product `q*n`, with the explicit `{0,2}` regression. |
| Q3: quantitative functions were placeholders | **Resolved** | All audited bodies are explicit; no ellipsis remains in the pinned specification. |
| Q4: norm conversion/multiple data were ambiguous | **Resolved** | `WithLp.toLp 2`, coefficient-one bounds, and exact integer-multiple fields are specified. |
| Q5: weak `q,N,M,Q,L` dependencies were not frozen | **Resolved** | Exact scalar identity and branch membership are fields of `WeakArithmeticData`. |
| Q6: completion `N_j,C_j,s_j,L_j,M` were not frozen | **Resolved** | Exact factors and their bounds are fields of `CompletionCertificate`. |
| Q7: strip/chameleon finite coverage was incomplete | **Resolved** | All anchors, line residues, support points, and period-box line types are enumerated. |
| Q8: degenerate cases were unclear | **Partly resolved** | Arithmetic empty-LCM/content cases are explicit; final singleton/empty-target proof routing still needs RQ4. |
| Q9: algorithm relied on proof-bearing/classical data | **Resolved for decidability; new cost issue** | Search data are Boolean finite tables, but RQ2 shows generation is not honestly counted. |
| Q10: operation-count theorem was not justified | **Unresolved, now concretely false** | RQ1 gives an exact counterexample; RQ2 gives an independent trace/model mismatch. |
| Q11: lattice conversion was underspecified | **Resolved mathematically; cost incomplete** | Scalar-period conversion is sound, but RQ3 requires a counted aggregate if its cost is public. |
| Q12: closed final exponents/parameter uniformity were missing | **Resolved** | Both period and search exponents are closed and depend only on the advertised tile parameters. |

## Minimum gate for the next re-review

1. Correct the nested-fold cost identity and add a checked `F=∅, B=1`
   regression.
2. Make candidate generation part of an executable counted definition, or
   explicitly remove it from the claimed primitive-operation model; derive the
   search cost from that definition.
3. Reconcile every branch/comparison/LCM/table-construction charge with the
   declared cost primitives and re-prove the closed bound.
4. If HNF conversion cost remains public, supply a counted table-conversion
   fold and its value/cost theorem.
5. Add the singleton and empty-target branches to the final correctness proof
   route.

Until items 1--3 are completed, this snapshot does not meet the requested
sorry-free, executable, operation-counted formalization standard.
