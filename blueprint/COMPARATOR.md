# Paper / blueprint / Lean comparator

This document compares arXiv:2010.03254v3, the mathematical blueprint, and the
implemented public Lean API.  It was first written before proof implementation
and was maintained through production: every statement drift discovered by
Lean work was returned to the blueprint and independently re-reviewed.

Reference paper: Rachel Greenfeld and Terence Tao, *The Structure of
Translational Tilings in `Z^d`*, arXiv:2010.03254v3.

Pinned formal environment: Lean 4 / Mathlib snapshot
`db584cd6d46c92f209a44c0f1c829460d327499d`.

## Reading the comparison

- “Exact” means the Lean conclusion is the source conclusion with notation
  translated and every hidden hypothesis made explicit.
- “Strengthened” means the Lean result contains extra usable data or a closed
  bound while immediately implying the paper statement.
- “Clarified” means the source relies on a standard convention or contains a
  typographical slip; the mathematical content is unchanged.
- A signature-only elaboration check verifies types and instances, not proofs.
  No row is considered formalized until its implementation builds without
  `sorry`, `admit`, project axioms, or opaque certificates.

## Main results

| Paper result | Source content | Public Lean declaration | Comparison | Quantitative/certificate payload | Principal proof chain |
|---|---|---|---|---|---|
| Theorem 1.3(i) | Every level-one tiling of a periodic subset of `Z²` by a finite tile is weakly periodic. | `theorem_1_3_i` | Clarified: adds `F.Nonempty`, the standard meaning of “tile”. Without it, `F=∅, E=∅` is a counterexample. `IsPeriodic E` is otherwise literal. | `WeakPeriodicDecomposition` stores the finite disjoint parts and a nonzero period for each. | Obtain a scalar period from the finite-index period lattice; translate the tile to contain zero; singleton branch; Theorem 1.4; convert cosetwise periodicity into a disjoint weak decomposition. |
| Theorem 1.3(ii) | An eight-element tile has a level-four tiling of `Z²` which is not weakly periodic. | `theorem_1_3_ii` | Exact. | Witnesses are the executable `counterexampleTile` and the explicit Bohr/floor set `counterexampleSet`. | Lemma 2.1 sign function; real indicator factorization; irrational fractional-part range; finite-difference obstruction to any finite weak decomposition. |
| Theorem 1.4 | Quantitative weak periodicity with `m≤|F|-1`, lattice-index, direction, and multiplier bounds; structural data independent of `A`. | `theorem_1_4_uniform`, `theorem_1_4_l1`, `theorem_1_4` | Strengthened. The uniform form chooses data before both `E` and `A`. The Euclidean form retains the source’s coefficient-one individual and product direction bounds. Each direction is an actual integer multiple of a nonzero tile vector. | `QuantitativeWeakPeriodData` exposes `m,h,Λ,L`, nonzero and pairwise-incommensurable laws, tile multipliers, both norm bounds, subgroup inclusion, relative-index bound, positive multiplier bound, and period membership. | Theorem 3.4; canonical grouping by primitive direction; Proposition 4.1; Lemmas 4.2--4.3; Proposition 4.4; exact q-N-M-Q-L arithmetic. |
| Theorem 1.5 | A tilable `ell Z²`-periodic target has an `ell*M Z²`-periodic tiling with `M <<_|F| diam(F)^{O(|F|⁴)}`. | `theorem_1_5_l1`, `theorem_1_5` | Strengthened. Gives a closed exponent and a typed certificate; handles empty targets and singleton tiles explicitly. | `periodicTilingExponent c=(c-1)*(c²+c-1)` and `periodicTilingExponent c≤3*(c+1)⁴`. `PeriodicTilingCertificate` stores `A'`, positive `M`, periodicity, and tiling. | Theorem 1.4; explicit quotient-fiber conversion to a directional partition; exact one-part completion or structural Theorem 5.4; certificate rebasing from `ell*L₀` to `ell`; `l1`/Euclidean comparison. |
| Corollary 1.6 | Decide whether `F` tiles `Z²` in unit-cost arithmetic time `exp(O_|F|(diam(F)^{O(|F|⁴)}))`. | `corollary_1_6` | Strengthened and made executable. The machine model is explicitly unit-cost arithmetic, as in the paper, not bit complexity. | Boolean `planarTileDecision`; counted evaluator; `planarTileSearchCost≤2^planarTileSearchExponent`; exponent bounded by a closed cardinality constant times `diameter^(4*periodicTilingExponent)`, with degree at most `12*(c+1)⁴`. | Enumerate `1≤M≤periodicTilingPeriodBound`; enumerate the `2^(M²)` subsets of the finite box; finite convolution check; Theorem 1.5 completeness. |
| Theorem 1.7 | Structure decomposition of an arbitrary set whose tile convolution is scalar-periodic. | `theorem_1_7` | Exact, with `d>0`, `ell>0`, and normalization `0∈F` explicit. | `StructureDecomposition` stores every `phi_f`, its `[0,1]` bounds, `q*f` period, and the pointwise decomposition identity. | Dilation Lemma 3.1; Følner ray averages; compact product; ultrafilter limit; finite-sum passage to the limit. |

## Numbered intermediate results

| Paper result | Lean name | Statement comparison | Formal proof obligations and reuse |
|---|---|---|---|
| Lemma 2.1 | `lemma_2_1` / `Counterexample.chi_lemma` | Exact concrete witness `chi : Z²→{−1,1}`, period four, annihilated by both two-point convolutions used by the construction. | Coordinate parity; finite convolution calculation; no analytic dependency. |
| Lemma 3.1(i) | `lemma_3_1_i` / `dilation_prime` | Exact prime-dilation clause, with boundedness and positive prime hypotheses explicit. | `AddMonoidAlgebra` over `ZMod p`; Frobenius; reduction/lift of the integer identity. |
| Lemma 3.1(ii) | `lemma_3_1_ii` / `dilation_coprime` | Exact theorem statement uses coprimality with the small-prime product. The source proof’s phrase `r=1 mod q` is recorded as a typo. | Prime factorization; repeated prime dilation; `Nat.Coprime`; preservation of cardinality under positive dilation. |
| Lemma 3.1(iii) | `lemma_3_1_iii` / `dilation_periodic` | Exact bounded-function periodic version. Congruence is `Nat.ModEq`, including modulus one. | Følner boxes with an explicit symmetric-difference estimate; bounded error tends to zero; integrality forces exact equality. |
| Theorem 3.4 | `theorem_3_4` | Exact in arbitrary `Z^d`; the one source line saying `Z²` is a prose typo. | Group Theorem 1.7 terms by canonical commensurability class; lcm scale produces a common integer multiple; direct product norm estimate. |
| Corollary 3.5 | `corollary_3_5` | Exact period `q*n`, not `lcm(q,n)`, where `n=lcm_{f≠0}|f|`. | In one dimension every nonzero direction period divides `q*n`; the mod-one decomposition leaves the indicator invariant. Regression instance `F={0,2}` distinguishes product from lcm. |
| Proposition 4.1(i) | `proposition_4_1_i` | Exact circle-valued mod-one sum on each lattice line. | Substitute the q-N-M lattice coordinates into the grouped decomposition. |
| Proposition 4.1(ii) | `proposition_4_1_ii` | Exact: every line function is a circle polynomial of the stated bounded degree. | Iterated backward differences eliminate the other periodic summands; bounded real sequence with vanishing higher difference; Newton/falling-factorial representation. |
| Proposition 4.1(iii) | `proposition_4_1_iii` | Exact pairwise supremum inequality. | Pointwise nonnegativity and `sum phi≤1`; translate suprema along independent line variables. |
| Lemma 4.2 | `lemma_4_2`, `lemma_4_2_bigO`; strengthening `complete_exponential_sum_paper` | Exact exponent `1-1/d`; `lemma_4_2` uses the paper's literal nonconstant-map hypothesis, and the constant is chosen before `P`. Rationality concerns only nonconstant coefficients. | Pass from nonconstant map to nonconstant coefficient data; normalize to a primitive integral phase; repeat averages under denominator change; use the recursively proved CRT/Weil/Chen complete-sum theorem. |
| Lemma 4.3 | `lemma_4_3`, `lemma_4_3_halfCircle` | Coordinate-free exact reformulation: a positive-length interval in `R/Z` contains a positive-radius metric ball. The used half-circle is expressed by real lifts, not an order on `AddCircle`. | Irrational coefficient implies equidistribution by van der Corput with residue-class splitting; a Fejér bump detects an avoided ball; Lemma 4.2 bounds the common denominator uniformly. |
| Proposition 4.4 | `proposition_4_4` | Exact period and lattice-membership conclusion under the paper's periodic-target hypothesis `SetScalarPeriodic ell E`; source summand `b_i` corrected to `b_j`.  The hypothesis is explicit because `GroupedStructureDecomposition` stores only the decomposition data, not the assumptions used to construct it. | Target periodicity makes `E` constant on weak-lattice cosets. Two supremum branches then give periodic rigidity for all but possibly one circle polynomial; the mod-one sum transfers the common period to the exception; exact q-N-M-Q multiplier. |
| Lemma 5.1 | `lemma_5_1` | Exact. `slicingLCM` filters by nonzero wedge, so diagonal and parallel differences never insert zero. | Dilation ray limit restricted to a tile slice; periods along `ell*k*h` and `q*k*f`; Cramer inclusion; lcm of nonzero determinants. |
| Corollary 5.3 | `corollary_5_3` | Exact, including equality of convolution on every quotient line. | `SL(2,Z)` sends the primitive vector to `(1,0)`; finitely many positive-length bit patterns; least equivalent representative; transport back. |
| Theorem 5.4 | `theorem_5_4`; strengthenings `theorem_5_4_exact`, `theorem_5_4_structural`; component clause `convolution_part_scalarPeriodic` | Canonical `theorem_5_4` is valid for every nonempty tile and returns `PaperCompletionResult`: the periodic completion with the honest `m`-dependent bound plus the separate component-convolution conclusion.  For `F.card=1` it uses a multiplier-one translate of the target.  The full exact `N * product L_j` certificate requires `1<F.card`; the structural result derives this from `2≤m≤F.card-1` and gives the printed hidden constant depending only on `|F|`. | Eliminate other components by differences to obtain canonical `N_j`; split `F.card=1` versus `1<F.card`; translate the periodic target in the singleton branch; otherwise use Corollary 5.3 componentwise and nonnegative level-one convolution for disjointness.  The `k=4096` regression proves the old singleton exact-certificate bound false.  Under `m≤c-1`, compare `((m+1)4^(2c))^m` with `(c4^(2c))^c`. |
| Theorem 6.2 | `theorem_6_2`, `theorem_6_2_lattice_input` | Exact for nonempty `F` together with existence of a tiling, when the target is supplied as a scalar-period code or in the checked triangular/HNF wire format. A proof-side coverage theorem shows that every finite-index lattice-periodic mathematical target admits such a code. Raw generator normalization is outside the wire-format decision API. | One executable tile/target normalization; lazy HNF-to-scalar reindexing; finite representative tuples; finite-strip chameleon test; classification by arbitrary line selections; two nonparallel changed lines destroy every nonzero period; at most one chameleon leaves a common period. |

## Exact quantitative dictionary

Write `c=F.card`, `D=l1Diameter F`, and `m` for the number of directions.

| Paper symbol or estimate | Closed Lean expression | Exact law used downstream |
|---|---|---|
| `q=lcm(ell, primes≤2c)` | `indicatorDilationModulus ell c` | `ell∣q`, `q≤ell*4^(2c)` |
| bounded avoidance vector `eTilde` | `avoidanceVector h` | nonzero, incommensurable with every `h_j`, `l1Norm≤m+1` |
| pair determinant lcm `N` | `pairWedgeLCM h` | positive for nonzero pairwise-incommensurable directions; `N≤prod_j ||h_j||₁^(m-1)` |
| avoidance determinant lcm `M` | `directionAvoidanceLCM h` | positive; `M≤(m+1)^m*prod_j ||h_j||₁` |
| universal rigidity period `Q_m` | `weakRigidityPeriod m` | every degree-`≤m` rigidity period divides it; `weakRigidityPeriod m ∣ weakRigidityPeriod c` supplies the cardinality-only cap |
| exact weak arithmetic | `WeakArithmeticData F ell h hm` | binds `q,N,M,Q_m,Lambda,L`, proves `ell*L=Q_m*M²*N*q`, and stores both branch-period and advertised-period membership facts |
| weak multiplier `L` | `weakMultiplier F ell h` | `Q_m*M²*N*(q/ell)` exactly; positive and bounded using the `Q_c` cap in `weakPeriodMultiplierBound c D` |
| weak lattice `Lambda` | `weakLattice F ell h hm` | subgroup of `ell Z²`; contains every `ell*L*h_j`; relative index bounded explicitly |
| slice exponent `r` | `completionSliceExponent c` | `c*(c-1)/2` |
| slice lcm `s_j` | `completionSliceLCM D j` | positive; at most `(||h'_j||₁*D)^r` |
| component convolution multiplier `N_j` | `completionConvolutionMultiplier D j` | `N*|eTilde wedge h_j|` exactly |
| dilation ratio `C_j` | `completionDilationRatio D j` | `indicatorDilationModulus (ell*N_j) c=(ell*N_j)*C_j`; `C_j≤4^(2c)` |
| one-part dilation ratio | `onePartDilationRatio D` | `indicatorDilationModulus ell c=ell*onePartDilationRatio D`; it is positive when `ell>0` |
| component completion factor `L_j` | `completionPartMultiplier D j` | `|eTilde wedge h_j|*C_j*k_j*s_j` exactly |
| final exact-construction multiplier `M` | `completionMultiplier D` | `N*prod_j L_j` exactly; `CompletionCertificate` existence requires `1<c` |
| General paper-facing Theorem 5.4 bound | `weakCompletionPeriodBound c D m H` | `PaperCompletionResult` is singleton-safe.  Its bound is `((m+1)4^(2c))^m * H^(m+r) * D^(m*r)`, with protective `max 1` factors and explicit `m` dependence; for `c=1` the direct witness has multiplier one. |
| Structural Theorem 5.4 bound | `structuralCompletionPeriodBound c D m H` | `(c4^(2c))^c * H^(m+r) * D^(m*r)` under `2≤m≤c-1`; these inequalities imply `1<c`, and the hidden constant depends only on `c` |
| Theorem 1.5 exponent | `periodicTilingExponent c` | `(c-1)*(c²+c-1)≤3*(c+1)^4` |
| finite-search cap | `periodicTilingPeriodBound c D` | every periodic witness multiplier is visited by the executable recursion through `1,...,cap` |
| search exponent | `planarTileSearchExponent F` | bounds the counted search by a power of two; diameter exponent is `4*periodicTilingExponent c≤12*(c+1)^4` |

## Definition and representation comparison

| Mathematical object | Lean representation | Why this representation is faithful and useful |
|---|---|---|
| `Z^d`, `Z²` | `Lattice d := Fin d → ℤ`, `Plane := Lattice 2` | Native coordinatewise additive group; finite-dimensional products and finite sums are already in Mathlib. |
| Finite tile | `Finset (Lattice d)` | Executable membership and finite convolution; duplicates are excluded by construction. |
| Indicator | `setIndicator A : G→ℤ` | Integer codomain records tiling levels exactly. It is noncomputable for arbitrary `Set`, which is kept outside Boolean algorithms. |
| Tile convolution | `tileConv F g x = sum_{f∈F} g(x-f)` | Total because the tile factor is finite; no summability assumption. |
| Level-`k` tiling | `TilesAtLevel F A E k` | Pointwise equality to `k*1_E`; `Tiles` specializes to level one. |
| Scalar periodicity | `ScalarPeriodic q f`, `SetScalarPeriodic q A` | Quantifies translations by every `q*z`; set and indicator forms have an exported equivalence. |
| Weak periodicity | `WeakPeriodicDecomposition` | Stores disjoint parts and nonzero period vectors, rather than a proof-irrelevant indicator sum. |
| Plane determinant | `wedge u v` | Integer determinant supports commensurability, subgroup index, and Cramer bounds without real coercions. |
| Euclidean norm | norm of `WithLp.toLp 2` in `EuclideanSpace` | Avoids the incorrect Pi supremum norm. Integer `l1` remains the executable bound norm. |
| Commensurability | nonzero integer multiples `a*u=b*v` | Excludes the zero-vector degeneracy intentionally; determinant lemmas state their nonzero hypotheses. |
| Primitive direction | gcd content and `primitivePart` | Computes both the primitive vector and the integer scale required by slicing and Section 6. |
| Circle polynomial | coefficient vector in `AddCircle 1` | Separates coefficient-constant, function-constant, and torsion-nonconstant predicates; the constant coefficient never enters denominators. |
| Positive-length interval in `R/Z` | positive-radius `Metric.ball` in `AddCircle 1` | Invariant under circle coordinates and avoids the ill-typed ordered interval API. |
| Periodic set input | `PeriodicSetCode` with a Boolean table on `Fin` residue vectors | Proof-free finite payload with unit table lookup; the positive period is stored; arbitrary-set encoding is explicitly noncomputable and not used by decisions. |
| General period-lattice input | `LatticePeriodicSetCode` in checked two-generator Hermite wire form | Stores `a,c>0`, the canonical shear range `0≤b<a`, and the `a*c` quotient bits; converts lazily to scalar period `a*c`; the two explicit generator identities prove the scalar-lattice inclusion. `exists_latticePeriodicSetCode_of_finite_quotient` proves coverage of every finite-index periodic target using proof-side (possibly noncomputable) HNF and quotient choices; no raw-normalization algorithm or cost is claimed. |
| Periodic representative tuple | bounded multiplier plus a finite function of finite residue subsets | Derives `Fintype` and `DecidableEq`; no arbitrary directions, periods, sets, or proof fields. |
| Individual tiling in the classifier | `LineSelection` over quotient lines | Correctly represents the genuinely infinite independent line choices without claiming to enumerate them finitely. |
| Unit-cost computation | recursive positive-period and Boolean-table searches, plus counted finite-input folds | The actual program visits `1,...,B` and recursively generates both branches of every `M²`-bit table. Exact structural cost recurrences are proved before the closed bound; no enumeration surcharge or list-order assumption is used. Its scope is unit-cost arithmetic, not bit complexity. |

## Source errata and formalization-only clarifications

| Location | Source text/problem | Comparator disposition |
|---|---|---|
| Lemma 3.1(ii), proof | Says an integer is `1 mod q` where the factorization step only requires and uses coprimality with `q`. | The statement and Lean use `Nat.Coprime`; documented source typo. |
| Theorem 3.4 discussion | One line says `Z²` although the result and proof variables are in `Z^d`. | Lean theorem remains dimension-generic. |
| Proposition 4.4, equation (29) | A summation term contains fixed `b_i` instead of indexed `b_j`. | Lean uses `b_j`; documented source typo. |
| Section 6 affine-line prose | Contains unmatched bracket/name slips. | Quotient-fiber and `addCoset` definitions remove representative ambiguity. |
| “finite tile” in Theorem 1.3(i) | Mathematical convention means a nonempty finite translating set, but the bare English adjective can be read as allowing empty. | Lean adds `F.Nonempty`; an empty-tile regression demonstrates necessity. |
| Theorem 5.4 exact construction at `|F|=1` | The paper conclusion remains true, but the blueprint's former stronger exact certificate used an `r>0` estimate when `r=|F|(|F|-1)/2=0`; scaled directions with permitted empty parts violate its local and total bounds. | Canonical `theorem_5_4` handles singleton tiles directly.  Only `theorem_5_4_exact` requires `1<F.card`; `completion_singleton_bound_regression` checks the `k=4096` numerical counterexample. |
| Euclidean asymptotic bounds | Paper hides constants depending on `|F|`. | Core proofs use exact integer `l1` bounds; separate theorems recover the coefficient-one Euclidean clauses and paper asymptotics. |

## Mathlib reuse versus project work

| Layer | Reused from pinned Mathlib | New project work |
|---|---|---|
| Finite algebra | `Finset`, `AddMonoidAlgebra`, `Finsupp`, `Nat.lcm/gcd`, prime factorization | Tile convolution adapters; Frobenius/dilation identities for finite tiles; exact representation-count lemmas. |
| Differences | `fwdDiff`, iterates, Gregory--Newton identities | Backward-difference convention; translation adapter; periodic-summand elimination; bounded polynomial-sequence rigidity. |
| Lattice geometry | Pi groups, matrices/adjugate, subgroup index/nsmul range, `WithLp` Euclidean spaces | Integer wedge/Cramer specialization; commensurability; primitive content; executable avoidance; determinant lcm bounds. |
| Compactness | Compact products, intervals, ultrafilter limits | Simultaneous ray-limit construction and passage of finite convolution identities. |
| Circle/Fourier | `AddCircle`, Haar probability, characters `fourier`, continuous functions/integration | Weyl criterion packaging; van der Corput; residue splitting; explicit avoided-ball separator. |
| Complete sums | `ZMod.stdAddChar`, polynomial content/derivatives, finite fields, quadratic Gauss sums, prime arithmetic | Chapter 05a proves the fixed-character prime bound by the Stepanov route; Chapter 05b owns the integral-phase/`Polynomial ℤ`/`ZMod` bridge, exact Chen recurrences, CRT/content transport, low degrees, padding, and the global degree-only constant; Chapter 05 only transfers the terminal theorem to circle polynomials. |
| Algorithms | `Fintype`, `Finset.univ`, dependent finite functions | Boolean-table periodic codes; counted folds; finite torus correctness; tuple classifier; chameleon test; line-selection completeness. |

## Signature and production evidence

The declaration-level acceptance validator is the strict, dependency-ordered
artifact `blueprint/validation/BlueprintIntegrated.lean`.  It is regenerated from all
blueprint Lean fences by
`blueprint/validation/generate_integrated.py`; the same run produces
`blueprint/validation/declaration-coverage.tsv`, which accounts for every
named declaration and distinguishes checked bodies from exact-type axiom
stubs.  Strict `--check` rejects stale artifacts, malformed fences, duplicate
public names, and theorem aliases without explicit result types.  The
integrated artifact is then elaborated against the pinned Lean/Mathlib
toolchain without ambient global classical instances.

Module resolution is checked by the separate module-aware validator in
`blueprint/validation/modules/`.  It maps all declaration-ledger rows to the
exact 29 production modules in `MODULE_LAYOUT.md`, copies definitions and
checked bodies, replaces bodyless theorems by exact-type stubs, checks the
direct-import DAG, and builds the generated umbrella through offline pinned
Lake with `relaxedAutoImplicit=false` and `maxSynthPendingDepth=3`.  Thus the
combined evidence covers both cross-declaration integration and actual
per-file visibility; neither validator supplies proof evidence.

Chapter-local files under `tmp/`--including the former foundations, geometry,
dilation, counterexample, polynomial, weak-periodicity, completion,
algorithms, and import validators--are diagnostic aids only.  Their isolated
namespaces and proposition-valued statement wrappers cannot detect public-name
collisions or dependent cross-chapter mismatches and do not establish
blueprint acceptance.

## Acceptance gate

Before proof implementation began, independent referees verified this
comparator against both the paper and the complete blueprint, confirmed that
the strict integrated artifact and declaration-coverage ledger matched the
displayed declarations, and approved an identified snapshot.  The completed
implementation is compared back to all 869 ledger rows by elaborated
`#check`/definitional-equality tests, and its theorem dependencies, trust
closure, executable regressions, imports, and documentation receive a fresh
independent review under the Tau Ceti-style standard.
