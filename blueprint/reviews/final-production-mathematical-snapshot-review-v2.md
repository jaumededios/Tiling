# Final production mathematical snapshot review v2

Date: 2026-08-26 UTC

Verdict: **APPROVE**

This is a fresh, independent mathematical review of the restored sealed
production snapshot. I did not use any earlier review verdict as evidence. I
read the paper, the complete mathematical blueprint, the public theorem API,
and the substantive production proof bodies along the full dependency chain;
I also ran independent build, validator, trust, and manifest gates.

The acceptance rule for this review is strict: every unresolved P0, P1, P2,
or P3 finding blocks approval. The final finding ledger has zero unresolved
findings at every blocking severity.

## 1. Snapshot identity and immutable-review discipline

- Review workspace:
  `/home/codex/Documents/Codex/2026-08-24/usi`
- Production repository:
  `/workspace/tiling`
- Compatibility path:
  `/home/codex/Documents/Codex/2026-08-14/Tiling`
- The production and compatibility paths resolve to the same restored
  repository.
- Production Git commit:
  `f963904489adb4bd318a0475cf4d18e756b5a9aa`
- Production branch:
  `recovery/tiling-formalization-20260826`
- Production Git status after all review builds: clean.
- Lean: `4.33.0`, commit
  `d8b18978322de05a8f3dba51ef03cf5461676c17`.
- Lake: `5.0.0-src+d8b1897`.
- Mathlib commit:
  `db584cd6d46c92f209a44c0f1c829460d327499d`.

The authoritative manifest is `blueprint/SNAPSHOT.sha256`.

- Exact manifest SHA-256:
  `482c18adc1fcdb3865454bd50471cb075d662ceac4ee84f35b607a38cbfa7ae3`
- Manifest rows: `95`
- Initial verification: `95/95 OK`
- Pre-report verification: `95/95 OK`
- Post-report verification: `95/95 OK`

The rejected historical digest
`e428270de372f935f6f101fe873ecc40ee1463b45f2c113d112060ba2facd1fb`
was not used.

I treated every manifest-listed payload and every production
`TranslationalTilings` source as immutable. I made no production, manifest,
blueprint, Git, or dependency edit. This report is outside the manifest and is
the only persistent review artifact I created.

## 2. Primary mathematical source and review scope

The paper reference was checked directly against the official arXiv v3 source:

- Rachel Greenfeld and Terence Tao, *The Structure of Translational Tilings in
  `Z^d`*, [arXiv:2010.03254v3](https://arxiv.org/abs/2010.03254v3).
- SHA-256 of the retrieved official v3 source archive:
  `2f66e9edfcdecf00bf94c09b316bf49c3d08c8057f4673ece3dcb037b640037f`.

I read the complete mathematical content of the paper and the complete
blueprint chapters `01` through `11`, together with `README.md`,
`COMPARATOR.md`, `MODULE_LAYOUT.md`, and both validation descriptions. I then
audited the genuine production proof bodies supporting the main and numbered
results, concentrating on the mathematical repair zones where a type-correct
formalization could still fail to represent the paper faithfully.

The reviewed production chain was:

```text
foundations / finite differences / arithmetic / lattice geometry
  -> periodic dilation and grouped structure
  -> explicit higher-level counterexample
  -> Stepanov point counts and reciprocal roots
  -> prime-field Weil bound
  -> Chen prime-power and CRT complete sums
  -> circle equidistribution and polynomial rigidity
  -> quantitative weak periodicity
  -> slicing and periodic completion
  -> finite tiling and non-one-periodic classifiers
  -> paper-facing Main API
```

## 3. Paper-to-Lean statement fidelity

| Paper result | Lean endpoint | Independent conclusion |
|---|---|---|
| Theorem 1.3(i) | `theorem_1_3_i` | Faithful. `F.Nonempty` makes the paper's tile convention explicit and is necessary when the periodic target is empty. The conclusion stores an actual finite disjoint weak-periodic decomposition with nonzero periods. |
| Theorem 1.3(ii) | `theorem_1_3_ii` | Exact eight-element, level-four counterexample. The production proof gives the explicit tile and Bohr/fractional-part set and proves failure of every finite weak decomposition. |
| Theorem 1.4 | `theorem_1_4_uniform`, `theorem_1_4_l1`, `theorem_1_4` | Faithful and strengthened. It preserves `m <= |F|-1`, nonzero pairwise-incommensurable directions, integer-multiple-of-tile witnesses, the coefficient-one Euclidean direction/product bounds, lattice containment/index control, positive multiplier control, and cosetwise periodicity. The uniform data are chosen independently of the tiling set (indeed independently of the target as well). |
| Theorem 1.5 | `theorem_1_5_l1`, `theorem_1_5` | Faithful and quantitatively strengthened. Empty targets and singleton tiles are handled separately; the general branch produces an actual periodic tiling certificate and a closed exponent implying the paper's `O_{|F|}(|F|^4)` exponent form. |
| Corollary 1.6 | `corollary_1_6` | Faithful executable realization of the paper's unit-cost arithmetic model. The Boolean search is finite, counted, correct in both directions, and bounded by an explicit exponential search recurrence. No bit-complexity claim is made. |
| Theorem 1.7 | `theorem_1_7` | Faithful in every positive dimension, with the normalization, dimension positivity, and scalar-period positivity explicit. The returned structure contains real functions, bounds, periods, and the pointwise decomposition law. |
| Lemma 3.1 | `lemma_3_1_i`--`iii` | Faithful. Part (ii) correctly uses coprimality, resolving the source proof's `r = 1 mod q` typo. Part (iii) uses genuine `Nat.ModEq`, includes `r > 0`, and works at modulus one. |
| Theorem 3.4 / Corollary 3.5 | `theorem_3_4`, `corollary_3_5` | Faithful. Grouping is dimension-generic, preserves oriented integer multiples and both norm-product bounds. The one-dimensional universal period is the product `q*n`, not the invalid `lcm(q,n)` replacement. |
| Proposition 4.1 / Lemmas 4.2--4.3 / Proposition 4.4 | corresponding `proposition_*` and `lemma_*` endpoints | Faithful. The formalization distinguishes coefficient-constant from function-constant circle polynomials, rationality concerns only nonconstant coefficients, the complete-sum exponent is exactly `1-1/d` with a constant fixed before the polynomial, avoidance is coordinate-free on the circle, and the periodic-target premise needed in Proposition 4.4 is explicit. The source's fixed `b_i` typo is correctly indexed by `j`. |
| Lemma 5.1 / Corollary 5.3 | `lemma_5_1`, `corollary_5_3` | Faithful. The slicing LCM excludes zero wedges, the primitive direction and positive periods are explicit, and the replacement preserves both whole convolution and each quotient-line convolution. |
| Theorem 5.4 | `theorem_5_4`, `theorem_5_4_exact`, `theorem_5_4_structural` | Faithful on the full paper domain. The public paper-facing result is singleton-safe. The stronger exact multiplier certificate correctly requires `1 < F.card`; the singleton branch uses a direct multiplier-one translate of the periodic target. |
| Theorem 6.2 | `theorem_6_2`, `theorem_6_2_lattice_input` | Faithful for the paper's finite input model: a nonempty tile already known to tile the periodic target. Both scalar-period tables and checked lattice-period/HNF input are covered, and the result is a two-sided Boolean correctness theorem. |

No theorem loses a paper conclusion. Added hypotheses are precisely the
positivity, nonemptiness, normalization, or finite-code conditions that the
paper treats as conventions or as part of its input representation.

## 4. Substantive proof-body audit

### 4.1 Foundations, lattice geometry, and dilation

`Basic.lean` uses the finite tile as the finite side of convolution, so no
summability or finite-support hypothesis is silently imposed on the tiling
set. `TilesAtLevel` agrees with exact representation counts. Periodicity is
expressed both for indicators and set membership, with explicit bridges.

`LatticeGeometry.lean` uses the actual Euclidean `PiLp 2` norm rather than the
ordinary supremum norm on functions. Cramer's identity, subgroup index,
content/primitive decomposition, common integer multiples, bounded avoidance,
and determinant-LCM containment are proved over the correct dimensions and
with the zero-vector cases separated.

`Dilation/Periodic.lean` contains a genuine Frobenius argument over
`AddMonoidAlgebra (ZMod p)`, the bounded integral lift from congruence to
equality, strong induction over prime factors, and an explicit finite Folner
box/symmetric-difference estimate. The final integer-valued averaging
argument forces the convolution difference to be zero; it is not an assumed
limit or a hidden analytic oracle.

### 4.2 Structure and counterexample

`Structure/Grouped.lean` constructs the structural functions from the
periodic dilation theorem, groups nonzero tile vectors by a genuine
commensurability quotient, and builds a common integer multiple for each
class. The l1 and Euclidean product estimates are derived classwise and then
multiplied over a real partition; no dimension-dependent norm-equivalence
loss is smuggled into the coefficient-one Euclidean claim.

`Counterexample.lean` proves the parity cancellations, tile cardinality and
level-four convolution, and then carries out the finite-difference
obstruction. The contradiction uses the infinite range of irrational
fractional parts after bounded higher differences force constancy. The
non-weak-periodicity conclusion is not postulated.

### 4.3 Weil--Stepanov, Chen complete sums, and rigidity

The number-theory dependency direction is sound. The Stepanov modules build
the auxiliary polynomial, multiplicity constraints, additive point-count
bound, Artin L-series trace identity, and reciprocal-root estimates. In
`PolynomialWeilBound.lean`, those roots are explicitly enumerated, their
norms are bounded by `sqrt p`, and the standard nontrivial additive character
specialization yields `(degree-1)*sqrt p` when `0 < degree < p`.

`CompleteExponentialSum.lean` discharges the conditional
`PolynomialPrimeSumBound` using that proved Weil theorem. The unconditional
Chen prime, prime-power, CRT/factorization, low-degree linear/quadratic, and
global fixed-degree estimates are real theorem bodies. The terminal
`polynomialCompleteSum_effective` invokes the proved bound rather than an
abstract prime-sum premise.

`PolynomialRigidity.lean` transports this terminal theorem to primitive
integral phases and circle polynomials, derives a fixed-degree constant,
combines equidistribution with the Fejer separator, and proves that avoiding
a positive rational ball forces a uniformly bounded positive period. The
half-circle specialization used downstream is correctly expressed through
real lifts rather than a nonexistent order on `AddCircle`.

### 4.4 Weak periodicity, slicing, and completion

`WeakPeriodicity.lean` contains the finite-difference elimination producing
the line polynomials, the pairwise supremum inequality, and both cases of the
coset-periodicity proof. The periodic target is used where the paper uses it.
The arithmetic `q-N-M-Q-L` data prove actual lattice membership and the
claimed relative-index/multiplier bounds. Canonical grouping makes the
uniform data depend only on the permitted inputs.

`Slicing.lean` proves the slice-convolution period by finite ray averages and
a compactness/subsequence limit, then constructs the improved set by choosing
consistent representatives of finite line-orbits. It proves scalar
periodicity, whole-convolution equivalence, and line-by-line convolution
equivalence.

`PeriodicCompletion.lean` proves component convolution periodicity by
eliminating the other components, improves each component, establishes
disjointness from the level-one convolution identity and nonempty tile, and
builds the final periodic union. The one-part, multi-part, empty-target,
singleton-tile, normalization, rebasing, and recentering branches are all
implemented. The closed l1 and Euclidean bounds follow from the exact stored
arithmetic, with protective `max 1` factors where zero diameters occur.

### 4.5 Executable classifiers

`Algorithms.lean` defines genuine Boolean programs over finite residue tables.
The planar tiling decider recursively visits positive periods up to the proved
cap, enumerates both branches of every bit table, checks finite convolution,
and has a two-sided correctness theorem plus counted cost recurrences.

The non-one-periodic classifier uses canonical tile normalization, finite
periodic representative tuples, finite line patterns, and chameleon tests.
The forward classification reconstructs every tiling through arbitrary line
selections. Conversely, two distinct chameleon directions are changed
simultaneously and their transverse supports are proved to destroy every
nonzero global period; if at most one direction is chameleonic, all other
components retain a common scalar period and the remaining component supplies
the common one-directional period. Empty target and singleton tile branches
are explicitly false, as required.

## 5. Library-scale rubric

| Rubric area | Result |
|---|---|
| Intent and content | Clear mathematical ownership: generic algebra and geometry first, analytic/number-theoretic seams independent of tiling applications, then weak periodicity, completion, algorithms, and the thin paper-facing API. |
| Reusable seams | The backward-difference adapter, lattice/primitive APIs, conditional Chen interface, unconditional Weil join, circle-polynomial layer, completion certificates, and periodic-set codes are reusable at their natural abstraction boundaries. |
| Public API | Main endpoints have explicit result types and faithful hypotheses. Proof-relevant structures expose exactly the witnesses used downstream. Validator-only axioms are not public production dependencies. |
| Module organization | The generated ownership check reports exactly 29 production modules, 869 blueprint declarations, total unique ownership, and an acyclic direct-import DAG. The umbrella imports only `TranslationalTilings.Main`. |
| Mathlib integration | The project reuses `Finset` lcm/gcd, additive monoid algebras, quotient groups, Cramer/index results, forward differences, compactness, finite fields, additive characters, and normed-space APIs. I found no competing foundational API that should replace these seams. |
| Proof architecture | Long arguments are decomposed into mathematical lemmas and typed certificates. Terminal endpoints consume proved unconditional results. No project axiom, opaque certificate, or validator import short-circuits a proof. |
| Cost and durability | There are no heartbeat, recursion-depth, error-count, or memory escape hatches in production. The strict entrypoints pass with warnings as errors. The executable cost claim is explicitly unit-cost arithmetic and is supported by counted recursive programs. |
| Refactor risk | No release-blocking refactor is warranted. The present boundaries encode important dependency direction, especially the conditional Chen seam and terminal Weil join; moving them would increase cycle and proof-coupling risk without a mathematical gain. |

## 6. Trust boundary and whole-tree scans

The complete production source tree and umbrella were scanned for:

```text
sorry  admit  axiom  opaque  unsafe
BlueprintIntegrated  BlueprintModuleValidation  blueprint.validation
maxHeartbeats  maxRecDepth  maxErrors  memory overrides
```

Result: no occurrence in production.

The generated blueprint validators intentionally replace bodyless blueprint
theorems by exact-type axioms. They are interface/module-boundary evidence
only and are outside the proof trust boundary. Production imports neither
validator tree.

An independent `#print axioms` query covered 21 paper-facing endpoints:

```text
theorem_1_3_i, theorem_1_3_ii,
theorem_1_4_uniform, theorem_1_4, theorem_1_5, corollary_1_6,
theorem_1_7,
lemma_3_1_i, lemma_3_1_ii, lemma_3_1_iii,
theorem_3_4, corollary_3_5,
lemma_4_2, lemma_4_3, proposition_4_4,
lemma_5_1, corollary_5_3,
theorem_5_4, theorem_5_4_exact,
theorem_6_2, theorem_6_2_lattice_input
```

Every queried endpoint depends only on the standard Lean/Mathlib axioms
`propext`, `Classical.choice`, and `Quot.sound`. No project-specific axiom or
validator declaration appears.

## 7. Hash record for principal sources

| Artifact | SHA-256 |
|---|---|
| `blueprint/SNAPSHOT.sha256` | `482c18adc1fcdb3865454bd50471cb075d662ceac4ee84f35b607a38cbfa7ae3` |
| `TranslationalTilings.lean` | `878d8516314a945acc9f2a2bda96f4c0ece894e5f66960ad6fc9c6033a40866c` |
| `TranslationalTilings/Main.lean` | `410366b9f079319164e0ba73c15b1a83d2902a39c6c838cf09b6fa567b742536` |
| `TranslationalTilings/Algorithms.lean` | `652c9cb48810aa1f7634bcabb2bb0bcaf3b86c4eb14ece52f1596731cd68930b` |
| `TranslationalTilings/Counterexample.lean` | `71435b6b23418bdeadf0e48df98caca03cf8b8970c6bcea5c4e2e59df1f7f6ff` |
| `TranslationalTilings/Dilation/Periodic.lean` | `b998f477ff1095a077346a02f622390a638c087da50f08bb77eeef360e9381b8` |
| `TranslationalTilings/Structure/Grouped.lean` | `76810941f6c1e7ba1eed109b2b7731b14f5df8981002e2b802023f8b97527b2e` |
| `TranslationalTilings/WeakPeriodicity.lean` | `249885c54a6d1db40c048d7be2f39d3bb91a6ffe4469e76b713f2de4d188d950` |
| `TranslationalTilings/Slicing.lean` | `d4ddf872b1bcc6d745736a6fe3abe9ed33294b8367292a23f9d2d0ea179afb64` |
| `TranslationalTilings/PeriodicCompletion.lean` | `50042b2e2a33b99a340f49373d2e36b0dae7bd3e234171d7f1134056170504d6` |
| `TranslationalTilings/NumberTheory/Stepanov/AdditivePointCount.lean` | `d22881870c4f14c59654073a56ce79e844b9dd83792160c9c61f22ed6dc41b8d` |
| `TranslationalTilings/NumberTheory/PolynomialWeilBound.lean` | `77c40b5ae025a53cdb4509fd0f1b63800438942a162c4ea0139e3748334dcc34` |
| `TranslationalTilings/NumberTheory/CompleteExponentialSum.lean` | `49cb393764e53f1e89f373ca09245bb6fbd88fe858e8c77215d463f4da35098c` |
| `TranslationalTilings/Analysis/PolynomialRigidity.lean` | `da6d870c5720242a9e1a6840596135f2e0e0e952f254bca790c5feeb36a213d6` |
| `lakefile.toml` | `f8794e06f4762d16d79699c596faf9465e18ece342b2e44df96028ac91aa914f` |
| `lean-toolchain` | `302cd63c54178885b89e669f33b38f12f4dd7ae7e5cac537b3203e3768d8fb2b` |
| `lake-manifest.json` | `fe7404c5eb045345e32beb25e6af810847e6c465af209b8b8adaa6a0fb84106f` |

These hashes agree with the sealed manifest.

## 8. Independent command evidence

| Command/gate | Result |
|---|---|
| `sha256sum blueprint/SNAPSHOT.sha256` and row count | Exact target digest; 95 rows. |
| `sha256sum -c blueprint/SNAPSHOT.sha256` | `95/95 OK` initially, before report generation, and after report generation. |
| `python3 blueprint/validation/generate_integrated.py --check` | PASS. Strict generated integrated artifact and 869-row declaration ledger current. |
| `python3 blueprint/validation/modules/generate_modules.py --check` | PASS: 29 modules, 869 declarations, acyclic DAG. |
| `sha256sum -c blueprint/validation/modules/generated-hashes.sha256` | All generated module-validation payloads OK. |
| `lake query TranslationalTilings` | Exit 0. Target resolved in the restored production package. |
| `lake build TranslationalTilings` | PASS: `Build completed successfully (3463 jobs)`. |
| `lake env lean -DwarningAsError=true TranslationalTilings/Main.lean` | PASS, no output. |
| `lake env lean -DwarningAsError=true TranslationalTilings.lean` | PASS, no output. |
| `lake env lean /tmp/FinalMathAudit.lean` | PASS; all endpoint types checked and all axiom closures were standard-only. |
| strict `lake env lean` on `blueprint/validation/BlueprintIntegrated.lean` with `relaxedAutoImplicit=false`, `maxSynthPendingDepth=3`, `maxErrors=1000` | PASS, no output. |
| `python3 blueprint/validation/modules/generate_modules.py --build` | PASS: `Build completed successfully (3446 jobs)` and module-validation current. The replay emitted only style lints for generated long lines/header text; production passed the separate warnings-as-errors gates. |
| `lake build Tiling TranslationalTilings` | PASS: `Build completed successfully (3479 jobs)`, confirming both independent library roots coexist. |
| production trust/import/resource scan | PASS: no forbidden marker, validator import, or resource escape hatch. |
| `git -C /workspace/tiling status --short` | Empty after all commands. |

## 9. Finding ledger

| Severity | Unresolved findings | Disposition |
|---|---:|---|
| P0 | 0 | None. |
| P1 | 0 | None. |
| P2 | 0 | None. |
| P3 | 0 | None. |

Informational conditions that are not findings:

1. Validator-only exact-type axioms are intentionally outside production and
   are not imported by production.
2. The module validator replays Markdown-generated files and reports sealed
   style lints for long lines/header text. The validator exits successfully,
   and the genuine production entrypoints pass with warnings promoted to
   errors.
3. Noncomputable choice is used only for proof-side mathematical witnesses
   such as compactness limits and arbitrary periodic-set encodings. The
   advertised classifiers themselves are concrete Boolean programs over
   finite codes.

## 10. Final decision

The sealed snapshot is mathematically faithful to arXiv:2010.03254v3, closes
the analytic estimate internally, proves the full tiling/rigidity/completion
chain with genuine production bodies, handles the documented degenerate
cases, exposes correct finite classifier endpoints, and has a clean standard
trust closure. All snapshot, build, validator, and query gates pass.

**APPROVE**
