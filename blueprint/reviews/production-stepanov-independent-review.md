# Independent production referee audit: Stepanov--Weil chain

Date: 2026-08-24

Reviewer qualification: this was a fresh, read-only, author-independent audit. The reviewer did
not implement any of the eight production modules in scope. The Tau-Ceti-style acceptance rule for
this task treats every P0--P3 finding as blocking.

## Verdict

**REQUEST CHANGES / NOT ACCEPTED.**

The complete mathematical chain passes: I found no false theorem, proof gap, circular dependency,
unhandled mathematical edge case, trust violation, API mismatch, definition-body mismatch, build
failure, resource override, or project axiom. Acceptance is nevertheless blocked by:

1. one P2 artificial project dependency and associated nonminimal import surface;
2. one P3 documentation-quality failure affecting all 81 public declarations in
   `HasseMultiplicity` and `ArtinLSeries`; and
3. one P3 diagnostic-suppression failure at four proof boundaries in `AdditivePointCount`.

No P0 or P1 finding was found. None of the required repairs changes the mathematical statements or
the public declaration types.

## Frozen snapshot

The production checkout was at Git commit
`b6744348ec0c2ab44788000b031721b861424c2f` on `main`. The reviewed files were untracked in that
checkout, so the file hashes below, rather than the commit alone, are the review identity.

| Production module | Lines | SHA-256 |
|---|---:|---|
| `TranslationalTilings/NumberTheory/Stepanov/NewtonWaring.lean` | 1,066 | `66e7e95eb83c08e723489596f57241526d8126d7d6b056874d7a231f2fc552a0` |
| `TranslationalTilings/NumberTheory/Stepanov/ArtinSchreier.lean` | 414 | `ef22fcdbf9b1323673877bcdb4513dc6c6d8f292f92b9677b810c687be021a7f` |
| `TranslationalTilings/NumberTheory/Stepanov/HasseMultiplicity.lean` | 1,003 | `6062fb9c924234ffd50ff6b777abcd6ec3fe06d2286fefe003c48b109167f48b` |
| `TranslationalTilings/NumberTheory/Stepanov/TranslationProduct.lean` | 981 | `59516e9d9c97c61bd39f0bd6dad4184019eb210a0d3cf069f36ff5b0bc34d955` |
| `TranslationalTilings/NumberTheory/Stepanov/AdditivePointCount.lean` | 485 | `322f032ca3138878f98e49ec91d9a39bbb4215a7f5efd7a3169b65a1c1ccd7a7` |
| `TranslationalTilings/NumberTheory/Stepanov/ArtinLSeries.lean` | 2,228 | `01911f2355e31f22179b18c493025254e64bf8020df05adb7f3fbed05156cfea` |
| `TranslationalTilings/NumberTheory/Stepanov/ReciprocalRoots.lean` | 381 | `b5e35b730c3d4b1563e084765b2befd056cee179e6992b2fc7fd5bde6e96ff3b` |
| `TranslationalTilings/NumberTheory/PolynomialWeilBound.lean` | 124 | `329f6f19012c2141b7e0e79550b71d81269c875148ac048d41c95c46950b3d50` |

The scope is 6,682 production lines. Reference and validation hashes were:

| Reference artifact | SHA-256 |
|---|---|
| `blueprint/05a-weil-stepanov.md` | `23f3373f2f8c6f1bc5d7ac91e541a7cbb875f039c26b478fa70608a0d99c27d5` |
| `blueprint/11-refereeing-standard.md` | `eda7b9ab79e0555878bde8157d39f14bfe1b760e8bfcbfa5861fa90ee3e7f8e5` |
| `blueprint/validation/modules/declaration-modules.tsv` | `8bd2eaabe9c99d04808fbc81d0d7ba4a78e6bdb17bc680b5b02896e922725bc6` |
| `blueprint/validation/modules/module-sources.tsv` | `3e393ac86f4ca7652fef8500d07fdd6292fa3ebf8d733b8139740383cd15c961` |
| generated `NewtonWaring.lean` | `e1202ee18f1fd93cc51a0c0fa42b29d80915ad265d28e511fd5fd37ac9920e67` |
| generated `ArtinSchreier.lean` | `d1201516e5fe65b2026a8e202da0a2f82ae292354887f928c547c1af9a01352c` |
| generated `HasseMultiplicity.lean` | `361f5e6a6a3beb7e72cb84dbc852f4a8b07e303ee2759f2fd6aebe97c638de4d` |
| generated `TranslationProduct.lean` | `e671bde96ce55751a4fed695a72465fe66a78cf046cf0f21dda35f1e08d82a1c` |
| generated `AdditivePointCount.lean` | `a501860d9c9e71cc4b0fd5af394f4fbe3c46e3ccf892e926d1e2c3f7e012d6c3` |
| generated `ArtinLSeries.lean` | `b05f4fd2249817e512a4c83bb0622d07a8fdf8aa6c68fc870f3e49b6c26d4d47` |
| generated `ReciprocalRoots.lean` | `80271adec375b5aa7824b3e5fad4ad3b248c1748c35e29018da329e00b0ee8a7` |
| generated `PolynomialWeilBound.lean` | `cb70fa58ac8d282d064490b47a9fa844bd51cfbd6a4dfbe6f342f53079a25b32` |

The toolchain was Lean 4.33.0, commit
`d8b18978322de05a8f3dba51ef03cf5461676c17`, with pinned Mathlib commit
`db584cd6d46c92f209a44c0f1c829460d327499d`. The production dependency files had hashes:

- `lean-toolchain`: `302cd63c54178885b89e669f33b38f12f4dd7ae7e5cac537b3203e3768d8fb2b`;
- `lake-manifest.json`: `fe7404c5eb045345e32beb25e6af810847e6c465af209b8b8adaa6a0fb84106f`;
- `lakefile.toml`: `f8794e06f4762d16d79699c596faf9465e18ece342b2e44df96028ac91aa914f`.

## Blocking findings

### [P2] `HasseMultiplicity` is artificially coupled to `NewtonWaring`

`HasseMultiplicity.lean:2` imports the project module `NewtonWaring`, but the file uses no
declaration owned by `NewtonWaring`. Lean's `#min_imports` audit removes that project import and
recommends direct Mathlib dependencies only:

```text
Mathlib.Algebra.Order.Star.Basic
Mathlib.Data.Int.ConditionallyCompleteOrder
Mathlib.Data.Nat.Choose.Lucas
Mathlib.FieldTheory.Finite.Trace
Mathlib.LinearAlgebra.FreeModule.PID
Mathlib.RingTheory.SimpleModule.Basic
```

This is not merely a redundant leaf import: it adds a false project-level edge to the frozen module
DAG, making the Hasse-derivative/linear-algebra development depend on the logically independent
Newton--Waring development. It also causes Hasse to inherit a large collection of unrelated field,
Galois, rational-function, and complex-analysis imports. The current `module-sources.tsv` and
generated module reproduce the same edge, so signature validation cannot detect this architecture
defect.

The same minimum-import pass finds an ordinary redundant direct import at
`ArtinLSeries.lean:1`: `Mathlib.FieldTheory.Minpoly.Field` is unnecessary once
`Mathlib.RingTheory.UniqueFactorizationDomain.Finsupp` and `NewtonWaring` are imported. The
minimum-import reports also show that `NewtonWaring` and `ArtinSchreier` can expose substantially
smaller Mathlib surfaces, although those broad Mathlib imports do not create a reversed project
dependency.

Required repair: replace the Hasse-to-Newton edge by direct Mathlib imports, remove the unused
Artin-L-series import, run `#min_imports` over the complete chain, and regenerate the module-source
map and generated signature modules. The public API must remain unchanged.

### [P3] 81 public docstrings are present but not informative

`#lint only docBlame` passes in all eight modules, and every module has a module docstring. That
presence check masks a semantic documentation failure: all 42 public declarations in
`HasseMultiplicity` and all 39 in `ArtinLSeries` use mechanically generated name-expansions rather
than mathematical descriptions.

Representative examples are:

```text
HasseMultiplicity.lean:14
  "Defines the vanishes to order at least used in the Stepanov argument."

HasseMultiplicity.lean:19
  "Establishes the vanishes to order at least iff root multiplicity identity or bound."

ArtinLSeries.lean:43
  "Defines the artin lpolynomial used in the Stepanov argument."

ArtinLSeries.lean:55
  "Establishes the artin lpolynomial coeff zero identity or bound."
```

Phrases such as “identity or bound” do not tell a library user what the result says, which
hypotheses matter, what normalization is used, or how the declaration fits the finite Euler-product
and reciprocal-root chain. This is particularly harmful at the public seams for the Hasse freezing
lemma, parameter package, rank-nullity construction, finite Euler recurrence, minpoly-fiber/orbit
bridge, trace identity, and reverse-root Newton recurrence.

Required repair: replace the 81 boilerplate comments, and expand the two terse module comments,
with concise mathematical documentation. Definitions should explain the chosen normalization and
indexing; theorems should state their mathematical content and important edge conditions. Rerun
`#lint only docBlame`, but do not treat that linter alone as the quality gate.

### [P3] Four proof-style diagnostics are disabled instead of repaired

`AdditivePointCount.lean` locally disables Mathlib's default `haveI`/`letI` style linter at lines
74, 143, 160, and 328. The four scopes cover the public theorem
`stepanov_traceFiberCard_upper` and three private fiber-count lemmas. Each proof then introduces
the finite-field `Fintype` with tactic-mode `letI`.

Mathlib's linter documents that in Lean 4 an ordinary tactic-mode `let` also registers the local
instance; in a proposition proof the only difference is proof-term inlining, which is irrelevant by
proof irrelevance. Consequently these four options suppress actionable diagnostics rather than a
necessary exception. A direct `-DwarningAsError=true` compile is green only because the warnings
have been disabled at their source.

Required repair: use the linter's `let` suggestion at all four sites, remove the four scoped option
disables, and rerun warning-as-error compilation. This is a proof-only presentation change and
must not alter any public type.

## Exact API and definition-body audit

The regenerated declaration ledger has 870 lines: one header and exactly 869 declaration rows.
The eight reviewed modules own 180 rows: 179 public declarations plus the intentionally private
`waringVariable`.

| Module | Ledger rows | Public production declarations |
|---|---:|---:|
| `NewtonWaring` | 38, including private `waringVariable` | 37 |
| `ArtinSchreier` | 22 | 22 |
| `HasseMultiplicity` | 42 | 42 |
| `TranslationProduct` | 26 | 26 |
| `AdditivePointCount` | 4 | 4 |
| `ArtinLSeries` | 39 | 39 |
| `ReciprocalRoots` | 6 | 6 |
| `PolynomialWeilBound` | 3 | 3 |

The production declaration count agrees exactly with the ledger in every module. For all 179
public names, I compiled `#check @<qualified-name>` with universes displayed against both production
and the generated signature package. The diff was empty: names, universes, implicit/explicit binder
order, hypotheses, and result types agree exactly.

The 180 reviewed ledger rows consist of 59 definitions, two abbreviations, three structures, and
116 theorems. After excluding the private definition, I compared `#print` output for all 63 public
definitions/abbreviations/structures. Every body agrees. The sole textual presentation difference is
`tracePhaseFiberCard`: the validator prints the local `Fintype.ofFinite` binding, while production
zeta-reduces it. An independent `rfl` example against the exact blueprint right-hand side confirms
definitional equality.

Both validation freshness checks pass:

```text
python3 blueprint/validation/modules/generate_modules.py --check
# module validation current: 29 modules; 869 declarations; DAG acyclic

python3 blueprint/validation/generate_integrated.py --check
```

The relevant generated signature modules compile. Their generated long-line warnings are validator
formatting noise and do not occur in the production sources; production has no line over 100
characters.

## Mathematical and proof-chain audit

### Newton--Waring encoding and cancellation

- The monic coefficient encoding handles degree zero and reconstructs the polynomial exactly.
- Root-multiset power sums use multiplicities, and the Newton--Waring recurrence has the correct
  indexing and sign.
- Multiplicativity is transported through an algebraic closure without losing normalized-factor
  multiplicities.
- The affine last-coordinate formula has the right degree-positive side condition, and additive
  character orthogonality is invoked only where nontriviality and `d < p` are needed.
- The unused `hf0` hypothesis on one boundary theorem is harmless: the proved theorem is stronger,
  and the frozen public type is preserved.

### Artin--Schreier irreducibility

- The derivative is `-1`, hence the polynomial is separable.
- Differences of roots lie in the prime subfield; one chosen root generates the splitting field.
- The Galois shift map is injective, forcing minpoly degree either one or `p`; reducibility is
  therefore equivalent to the existence of a base-field root.
- The rational-function specialization clears a normalized coprime denominator and then uses the
  degree of `A ^ p - A`. It does not use the known-invalid argument that translating an arbitrary
  proper factor preserves that factor.

### Hasse multiplicities and the linear system

- Vanishing of Hasse derivatives is correctly identified with root multiplicity, and pairwise
  coprime linear factors give the degree/cardinality inequality.
- Frobenius Hasse freezing is proved with Lucas divisibility. The general theorem also handles the
  characteristic-zero branch (`p = 0`) rather than silently assuming a positive characteristic.
- The explicit Stepanov parameters prove all strict arithmetic inequalities. The `d >= 2` branch
  forces `p >= 3`; positivity and nonzero extension-degree conditions are carried where needed.
- Source and target vector spaces, coefficient decoding, reduced Hasse maps, exact finranks, and
  rank-nullity are literal. The kernel witness is transported back to nonzero auxiliary
  coefficients without collapsing to the zero polynomial.

### Translation-product descent

- Translation invariance is descended through the fixed ring generated by `T ^ p - T`, with the
  coefficient-degree filtration preserved.
- Evaluation at the trace polynomial gives the required modulus `X ^ (p ^ n)`, and the norm-degree
  inequality forces the relevant quotient polynomial to vanish.
- The Artin--Schreier minpoly selects exactly one vanishing translation factor; no illicit
  cancellation between factors is used.
- Strong induction over the coefficient blocks removes every block, including the initial-zero
  case.

### Additive point count

- Multiplicity and degree give the one-sided trace-fiber bound; the exact partition of the finite
  field converts it to a two-sided bound.
- The Stepanov parameter inequalities produce the stated square-root error with the correct powers
  of `p`, `d`, and the extension degree.
- Degree one is handled directly through the trace functional, and characteristic two is routed
  through that case rather than passed through the `d >= 2` parameter construction.

### Finite Artin L-series

- The Euler product is cutoff-finite, so no analytic convergence or illegal infinite-product
  interchange occurs.
- Coefficients are enumerated through normalized irreducible factors with multiplicity. The
  logarithmic derivative recurrence has the correct positive marked-factor contribution.
- Minpoly fibers have the correct divisibility criterion and cardinality and are identified with a
  single Frobenius/Galois orbit. Trace terms split into the right repeated orbit blocks.
- The Artin coefficient recurrence and reverse-root Newton recurrence have the correct negative
  sign. Constant coefficient one and the constant-polynomial regression are explicit.
- The `n = 1` bridge reindexes through `GaloisField.equivZmodP` and identifies the degree-one trace,
  so the terminal sum is literally over `ZMod p` rather than merely an isomorphic field.

### Reciprocal-root bound and terminal Weil theorem

- Fourier decomposition groups trace fibers correctly, and nontrivial additive-character
  cancellation removes the main term.
- Simultaneous phase alignment respects multiplicities, while submaximal normalized roots tend to
  zero. Empty multisets, zero radius, repeated roots, and the constant L-polynomial are safe.
- The terminal theorem restores the erased constant by a unit character twist, uses the exact
  one-dimensional sum bridge, and applies the triangle inequality to at most `d - 1` reciprocal
  roots. The hypotheses exclude the constant-polynomial case and require a nontrivial character.

Across the chain, extension degree zero is permitted only in definitions; every orbit/trace/cardinal
identity that needs a nontrivial extension carries a nonzero or positive degree hypothesis. I found
no reversed inequality, missing multiplicity, sign error, circular proof, or uncovered boundary
case.

## Imports and dependency direction

The frozen project-edge DAG recorded in `module-sources.tsv` and implemented in production is:

```text
NewtonWaring
ArtinSchreier
HasseMultiplicity -> NewtonWaring                 [artificial; P2 above]
TranslationProduct -> ArtinSchreier, HasseMultiplicity
AdditivePointCount -> TranslationProduct
ArtinLSeries -> NewtonWaring
ReciprocalRoots -> AdditivePointCount, ArtinLSeries
PolynomialWeilBound -> ReciprocalRoots
```

Apart from the artificial Hasse edge, the direction is correct and acyclic. No reviewed module
imports a downstream Chen, analysis, rigidity, or terminal module. The later modules import the
earlier mathematical seams rather than duplicating their results. `TranslationProduct`,
`AdditivePointCount`, `ReciprocalRoots`, and `PolynomialWeilBound` already have exact minimal project
imports under `#min_imports`.

## Build, diagnostics, resources, and trust

All direct production compilations passed with warning-as-error and no output under the default
project budget:

| Module | Wall time | Exit |
|---|---:|---:|
| `NewtonWaring` | 7.01s | 0 |
| `ArtinSchreier` | 5.52s | 0 |
| `HasseMultiplicity` | 13.62s | 0 |
| `TranslationProduct` | 6.91s | 0 |
| `AdditivePointCount` | 7.89s | 0 |
| `ArtinLSeries` | 8.81s | 0 |
| `ReciprocalRoots` | 6.04s | 0 |
| `PolynomialWeilBound` | 5.86s | 0 |

The joint build passed with `Build completed successfully (3268 jobs)`. A diagnostics-enabled,
warning-as-error compile of `PolynomialWeilBound.lean` also passed without a pending-synthesis or
resource failure. The reviewed sources contain no `maxHeartbeats` or `maxRecDepth`; no increased
resource budget was used. Scoped `backward.isDefEq.respectTransparency false` options are confined
to factorization elaboration and do not change the trust boundary. The two Newton linter exceptions
for frozen unused API data are accompanied by explanatory comments; the four undocumented
`haveILetI` suppressions are the P3 finding above.

The forbidden scan was empty for:

```text
sorry admit axiom unsafe placeholder opaque native_decide
BlueprintModuleValidation maxHeartbeats maxRecDepth
```

I ran `#print axioms` on all 179 public ledger declarations. Exactly 179 results were parsed. The
union of axioms is precisely:

```text
Classical.choice
Quot.sound
propext
```

No project axiom, generated-validator axiom, or unexpected trust dependency appears.

Appending `#lint only docBlame` to each module in an ephemeral check compiles with
`-DwarningAsError=true`. This proves documentation presence; it does not discharge the P3 semantic
documentation defect above.

## Library-referee assessment

1. **Intent and mathematical specification:** clear and faithful to the approved chapter.
2. **Reusable boundaries:** strong theorem seams throughout; blocked only by the false
   Hasse-to-Newton project edge.
3. **Public API:** exact against all 179 public ledger rows; no accidental export found.
4. **Dependency direction:** acyclic and mathematically ordered except the P2 artificial edge.
5. **Mathlib reuse:** strong use of polynomial multiplicities, Hasse derivatives, finite fields,
   traces, minpolys, normalized factors, linear maps, rank-nullity, and complex norms.
6. **Proof architecture:** finite algebraic recurrences and explicit transports replace informal
   analytic or isomorphism shortcuts.
7. **Durability:** proof structure is robust under the default budget; P3 docs and disabled style
   diagnostics must be repaired before acceptance.
8. **Refactor risk:** preserve every public type and the finite-recursion architecture. Do not
   replace the Artin--Schreier proof by translation of arbitrary factors, and do not replace the
   finite L-series recurrence by a formal infinite Euler product.

## Reproduction commands

Run production commands from `/home/codex/Documents/Codex/2026-08-14/Tiling`:

```bash
for file in \
  TranslationalTilings/NumberTheory/Stepanov/NewtonWaring.lean \
  TranslationalTilings/NumberTheory/Stepanov/ArtinSchreier.lean \
  TranslationalTilings/NumberTheory/Stepanov/HasseMultiplicity.lean \
  TranslationalTilings/NumberTheory/Stepanov/TranslationProduct.lean \
  TranslationalTilings/NumberTheory/Stepanov/AdditivePointCount.lean \
  TranslationalTilings/NumberTheory/Stepanov/ArtinLSeries.lean \
  TranslationalTilings/NumberTheory/Stepanov/ReciprocalRoots.lean \
  TranslationalTilings/NumberTheory/PolynomialWeilBound.lean
do
  lake env lean -DwarningAsError=true "$file"
done

lake build \
  TranslationalTilings.NumberTheory.Stepanov.NewtonWaring \
  TranslationalTilings.NumberTheory.Stepanov.ArtinSchreier \
  TranslationalTilings.NumberTheory.Stepanov.HasseMultiplicity \
  TranslationalTilings.NumberTheory.Stepanov.TranslationProduct \
  TranslationalTilings.NumberTheory.Stepanov.AdditivePointCount \
  TranslationalTilings.NumberTheory.Stepanov.ArtinLSeries \
  TranslationalTilings.NumberTheory.Stepanov.ReciprocalRoots \
  TranslationalTilings.NumberTheory.PolynomialWeilBound

lake env lean -Ddiagnostics=true -DwarningAsError=true \
  TranslationalTilings/NumberTheory/PolynomialWeilBound.lean

rg -n --ignore-case \
  '\b(sorry|admit|axiom|unsafe|placeholder)\b|maxHeartbeats|maxRecDepth|BlueprintModuleValidation|native_decide|\bopaque\b' \
  TranslationalTilings/NumberTheory/Stepanov \
  TranslationalTilings/NumberTheory/PolynomialWeilBound.lean

rg -n '^import |^set_option |^/-!|^/--' \
  TranslationalTilings/NumberTheory/Stepanov/{NewtonWaring,ArtinSchreier,HasseMultiplicity,TranslationProduct,AdditivePointCount,ArtinLSeries,ReciprocalRoots}.lean \
  TranslationalTilings/NumberTheory/PolynomialWeilBound.lean
```

Run validation freshness checks from `/home/codex/Documents/Codex/2026-08-24/usi`:

```bash
python3 blueprint/validation/modules/generate_modules.py --check
python3 blueprint/validation/generate_integrated.py --check
```

The exact API check generated `#check @<qualified-name>` commands from the reviewed rows of
`declaration-modules.tsv`, enabled `pp.universes`, compiled once against production and once against
`BlueprintModuleValidation`, and diffed the outputs. The definition audit repeated that method with
`#print` for public `def`, `abbrev`, and `structure` rows. The trust audit generated one
`#print axioms <qualified-name>` command per public row and rejected any axiom outside the three
listed above.

## Acceptance gate

Do not accept these frozen hashes as Tau-Ceti-standard production. First repair the project import
edge and regenerate its validation metadata, replace the 81 boilerplate docstrings, and remove the
four diagnostic suppressions. Then rerun the exact API/body, default warning-as-error build,
`docBlame`, forbidden-token, line-length, diagnostics, and all-public-axiom checks, bind the new
results to new hashes, and obtain an independent follow-up verdict. No mathematical theorem or
proof-chain redesign is requested by this audit.
