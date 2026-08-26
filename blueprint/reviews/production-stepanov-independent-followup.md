# Independent production follow-up: Stepanov--Weil chain

Date: 2026-08-24

Reviewer qualification: this is a fresh, read-only, author-independent PM6 follow-up. The reviewer
did not implement any of the eight production modules. The rereview covers the repaired bytes, not
the superseded snapshot in `production-stepanov-independent-review.md`. Every P0--P3 finding is
blocking.

## Verdict

**ACCEPT.**

All three findings from the initial independent audit are resolved. No new P0, P1, P2, or P3
finding was found. The repaired import graph is accurate and explicitly provider-oriented; the 81
formerly mechanical docstrings are now mathematical and informative; the four disabled
`haveI`/`letI` diagnostics are gone. Exact API, definition-body, build, documentation, resource,
trust, validation-freshness, and axiom gates all pass.

## Frozen follow-up snapshot

The production checkout remained at Git commit
`b6744348ec0c2ab44788000b031721b861424c2f` on `main`. The reviewed files remain untracked, so the
eight hashes below are the production review identity.

| Production module | Lines | SHA-256 |
|---|---:|---|
| `TranslationalTilings/NumberTheory/Stepanov/NewtonWaring.lean` | 1,048 | `fecf4b3bbc49d45947d4558bdfa501baef69903c568a3bfe664c6bbb2bc3419f` |
| `TranslationalTilings/NumberTheory/Stepanov/ArtinSchreier.lean` | 410 | `76239588e263459756f66c3a99954735a10f0e9c7c09af63bdee5b1fb493ed7c` |
| `TranslationalTilings/NumberTheory/Stepanov/HasseMultiplicity.lean` | 1,026 | `75e3d66065bb209d8509e841d42cd3c7c2c5aaea54918186be50694689f67c1f` |
| `TranslationalTilings/NumberTheory/Stepanov/TranslationProduct.lean` | 983 | `1041907da2bbc16bb482c8d13644d51b9ca3db41f4fc58b770791704c0e6fd4a` |
| `TranslationalTilings/NumberTheory/Stepanov/AdditivePointCount.lean` | 481 | `d22881870c4f14c59654073a56ce79e844b9dd83792160c9c61f22ed6dc41b8d` |
| `TranslationalTilings/NumberTheory/Stepanov/ArtinLSeries.lean` | 2,253 | `9de3e36d5e58f8bbf4e6003907f12df122aa2ddd4d88b36e6b30ed9ba9c4740c` |
| `TranslationalTilings/NumberTheory/Stepanov/ReciprocalRoots.lean` | 383 | `16c8fd3bc7fbc260f6b0d4d88a9732bd453de8305321bc1d3d526078b4940eba` |
| `TranslationalTilings/NumberTheory/PolynomialWeilBound.lean` | 125 | `77c40b5ae025a53cdb4509fd0f1b63800438942a162c4ea0139e3748334dcc34` |

The scope is 6,709 production lines. The reference and regenerated validation bytes were:

| Artifact | SHA-256 |
|---|---|
| `blueprint/05a-weil-stepanov.md` | `23f3373f2f8c6f1bc5d7ac91e541a7cbb875f039c26b478fa70608a0d99c27d5` |
| `blueprint/11-refereeing-standard.md` | `eda7b9ab79e0555878bde8157d39f14bfe1b760e8bfcbfa5861fa90ee3e7f8e5` |
| `blueprint/validation/modules/declaration-modules.tsv` | `8bd2eaabe9c99d04808fbc81d0d7ba4a78e6bdb17bc680b5b02896e922725bc6` |
| `blueprint/validation/modules/module-sources.tsv` | `77f20a932a9a5821b698691c046802e379e1962c855bb24a7934b28f8981896c` |
| `blueprint/validation/modules/generated-hashes.sha256` | `5fbaef2d6cac20c3afa1e011a4c4cc9e27cd63ab54f6bb6a5c0e0b03d1ee0142` |
| `blueprint/validation/modules/generate_modules.py` | `e9230f042900319ac1e1cbac42741531f3785f4536e14b7b2c96190afcab2337` |
| `blueprint/validation/modules/module-map.json` | `1b6353443e648f701e479e37ad797e4ba29870c00d24b83b86d5fc971042aa06` |
| `blueprint/validation/BlueprintIntegrated.lean` | `9dc79c498af10ea4ee0a0c66d98fffacb0534916e2f9ba0d2c1ae71f8a9e7d12` |
| `blueprint/validation/generate_integrated.py` | `58d9f3039e5f56bed18f424810f155d4eea12437038e8378475bbfc577646d79` |

Relevant generated module hashes are:

| Generated module | SHA-256 |
|---|---|
| `NewtonWaring.lean` | `e1202ee18f1fd93cc51a0c0fa42b29d80915ad265d28e511fd5fd37ac9920e67` |
| `ArtinSchreier.lean` | `d1201516e5fe65b2026a8e202da0a2f82ae292354887f928c547c1af9a01352c` |
| `HasseMultiplicity.lean` | `b45c7ed8f846b3118b78aba289bdd6513579bcc74d0ea2b1357fcffadeb0c31c` |
| `TranslationProduct.lean` | `abeaf0b2230b172165a87b8270efac6a964d74d3fb01f342a4fc346ff3331d17` |
| `AdditivePointCount.lean` | `a501860d9c9e71cc4b0fd5af394f4fbe3c46e3ccf892e926d1e2c3f7e012d6c3` |
| `ArtinLSeries.lean` | `b05f4fd2249817e512a4c83bb0622d07a8fdf8aa6c68fc870f3e49b6c26d4d47` |
| `ReciprocalRoots.lean` | `80271adec375b5aa7824b3e5fad4ad3b248c1748c35e29018da329e00b0ee8a7` |
| `PolynomialWeilBound.lean` | `cb70fa58ac8d282d064490b47a9fa844bd51cfbd6a4dfbe6f342f53079a25b32` |

The toolchain is Lean 4.33.0, commit
`d8b18978322de05a8f3dba51ef03cf5461676c17`, with Mathlib commit
`db584cd6d46c92f209a44c0f1c829460d327499d`. Production dependency hashes remain:

- `lean-toolchain`: `302cd63c54178885b89e669f33b38f12f4dd7ae7e5cac537b3203e3768d8fb2b`;
- `lake-manifest.json`: `fe7404c5eb045345e32beb25e6af810847e6c465af209b8b8adaa6a0fb84106f`;
- `lakefile.toml`: `f8794e06f4762d16d79699c596faf9465e18ece342b2e44df96028ac91aa914f`.

## Original findings: disposition

### P2 import/dependency finding: resolved

`HasseMultiplicity` no longer imports `NewtonWaring`. Its six direct imports are exactly the six
reported by a fresh source-appended `#min_imports` pass:

```text
Mathlib.Algebra.Order.Star.Basic
Mathlib.Data.Int.ConditionallyCompleteOrder
Mathlib.Data.Nat.Choose.Lucas
Mathlib.FieldTheory.Finite.Trace
Mathlib.LinearAlgebra.FreeModule.PID
Mathlib.RingTheory.SimpleModule.Basic
```

The repaired project DAG therefore makes Hasse derivatives and the Stepanov linear system
independent of Newton--Waring. `module-sources.tsv` records no Hasse project import and records the
three actual inputs of `TranslationProduct`.

The complete provider audit is also clean:

- `NewtonWaring` has the six semantic imports returned by `#min_imports` plus
  `Mathlib.Tactic.DeriveFintype`, the direct elaborator provider for `deriving Fintype` at line 68.
  The seventh import is intentional: `#min_imports` runs after elaboration and cannot express that
  syntax-provider dependency.
- `ArtinSchreier` has exactly its five `#min_imports` providers:
  `Finite.Basic`, `PolynomialGaloisGroup`, `RatFunc.Basic`, `DedekindDomain.Dvr`, and
  `Polynomial.IsIntegral`.
- `ArtinLSeries` has six imports and no `Mathlib.FieldTheory.Minpoly.Field`. Five are returned by
  `#min_imports`; the retained `Finite.GaloisField` import is the direct provider for the explicitly
  used `GaloisField` type and its `equivZmodP`, `finrank`, and `card` API. Keeping it avoids relying
  on accidental re-export from `Finite.Extension`.
- `TranslationProduct` directly imports `RatFunc.AsPolynomial`, `ArtinSchreier`,
  `HasseMultiplicity`, and `NewtonWaring`. A fresh `#min_imports` pass returns exactly those four.
- `AdditivePointCount` directly imports only `TranslationProduct`, exactly as reported by
  `#min_imports`.
- `ReciprocalRoots` directly imports the `Complex.Circle` and Legendre add-character providers plus
  `AdditivePointCount` and `ArtinLSeries`. A fresh `#min_imports` pass returns exactly those four.
- `PolynomialWeilBound` directly imports `Complex.CircleAddChar` and `ReciprocalRoots`, exactly as
  reported by `#min_imports`.

The resulting project edges are acyclic and flow in the intended direction:

```text
NewtonWaring
ArtinSchreier
HasseMultiplicity
TranslationProduct -> ArtinSchreier, HasseMultiplicity, NewtonWaring
AdditivePointCount -> TranslationProduct
ArtinLSeries -> NewtonWaring
ReciprocalRoots -> AdditivePointCount, ArtinLSeries
PolynomialWeilBound -> ReciprocalRoots
```

There is no downstream Chen, analysis, rigidity, or terminal import in this chain.

### P3 documentation finding: resolved

All 42 public declarations in `HasseMultiplicity` and all 39 in `ArtinLSeries` now have concise
mathematical docstrings. The former name-expansions and “identity or bound” boilerplate are absent.
The module comments now explain the Hasse/linear-algebra construction and the finite Euler-product,
Frobenius, Newton-recurrence chain respectively.

The declaration comments document actual normalizations and seam content. In particular they now
identify:

- Hasse vanishing as vanishing of derivatives through `R - 1` and relate it to multiplicity;
- the exact source and constraint dimensions, the reduced Hasse polynomial, and the nonzero kernel
  construction;
- the Artin cutoff convention, reciprocal-root multiplicities, finite local Euler factors, and
  logarithmic-derivative recurrence;
- minpoly-fiber divisibility/cardinality, its Frobenius orbit interpretation, and the degree-one
  prime-field sum bridge; and
- the negative reverse-root power-sum trace formula and the linear-polynomial zero case.

Source-appended `#lint only docBlame`, compiled through `/dev/stdin` with
`-DwarningAsError=true`, passes independently for every reviewed file. It reports zero errors in
each file. A direct phrase scan finds none of the former tautological templates.

### P3 diagnostic-suppression finding: resolved

`AdditivePointCount` contains no `linter.style.haveILetI` option and no tactic-mode `letI` or
`haveI`. The four finite-field `Fintype` bindings use ordinary `let`, as recommended by Mathlib's
Lean 4 linter. Direct warning-as-error compilation is silent.

The only remaining disabled linters in scope are the two documented Newton boundary exceptions:

- `unusedFintypeInType` preserves the blueprint's public finite-ring hypothesis;
- `unusedVariables` preserves the public constant-normalization hypothesis although the proof
  establishes a stronger cancellation theorem.

Both have adjacent explanatory comments and freeze an intentional public API. The scoped
`backward.isDefEq.respectTransparency false` options are proof-elaboration controls for
factorization and do not change the resource or trust budget.

## API and definition-body rereview

The current ledger still contains exactly 869 declaration rows. The reviewed modules own 180:
179 public declarations and the private `waringVariable`. Per module, production and ledger counts
remain 37 public Newton declarations, 22 Artin--Schreier, 42 Hasse, 26 translation-product, four
point-count, 39 Artin-L-series, six reciprocal-root, and three terminal declarations.

For all 179 public names, a fresh `#check @<qualified-name>` comparison with `pp.universes` enabled
has an empty production-versus-generated diff. Universes, binder order, binder visibility,
hypotheses, and result types are exact.

The 63 public definitions, abbreviations, and structures were rereviewed with `#print`. Their bodies
are exact. As in the initial audit, the only textual pretty-printer difference is
`tracePhaseFiberCard`: the generated definition displays its local `Fintype.ofFinite` binding while
production zeta-reduces it. A standalone example against the exact blueprint body compiles by
`rfl`, confirming definitional equality rather than propositional compatibility.

No new public declaration, accidental export, moved owner, or changed theorem statement was found.

## Build, diagnostics, resources, and trust

All eight direct production commands

```text
lake env lean -DwarningAsError=true <file>
```

exit zero with no output. In the parallel replay their wall times were 9.32s (Newton), 7.18s
(Artin--Schreier), 20.10s (Hasse), 10.40s (translation product), 11.50s (point count), 12.89s
(Artin L-series), 9.55s (reciprocal roots), and 10.56s (terminal). The joint production build passes:

```text
Build completed successfully (3266 jobs).
```

A terminal compile with both `-Ddiagnostics=true` and `-DwarningAsError=true` passes. It reports no
pending-synthesis failure or resource exhaustion. The largest displayed imported typeclass counter
is 1,048, within the default project budget. The sources contain no `maxHeartbeats` or
`maxRecDepth`; no enlarged resource setting was used. No production line in the eight files exceeds
100 characters.

The exact forbidden scan is empty for:

```text
sorry admit axiom unsafe placeholder opaque native_decide
BlueprintModuleValidation maxHeartbeats maxRecDepth
```

Fresh `#print axioms` output was parsed for exactly all 179 public declarations. The complete axiom
union is:

```text
Classical.choice
Quot.sound
propext
```

No project axiom, validator axiom, or unexpected trust dependency appears.

## Validation freshness

After the repaired dependency graph was regenerated, every freshness gate passes:

```text
python3 blueprint/validation/modules/generate_modules.py --check
# module validation current: 29 modules; 869 declarations; DAG acyclic

python3 blueprint/validation/generate_integrated.py --check

sha256sum -c blueprint/validation/modules/generated-hashes.sha256
# all 38 entries OK
```

A fresh build of the standalone generated package completes successfully with 3,446 jobs. The
generated signature sources emit their known long-line diagnostics; those are generated-validator
formatting diagnostics, not production diagnostics, and the hash manifest records the exact bytes.

## Library-referee assessment

1. **Mathematical intent:** unchanged and faithful to the approved chapter.
2. **Reusable seams:** Newton, Artin--Schreier, Hasse, translation descent, point count, finite
   L-series, reciprocal roots, and terminal Weil result are now separated along true dependencies.
3. **Public API:** exact for all 179 public ledger declarations.
4. **Dependency design:** clean, acyclic, and provider-explicit; the original false edge is gone.
5. **Mathlib integration:** direct providers and existing polynomial, finite-field, trace, minpoly,
   rank-nullity, circle, and norm infrastructure are used appropriately.
6. **Proof architecture:** the finite recurrences and explicit transports remain intact; no proof
   was weakened during import or documentation repair.
7. **Cost and durability:** default-budget builds are clean, semantic imports are small, and direct
   syntax/declaration providers protect against transitive-import churn.
8. **Refactor risk:** no further refactor is recommended at this milestone. Preserve the exact API,
   finite Euler recurrence, Galois shift proof, translation-product block induction, and direct
   degree-one sum bridge.

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
  TranslationalTilings/NumberTheory/Stepanov/{NewtonWaring,ArtinSchreier,HasseMultiplicity,TranslationProduct,AdditivePointCount,ArtinLSeries,ReciprocalRoots}.lean \
  TranslationalTilings/NumberTheory/PolynomialWeilBound.lean

rg -n 'linter\.style\.haveILetI|\bletI\b|\bhaveI\b' \
  TranslationalTilings/NumberTheory/Stepanov/AdditivePointCount.lean
```

For each file, the doc and minimum-import checks were performed without editing it:

```bash
awk '1; END { print ""; print "#lint only docBlame" }' "$file" |
  lake env lean -DwarningAsError=true /dev/stdin

awk '1; END { print ""; print "#min_imports" }' "$file" |
  lake env lean /dev/stdin
```

Run validation commands from `/home/codex/Documents/Codex/2026-08-24/usi`:

```bash
python3 blueprint/validation/modules/generate_modules.py --check
python3 blueprint/validation/generate_integrated.py --check
sha256sum -c blueprint/validation/modules/generated-hashes.sha256

cd blueprint/validation/modules/BlueprintModuleValidation
lake build
```

The API/body and axiom checks were generated from the reviewed rows of
`declaration-modules.tsv`. API types were compared with `#check @name` and `pp.universes`; public
definition bodies were compared with `#print`; trust was checked with one `#print axioms name` per
public declaration. No validator module was imported into production.

## Acceptance statement

The eight repaired production hashes at the top of this report satisfy the PM6 Tau-Ceti-style
follow-up gate. The original P2 and two P3 findings are closed, and there is no remaining P0--P3
finding in scope. This snapshot is accepted without qualification.
