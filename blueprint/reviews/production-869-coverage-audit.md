# Production 869-row coverage and trust audit

Date: 2026-08-24 UTC.  Verdict: **PASS**, with one explicitly out-of-scope
pre-existing trust finding in the separate `Tiling` library.

## Scope and reviewer disclosure

This is a mechanical production coverage, exact-type, and trust audit of the
29-module `TranslationalTilings` library against the regenerated 869-row
`blueprint/validation/modules/declaration-modules.tsv` ledger.  It is not a
mathematical proof review.

The auditing agent is also the production author of
`PolynomialCongruence.lean` and `ChenCompleteSum.lean`.  In particular, this
report is **not independent evidence for the mathematical correctness of the
Chen proofs**.  Those files have separate independent reviews.  Validator-only
axiom stubs are used here solely as expected type signatures and are never
counted as production proof evidence.

The production worktree is intentionally dirty and uncommitted at base commit
`b6744348ec0c2ab44788000b031721b861424c2f`.  The audit binds its conclusions to
the exact source hashes listed below, not to the branch name.

## Method and commands

The audit harness was created and run only under `/tmp`; it did not edit any
manifest-listed production or blueprint source.  The principal commands were:

```bash
cd /home/codex/Documents/Codex/2026-08-24/usi
python3 -m py_compile /tmp/production_coverage_audit.py
python3 /tmp/production_coverage_audit.py
```

For each module in manifest topological order, the harness removed the
production `.lake/build/lib/lean` directory from `LEAN_PATH`, compiled the
current source bytes into an isolated `/tmp` olean tree with the project
options and `-DwarningAsError=true`, and imported that isolated olean
individually.  Thus a stale project olean could not hide a source failure.  A
separate isolated tree compiled the generated validator modules.

For every addressable ledger name, Lean environment inspection checked
presence and dumped the fully explicit elaborated type (`pp.all` and
universes).  Textual differences were re-elaborated as expected signatures in
the production environment and adjudicated with `Meta.isDefEq`.  A separate
production-only file ran `#print axioms` for every addressable name.  The
validator package was not imported into that trust check.

The final source hashes were compared both at audit start/end and once more
after the audit.  The post-audit result was:

```text
POST_AUDIT_HASH_DRIFT 0
```

The one supplemental CirclePolynomial adjudication was run against the exact
frozen production olean with:

```bash
cd /home/codex/Documents/Codex/2026-08-14/Tiling
base=$(lake env printenv LEAN_PATH | sed 's#:/home/codex/Documents/Codex/2026-08-14/Tiling/.lake/build/lib/lean##')
LEAN_PATH=/tmp/production_coverage_audit_20260824T161917Z_966414/production-olean:$base \
  $(lake env which lean) \
  -Dpp.unicode.fun=true -DrelaxedAutoImplicit=false \
  -Dweak.linter.mathlibStandardSet=true -DmaxSynthPendingDepth=3 \
  -DwarningAsError=true /tmp/TestCircleDefEq.lean
```

It produced:

```text
AUDIT_DEFEQ	TranslationalTilings.normalized_completeSum_repeat_zero_regression	true
```

## Result

- 29/29 production modules compile strictly from current source bytes.
- 869/869 ledger rows are accounted for.
- 858/858 addressable public declarations are present.
- 858/858 addressable public declarations have the expected exact elaborated
  type, including differences discharged only after same-environment
  definitional-equality checking.
- 11/11 nonaddressable rows are accounted for by strict source compilation:
  one private declaration, one anonymous CirclePolynomial declaration, and
  nine anonymous Algorithms declarations.
- Every production axiom report parsed successfully.  The only dependencies
  found were the accepted kernel axioms `propext`, `Classical.choice`, and
  `Quot.sound`; there were zero unexpected axioms and zero parse gaps.
- There are zero imports from `BlueprintModuleValidation`,
  `BlueprintIntegrated`, either validator tree, or a `Validator` module.
- The production source scan found no `axiom`, `admit`, `unsafe`,
  `native_decide`, `implemented_by`, `maxHeartbeats`, or `maxRecDepth` token.
  It found 27 occurrences of the project-standard
  `set_option maxSynthPendingDepth 3` and no resource escape.
- No retained `#lint`, `#check`, or `#print` command occurs in the
  `TranslationalTilings` production sources.
- No source changed during the audit, and the post-audit rehash of all 29
  modules found zero drift.

The adjudicated per-module coverage is:

| Module | Rows | Public | Nonaddressable | Strict | Exact types | Missing | Unexpected axioms |
|---|---:|---:|---:|:---:|---:|---:|---:|
| `TranslationalTilings.Basic` | 36 | 36 | 0 | yes | 36 | 0 | 0 |
| `TranslationalTilings.FiniteDifference` | 15 | 15 | 0 | yes | 15 | 0 | 0 |
| `TranslationalTilings.Arithmetic` | 23 | 23 | 0 | yes | 23 | 0 | 0 |
| `TranslationalTilings.LatticeGeometry` | 41 | 41 | 0 | yes | 41 | 0 | 0 |
| `TranslationalTilings.Dilation.Periodic` | 19 | 19 | 0 | yes | 19 | 0 | 0 |
| `TranslationalTilings.Structure.Grouped` | 8 | 8 | 0 | yes | 8 | 0 | 0 |
| `TranslationalTilings.Counterexample` | 25 | 25 | 0 | yes | 25 | 0 | 0 |
| `TranslationalTilings.NumberTheory.Stepanov.NewtonWaring` | 38 | 37 | 1 | yes | 37 | 0 | 0 |
| `TranslationalTilings.NumberTheory.Stepanov.ArtinLSeries` | 39 | 39 | 0 | yes | 39 | 0 | 0 |
| `TranslationalTilings.NumberTheory.Stepanov.ArtinSchreier` | 22 | 22 | 0 | yes | 22 | 0 | 0 |
| `TranslationalTilings.NumberTheory.Stepanov.HasseMultiplicity` | 42 | 42 | 0 | yes | 42 | 0 | 0 |
| `TranslationalTilings.NumberTheory.Stepanov.TranslationProduct` | 26 | 26 | 0 | yes | 26 | 0 | 0 |
| `TranslationalTilings.NumberTheory.Stepanov.AdditivePointCount` | 4 | 4 | 0 | yes | 4 | 0 | 0 |
| `TranslationalTilings.NumberTheory.Stepanov.ReciprocalRoots` | 6 | 6 | 0 | yes | 6 | 0 | 0 |
| `TranslationalTilings.NumberTheory.PolynomialWeilBound` | 3 | 3 | 0 | yes | 3 | 0 | 0 |
| `TranslationalTilings.NumberTheory.FiniteCyclicPhase` | 17 | 17 | 0 | yes | 17 | 0 | 0 |
| `TranslationalTilings.NumberTheory.PolynomialCongruence` | 30 | 30 | 0 | yes | 30 | 0 | 0 |
| `TranslationalTilings.NumberTheory.ChenCompleteSum` | 60 | 60 | 0 | yes | 60 | 0 | 0 |
| `TranslationalTilings.NumberTheory.QuadraticCompleteSum` | 19 | 19 | 0 | yes | 19 | 0 | 0 |
| `TranslationalTilings.NumberTheory.CompleteExponentialSum` | 20 | 20 | 0 | yes | 20 | 0 | 0 |
| `TranslationalTilings.Analysis.CirclePolynomial` | 39 | 38 | 1 | yes | 38 | 0 | 0 |
| `TranslationalTilings.Analysis.Equidistribution` | 17 | 17 | 0 | yes | 17 | 0 | 0 |
| `TranslationalTilings.Analysis.FejerSeparator` | 7 | 7 | 0 | yes | 7 | 0 | 0 |
| `TranslationalTilings.Analysis.PolynomialRigidity` | 12 | 12 | 0 | yes | 12 | 0 | 0 |
| `TranslationalTilings.WeakPeriodicity` | 63 | 63 | 0 | yes | 63 | 0 | 0 |
| `TranslationalTilings.Slicing` | 16 | 16 | 0 | yes | 16 | 0 | 0 |
| `TranslationalTilings.PeriodicCompletion` | 47 | 47 | 0 | yes | 47 | 0 | 0 |
| `TranslationalTilings.Algorithms` | 145 | 136 | 9 | yes | 136 | 0 | 0 |
| `TranslationalTilings.Main` | 30 | 30 | 0 | yes | 30 | 0 | 0 |

## CirclePolynomial raw false positive

The raw report recorded one apparent mismatch for
`normalized_completeSum_repeat_zero_regression`.  The expected fully explicit
type contains a layout-sensitive `let`.  The initial `/tmp` expected-axiom
generator preserved the pretty-printed text but not its continuation
indentation, so Lean rejected that generated axiom and the harness recorded the
failed comparison as `false`.  This was an audit-tool defect, not a production
or blueprint defect.

The raw report remains preserved.  The harness was corrected only in `/tmp` to
parenthesize and indent the expected type; the supplemental checker against the
same frozen production olean returned `isDefEq = true`.  The adjudicated
coverage and discrepancy files record the corrected result.

## Discrepancy ledger

There is no `TranslationalTilings` ledger coverage, exact-type, strict-build,
validator-import, or production-axiom discrepancy.

The whole-production-tree token scan additionally found:

| Scope | File | Line | Token | Disposition |
|---|---|---:|---|---|
| Outside the 29-module ledger | `Tiling/Geometry/Plate.lean` | 125 | `sorry` | Pre-existing and unrelated; reported, not edited, and not counted as proof evidence for `TranslationalTilings`. |

## Frozen production hashes

```text
652c9cb48810aa1f7634bcabb2bb0bcaf3b86c4eb14ece52f1596731cd68930b  TranslationalTilings.Algorithms
7b1cc96f97a7989e50faef41ce780d9a9a851d6ffc75b3c8e1aba21196af81ee  TranslationalTilings.Analysis.CirclePolynomial
758ea5803e08367dfb94dd2908569eac12180fb8f4f1edbd2414b561c726c66d  TranslationalTilings.Analysis.Equidistribution
d6d561da1f2ec6c306b883fc6768cce4df2e415b65c36e37a9fa9ad8f6639cfa  TranslationalTilings.Analysis.FejerSeparator
da6d870c5720242a9e1a6840596135f2e0e0e952f254bca790c5feeb36a213d6  TranslationalTilings.Analysis.PolynomialRigidity
4188eb7bfebf6a25a845c4470299a573fcf8b8b8c8532a8e09184fa25e7d2f24  TranslationalTilings.Arithmetic
5d55253056ad40eea94ed3e31e02a62b0eb459845c9f23cc71464ae8ed786560  TranslationalTilings.Basic
71435b6b23418bdeadf0e48df98caca03cf8b8970c6bcea5c4e2e59df1f7f6ff  TranslationalTilings.Counterexample
b998f477ff1095a077346a02f622390a638c087da50f08bb77eeef360e9381b8  TranslationalTilings.Dilation.Periodic
abedb559631364444c99e4ace0f9062b64bff2c78e7315b9fc004b17f4750f1d  TranslationalTilings.FiniteDifference
4e4ea6f66ad47ec41c14a19aa8965458e4b764db0c6e82aa275ef568f4660a7c  TranslationalTilings.LatticeGeometry
410366b9f079319164e0ba73c15b1a83d2902a39c6c838cf09b6fa567b742536  TranslationalTilings.Main
df9fc411e36e60c1e0affba9945800304297a77d23b01adec5edc47777bec0ec  TranslationalTilings.NumberTheory.ChenCompleteSum
49cb393764e53f1e89f373ca09245bb6fbd88fe858e8c77215d463f4da35098c  TranslationalTilings.NumberTheory.CompleteExponentialSum
cbecf502eb898bd02255f2d8ae80263631bde43b6753602b4bcef3c231e3cb29  TranslationalTilings.NumberTheory.FiniteCyclicPhase
44ddee5cecaa18226fdc2379631c2134e63f4e8b0e4fb4a1e863801dac08b764  TranslationalTilings.NumberTheory.PolynomialCongruence
77c40b5ae025a53cdb4509fd0f1b63800438942a162c4ea0139e3748334dcc34  TranslationalTilings.NumberTheory.PolynomialWeilBound
b862d62a458d1a278aa03659c0ed58c2f4e958d068b63c7040419e74dbab7ccd  TranslationalTilings.NumberTheory.QuadraticCompleteSum
d22881870c4f14c59654073a56ce79e844b9dd83792160c9c61f22ed6dc41b8d  TranslationalTilings.NumberTheory.Stepanov.AdditivePointCount
9de3e36d5e58f8bbf4e6003907f12df122aa2ddd4d88b36e6b30ed9ba9c4740c  TranslationalTilings.NumberTheory.Stepanov.ArtinLSeries
76239588e263459756f66c3a99954735a10f0e9c7c09af63bdee5b1fb493ed7c  TranslationalTilings.NumberTheory.Stepanov.ArtinSchreier
75e3d66065bb209d8509e841d42cd3c7c2c5aaea54918186be50694689f67c1f  TranslationalTilings.NumberTheory.Stepanov.HasseMultiplicity
fecf4b3bbc49d45947d4558bdfa501baef69903c568a3bfe664c6bbb2bc3419f  TranslationalTilings.NumberTheory.Stepanov.NewtonWaring
16c8fd3bc7fbc260f6b0d4d88a9732bd453de8305321bc1d3d526078b4940eba  TranslationalTilings.NumberTheory.Stepanov.ReciprocalRoots
1041907da2bbc16bb482c8d13644d51b9ca3db41f4fc58b770791704c0e6fd4a  TranslationalTilings.NumberTheory.Stepanov.TranslationProduct
50042b2e2a33b99a340f49373d2e36b0dae7bd3e234171d7f1134056170504d6  TranslationalTilings.PeriodicCompletion
d4ddf872b1bcc6d745736a6fe3abe9ed33294b8367292a23f9d2d0ea179afb64  TranslationalTilings.Slicing
76810941f6c1e7ba1eed109b2b7731b14f5df8981002e2b802023f8b97527b2e  TranslationalTilings.Structure.Grouped
249885c54a6d1db40c048d7be2f39d3bb91a6ffe4469e76b713f2de4d188d950  TranslationalTilings.WeakPeriodicity
```

## Evidence hashes

```text
8bd2eaabe9c99d04808fbc81d0d7ba4a78e6bdb17bc680b5b02896e922725bc6  declaration-modules.tsv
77f20a932a9a5821b698691c046802e379e1962c855bb24a7934b28f8981896c  module-sources.tsv
5fbaef2d6cac20c3afa1e011a4c4cc9e27cd63ab54f6bb6a5c0e0b03d1ee0142  generated-hashes.sha256
1b6353443e648f701e479e37ad797e4ba29870c00d24b83b86d5fc971042aa06  module-map.json
878c8dd0167620c892fa0bfd298521d8d50c274cbb48452515c1e417db1579c5  /tmp/production_coverage_audit_20260824T161917Z_966414/report.json
f2d3a1b63f8fa0646376a019ea554d50d33e506e989668bb436ece519aa79175  /tmp/production_coverage_audit_20260824T161917Z_966414/coverage.tsv
e153d3e659d7da94762a12e6fe5139cb054997522a114dee755ceb3d8f927ae9  /tmp/production_coverage_audit_20260824T161917Z_966414/discrepancies.tsv
3041330b6ec673f31232f13f5fc1612aea17c27e159e4cbcc0912c3d5f16ffef  /tmp/production_coverage_audit_20260824T161917Z_966414/coverage-adjudicated.tsv
0855ef0831182722f1b5fc4babf5e77cfde05da6ea189bd8453f15aa5ed9d943  /tmp/production_coverage_audit_20260824T161917Z_966414/discrepancies-adjudicated.tsv
bab3dbd4bdd3e76e4109cd864b2d361c469a2fa4e5b8989300dbfb64b713dd46  /tmp/production_coverage_audit_20260824T161917Z_966414/adjudication.md
abccd13c4e82f294325ed047b3c870b9f8787232f3bde7db92b4a12cfbf600d7  /tmp/TestCircleDefEq.lean
a32a4afa35f4ee74477cec402c25dd940ad1ccab313ac334b251684f725d1780  /tmp/production_coverage_audit.py
```
