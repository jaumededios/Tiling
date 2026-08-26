# Final production mathematical snapshot review

Date: 2026-08-24 UTC

## Verdict

**APPROVE.** I found zero unresolved P0, P1, P2, or P3 findings in the
content-addressed snapshot reviewed below. The paper-facing statements,
hypotheses, quantifiers, definitions, recursive closures, algorithms, cost
recurrences, and genuine production proof bodies are mathematically coherent
and faithful to arXiv:2010.03254v3. Generated validator axioms were used only
as signature and module-boundary evidence, never as proof evidence.

Finding counts: P0 = 0, P1 = 0, P2 = 0, P3 = 0.

## Immutable snapshot binding

- Manifest: `blueprint/SNAPSHOT.sha256`
- Manifest SHA-256:
  `482c18adc1fcdb3865454bd50471cb075d662ceac4ee84f35b607a38cbfa7ae3`
- Manifest entries: exactly 95
- Full `sha256sum -c blueprint/SNAPSHOT.sha256`: PASS before this review
  artifact was written. A second full 95-entry check is required after the
  final bytes of this artifact are written and is reported in the handoff.
- Paper PDF SHA-256:
  `2a3f035bb13718e47087a27233f5339ed8feb9fe8dabccb9dec93a95fae2a0a9`
- Complete 28-page extracted paper text SHA-256:
  `f96210a8b969695c9892301e9efb8c6fc3c6f4560fc3fce6eb38aa7f7db60159`
- Production repository HEAD (environmental identifier, not the snapshot
  identity): `b6744348ec0c2ab44788000b031721b861424c2f`.
- The production checkout was already dirty and the reviewed
  `TranslationalTilings` tree was untracked by that HEAD. Consequently the
  authoritative identity is the manifest's 33 production payload hashes,
  not Git status. The SHA-256 of the exact 33 production lines in the
  manifest is
  `52c54b8332c5cb869da9d9d2f165071850b6ce6bd6128f692007af1d7e0ea401`.

### Production payload hashes

| SHA-256 | Manifest path |
|---|---|
| `652c9cb48810aa1f7634bcabb2bb0bcaf3b86c4eb14ece52f1596731cd68930b` | `../../2026-08-14/Tiling/TranslationalTilings/Algorithms.lean` |
| `7b1cc96f97a7989e50faef41ce780d9a9a851d6ffc75b3c8e1aba21196af81ee` | `../../2026-08-14/Tiling/TranslationalTilings/Analysis/CirclePolynomial.lean` |
| `758ea5803e08367dfb94dd2908569eac12180fb8f4f1edbd2414b561c726c66d` | `../../2026-08-14/Tiling/TranslationalTilings/Analysis/Equidistribution.lean` |
| `d6d561da1f2ec6c306b883fc6768cce4df2e415b65c36e37a9fa9ad8f6639cfa` | `../../2026-08-14/Tiling/TranslationalTilings/Analysis/FejerSeparator.lean` |
| `da6d870c5720242a9e1a6840596135f2e0e0e952f254bca790c5feeb36a213d6` | `../../2026-08-14/Tiling/TranslationalTilings/Analysis/PolynomialRigidity.lean` |
| `4188eb7bfebf6a25a845c4470299a573fcf8b8b8c8532a8e09184fa25e7d2f24` | `../../2026-08-14/Tiling/TranslationalTilings/Arithmetic.lean` |
| `5d55253056ad40eea94ed3e31e02a62b0eb459845c9f23cc71464ae8ed786560` | `../../2026-08-14/Tiling/TranslationalTilings/Basic.lean` |
| `71435b6b23418bdeadf0e48df98caca03cf8b8970c6bcea5c4e2e59df1f7f6ff` | `../../2026-08-14/Tiling/TranslationalTilings/Counterexample.lean` |
| `b998f477ff1095a077346a02f622390a638c087da50f08bb77eeef360e9381b8` | `../../2026-08-14/Tiling/TranslationalTilings/Dilation/Periodic.lean` |
| `abedb559631364444c99e4ace0f9062b64bff2c78e7315b9fc004b17f4750f1d` | `../../2026-08-14/Tiling/TranslationalTilings/FiniteDifference.lean` |
| `4e4ea6f66ad47ec41c14a19aa8965458e4b764db0c6e82aa275ef568f4660a7c` | `../../2026-08-14/Tiling/TranslationalTilings/LatticeGeometry.lean` |
| `410366b9f079319164e0ba73c15b1a83d2902a39c6c838cf09b6fa567b742536` | `../../2026-08-14/Tiling/TranslationalTilings/Main.lean` |
| `df9fc411e36e60c1e0affba9945800304297a77d23b01adec5edc47777bec0ec` | `../../2026-08-14/Tiling/TranslationalTilings/NumberTheory/ChenCompleteSum.lean` |
| `49cb393764e53f1e89f373ca09245bb6fbd88fe858e8c77215d463f4da35098c` | `../../2026-08-14/Tiling/TranslationalTilings/NumberTheory/CompleteExponentialSum.lean` |
| `cbecf502eb898bd02255f2d8ae80263631bde43b6753602b4bcef3c231e3cb29` | `../../2026-08-14/Tiling/TranslationalTilings/NumberTheory/FiniteCyclicPhase.lean` |
| `44ddee5cecaa18226fdc2379631c2134e63f4e8b0e4fb4a1e863801dac08b764` | `../../2026-08-14/Tiling/TranslationalTilings/NumberTheory/PolynomialCongruence.lean` |
| `77c40b5ae025a53cdb4509fd0f1b63800438942a162c4ea0139e3748334dcc34` | `../../2026-08-14/Tiling/TranslationalTilings/NumberTheory/PolynomialWeilBound.lean` |
| `b862d62a458d1a278aa03659c0ed58c2f4e958d068b63c7040419e74dbab7ccd` | `../../2026-08-14/Tiling/TranslationalTilings/NumberTheory/QuadraticCompleteSum.lean` |
| `d22881870c4f14c59654073a56ce79e844b9dd83792160c9c61f22ed6dc41b8d` | `../../2026-08-14/Tiling/TranslationalTilings/NumberTheory/Stepanov/AdditivePointCount.lean` |
| `9de3e36d5e58f8bbf4e6003907f12df122aa2ddd4d88b36e6b30ed9ba9c4740c` | `../../2026-08-14/Tiling/TranslationalTilings/NumberTheory/Stepanov/ArtinLSeries.lean` |
| `76239588e263459756f66c3a99954735a10f0e9c7c09af63bdee5b1fb493ed7c` | `../../2026-08-14/Tiling/TranslationalTilings/NumberTheory/Stepanov/ArtinSchreier.lean` |
| `75e3d66065bb209d8509e841d42cd3c7c2c5aaea54918186be50694689f67c1f` | `../../2026-08-14/Tiling/TranslationalTilings/NumberTheory/Stepanov/HasseMultiplicity.lean` |
| `fecf4b3bbc49d45947d4558bdfa501baef69903c568a3bfe664c6bbb2bc3419f` | `../../2026-08-14/Tiling/TranslationalTilings/NumberTheory/Stepanov/NewtonWaring.lean` |
| `16c8fd3bc7fbc260f6b0d4d88a9732bd453de8305321bc1d3d526078b4940eba` | `../../2026-08-14/Tiling/TranslationalTilings/NumberTheory/Stepanov/ReciprocalRoots.lean` |
| `1041907da2bbc16bb482c8d13644d51b9ca3db41f4fc58b770791704c0e6fd4a` | `../../2026-08-14/Tiling/TranslationalTilings/NumberTheory/Stepanov/TranslationProduct.lean` |
| `50042b2e2a33b99a340f49373d2e36b0dae7bd3e234171d7f1134056170504d6` | `../../2026-08-14/Tiling/TranslationalTilings/PeriodicCompletion.lean` |
| `d4ddf872b1bcc6d745736a6fe3abe9ed33294b8367292a23f9d2d0ea179afb64` | `../../2026-08-14/Tiling/TranslationalTilings/Slicing.lean` |
| `76810941f6c1e7ba1eed109b2b7731b14f5df8981002e2b802023f8b97527b2e` | `../../2026-08-14/Tiling/TranslationalTilings/Structure/Grouped.lean` |
| `249885c54a6d1db40c048d7be2f39d3bb91a6ffe4469e76b713f2de4d188d950` | `../../2026-08-14/Tiling/TranslationalTilings/WeakPeriodicity.lean` |
| `878d8516314a945acc9f2a2bda96f4c0ece894e5f66960ad6fc9c6033a40866c` | `../../2026-08-14/Tiling/TranslationalTilings.lean` |
| `f8794e06f4762d16d79699c596faf9465e18ece342b2e44df96028ac91aa914f` | `../../2026-08-14/Tiling/lakefile.toml` |
| `302cd63c54178885b89e669f33b38f12f4dd7ae7e5cac537b3203e3768d8fb2b` | `../../2026-08-14/Tiling/lean-toolchain` |
| `fe7404c5eb045345e32beb25e6af810847e6c465af209b8b8adaa6a0fb84106f` | `../../2026-08-14/Tiling/lake-manifest.json` |

## Scope and review method

I read arXiv:2010.03254v3 completely, including every theorem and the full
proof chain through Sections 2--6. I then read all 17 manifest-listed
blueprint/review payloads, all 45 manifest-listed validator payloads, and all
29 genuine production modules plus the production umbrella. The validator
set comprises 869 declarations across 29 generated modules; its bodyless
theorem axioms were checked solely for exact public types, ownership,
imports, and dependency acyclicity. Every mathematical conclusion below was
checked against handwritten production bodies.

The audit followed definitions through their actual consumers rather than
stopping at paper aliases. It checked hypothesis direction, positivity and
nonemptiness conditions, finite-index/coset quantifiers, recursive descent
invariants, CRT support, field/ring assumptions, degree estimates,
multiplicity accounting, and both directions of each executable
classification theorem.

## Mathematical audit

| Area | Direct production evidence checked | Conclusion |
|---|---|---|
| Singleton completion and Theorem 5.4 | `singleton_tile_periodic_completion`, `improve_weaklyPeriodic`, `improve_weaklyPeriodic_exact`, `improve_weaklyPeriodic_structural`, and the three `theorem_5_4` endpoints | The singleton branch constructs the unique translated target complement with multiplier 1. Exact certificates retain the necessary non-singleton hypothesis; the general and structural results dispatch singleton separately. This is compatible with the paper's `m >= 2` completion argument and closes the API endpoint honestly. |
| Support-indexed Chen factorization | `FactorizationScalar`, its support lookup lemmas, CRT assembly, global factorization, and all finite-product consumers | Scalars are indexed only by prime support. For `q = 1` the support is empty, the complete sum and empty product are both 1, and scalar uniqueness is valid. No nonexistent prime-factor coordinate is demanded. |
| Weil multiplicativity domain | `Stepanov.monicWeight_mul` and its Newton/Waring and reciprocal-root consumers | The theorem is correctly stated over a `Field`, where the no-zero-divisor step used in the proof is available. No stronger multiplicativity is exported over a semiring with zero divisors. |
| PM1/PM2 ownership | Conditional Chen `_of_primeBound` declarations, terminal `polynomialPrimeSumBound`, unconditional Chen wrappers, local quadratic prime-power theorems, and terminal composite quadratic wrappers | The dependency join is acyclic and mathematically honest: Chen owns conditional recursion; `CompleteExponentialSum` owns the Weil-dependent unconditional results and the Chen-dependent composite quadratic results. |
| ACK (2.10) | `ack_ineq_2_10`, its call to the (2.6) recursion, and every terminal caller | The upper-range premise `hpB` required by the recursive child is explicit and supplied exactly in the middle-prime branch. No hidden strengthening remains. |
| PM4 target periodicity | `coset_one_dimensional_periodicity`, `proposition_4_4`, quantitative weak-period construction, periodic completion, and Algorithms callers | The used hypothesis `hE : SetScalarPeriodic ell E` is explicit at the core theorem and paper alias, and every caller passes it. The formerly false raw-decomposition signature is gone. |
| Stepanov/Artin/Weil chain | Hasse multiplicities, dimension parameters, translation-product nonvanishing, additive point count, Artin--Schreier irreducibility, Artin L-series recurrences, reciprocal-root bounds, Newton/Waring identities, and `polynomialPrimeSumBound` | The proof chain is genuine. Degree and multiplicity bounds match the chosen parameters; trace identities and translation norms are used at the correct fields; reciprocal roots yield the advertised prime complete-sum estimate. Degree-one and small-character endpoints are separated explicitly. |
| Complete sums and parity endpoints | Linear sums, odd-prime quadratic completion, odd prime-power and two-power recurrences, `q = 1`, modulus 2, even/odd linear coefficient branches, Chen small/middle/large prime recursion, and global finite products | All base cases and recurrence hypotheses are present. Quadratic parity behavior is exact, and the final Stechkin majorant follows from the local factors without assuming a missing factorization theorem. |
| Counterexample | Explicit eight-element tile, three cancellation directions, level-four convolution identity, irrational fractional-part range, and the contradiction to any finite weak-periodic union | The level-four tiling and failure of weak periodicity are proved for the displayed set, not postulated. The cardinality is exactly eight. |
| Weak periodicity | Grouped structure data, circle-polynomial rigidity, canonical primitive directions, coset periodicity, quantitative index/multiplier bounds, and the main weak-period theorem | The finite-difference, equidistribution, Fejer separator, and complete-sum arguments feed the structural decomposition with the correct nonzero-direction and positive-period facts. Pairwise incommensurability and all coset quantifiers are retained. |
| Algorithms and costs | Periodic codes, representative tuples, finite line checks, pattern decoder, chameleon iff theorem, directional assembly, two-chameleon nonperiodicity, at-most-one periodicity, normalisation, HNF wrapper, and every counted search recurrence/closed bound | The executable predicates are proved equivalent to the semantic predicates. Forward assembly and converse classification are both present. Two nonparallel modified directions rule out every nonzero global period; zero or one modified direction yields a common period. Counted costs match their recursive definitions and close to the stated elementary bounds. |

Endpoint audit included empty tiles, empty targets, singleton tiles, constant and
degree-zero circle polynomials, linear and quadratic phases, modulus one,
modulus two, empty factor support, zero direction count, one decomposition
part, multiple parts, and normalized versus unnormalized/lattice-input
classifier entry points. No endpoint is discharged by an inconsistent or
vacuous premise.

## Verification record

The following checks passed against the bound bytes:

1. `sha256sum blueprint/SNAPSHOT.sha256` and `wc -l` produced the exact
   manifest SHA and 95 entries; `sha256sum -c blueprint/SNAPSHOT.sha256`
   passed every entry.
2. `python3 blueprint/validation/generate_integrated.py --check` passed.
3. Strict elaboration of `blueprint/validation/BlueprintIntegrated.lean`
   passed with `relaxedAutoImplicit=false`, `maxSynthPendingDepth=3`, and
   `maxErrors=1000`.
4. `python3 blueprint/validation/modules/generate_modules.py --check` passed,
   reporting 29 modules, 869 declarations, and an acyclic DAG.
5. `sha256sum -c blueprint/validation/modules/generated-hashes.sha256`
   passed, and `generate_modules.py --build` completed successfully.
6. In the genuine production checkout, `lake query TranslationalTilings`,
   `lake build TranslationalTilings`, and
   `lake build Tiling TranslationalTilings` completed successfully.
7. Every one of the 29 genuine `TranslationalTilings/**/*.lean` modules and
   `TranslationalTilings.lean` elaborated individually under
   `warningAsError=true`, `relaxedAutoImplicit=false`, and
   `maxSynthPendingDepth=3`.
8. A trust scan found no `sorry`, `admit`, production `axiom`, `opaque`,
   `unsafe`, or import of either validator tree in the reviewed production
   sources. Endpoint `#print axioms` queries for Theorems 1.3--1.7,
   Proposition 4.4, all Theorem 5.4 variants, Theorem 6.2, the prime Weil
   bound, the global complete-sum theorem, and the classifier correctness
   theorem reported only `propext`, `Classical.choice`, and `Quot.sound`.
9. A concrete production `#eval` of
   `nonOnePeriodicTilingDecision` on the empty-tile endpoint returned
   `false`, agreeing with the proved degenerate branch.

The joint legacy-target build replayed a pre-existing `sorry` warning in
`Tiling/Geometry/Plate.lean`. That file is outside all 95 manifest entries,
is not imported by `TranslationalTilings`, and is not in this review's trust
boundary. It therefore does not alter this content-addressed verdict.

## Final assessment

The current snapshot resolves every named repair zone without weakening the
paper endpoints or shifting an unproved obligation into validator axioms.
There is no minimal repair to request: the final mathematical verdict is
**APPROVE** with zero unresolved blocking findings.

The SHA-256 of this report itself is necessarily computed after its final
bytes are fixed and is supplied together with the post-write 95-payload
verification in the review handoff.
