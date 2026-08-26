# Frozen Chen/terminal production referee audit

Date: 2026-08-24

Reviewer task: Tau-Ceti-style, read-only production audit of the conditional Chen boundary and the terminal complete-exponential-sum join. The review applied both the library-scale and local-proof rubrics. Under the audit mandate, every P0--P3 finding is blocking.

## Snapshot and scope

The reviewed production bytes were:

- `TranslationalTilings/NumberTheory/ChenCompleteSum.lean`: SHA-256 `a1671beb23762d7a57d2e1856bf9eb330587b5725da6d0af1b241580a659d311` (3,994 lines).
- `TranslationalTilings/NumberTheory/CompleteExponentialSum.lean`: SHA-256 `419af2ef7200228488dd004d543a8ef4577bcb39caf5e8a71e6ee42e41fa7ae9` (524 lines).

The reference bytes were:

- `blueprint/05b-chen-complete-sums.md`: `81b1799e2e08cdaa6639df75a16e15fb3c415793ee04f52cc3cdd2def5dd15a3`.
- `blueprint/validation/modules/declaration-modules.tsv`: `1ced9cce08d0db519eb8ec699b5db9e9d19f76f623a6437253dd451f481aaf57`.
- `blueprint/validation/modules/module-sources.tsv`: `497ef0b3af34fb6bfdf4bda0101fda69f8a9440a5f035963fcdc6c2255ef8215`.
- generated Chen signature module: `cd03788aa0b765957c87dcfeb797decdc966ffdfb74ba7c6f90b70f5eb5e03dc`.
- generated terminal signature module: `3e00e09694654c195bfe84bc4ec31b0f1c3b7af66165b694a35d57cb3597248d`.
- `blueprint/11-refereeing-standard.md`: `eda7b9ab79e0555878bde8157d39f14bfe1b760e8bfcbfa5861fa90ee3e7f8e5`.

The production tree was at Git commit `b6744348ec0c2ab44788000b031721b861424c2f`; both reviewed files were untracked, so the two file hashes above, not the repository commit, are the review identity. Lean was 4.33.0 (`d8b1897...`) and the pinned Mathlib commit was `db584cd6d46c92f209a44c0f1c829460d327499d`.

Independence qualification: the reviewer did not implement `ChenCompleteSum.lean`, so that half is author-independent. The reviewer did implement the frozen `CompleteExponentialSum.lean`; this is a fresh snapshot-bound self-referee pass, not a two-person independence certificate for the terminal half. All nine agent slots were occupied during this pass, so a fresh terminal referee could not be spawned. Strict Tau-Ceti-style acceptance still requires an author-independent terminal sign-off.

## Verdict

**REQUEST CHANGES / NOT ACCEPTED.**

The proofs, builds, trust audit, covered signatures, definition bodies, imports, PM1/PM2 direction, and mathematical endpoints pass. Acceptance is nevertheless blocked by one P2 public-API ownership defect, one P3 documentation defect, and the terminal independence qualification above.

## Blocking findings

### [P2] Two exported simp theorems are absent from the repaired ownership ledger

The ledger assigns 58 declarations to `ChenCompleteSum.lean`, but the frozen file has 60 explicit public declarations. The two unledgered exports are:

- `TranslationalTilings.factorizationScalarLookup_of_mem`, at production line 3437;
- `TranslationalTilings.factorizationScalarLookup_of_not_mem`, at production line 3444.

These are not accidental proof artifacts: both are public `[simp]` theorems, occur in the mathematical blueprint at lines 964 and 971, and occur in the generated Chen signature module at lines 412 and 419. They nevertheless have no rows in `declaration-modules.tsv`. Thus the generated module and production agree with one another, but the claimed exact `58 + 20` owned boundary is false: the actual explicit boundary is `60 + 20`. In particular, the two exports have no machine-readable owner, source line, visibility, or validator-representation record.

Required repair: either add two ledger rows, update the Chen declaration count to 60, and regenerate/re-hash the affected validation artifacts, or deliberately remove/private the theorems and update the blueprint/generated module. Since they are a useful public simp API already discussed in the blueprint, adding the missing ownership rows is the natural repair.

### [P3] The frozen public boundary is not documented in Lean

`ChenCompleteSum.lean` has one module doc comment and no declaration docstrings. `CompleteExponentialSum.lean` has neither a module doc comment nor declaration docstrings. The exact scan

```text
rg -n '^/-!|^/--' ChenCompleteSum.lean CompleteExponentialSum.lean
```

returns only `ChenCompleteSum.lean:12:/-!`. This leaves the conditional/unconditional PM1 split, PM2 wrappers, certificate structure, executable constant, and terminal theorems undiscoverable through the Lean API itself. An external blueprint is valuable but does not replace library-facing documentation attached to public declarations.

Required repair: add a terminal module docstring and docstrings for the exported definitions, structures, and theorems, with equation/blueprint references where appropriate. The public conditional versus unconditional theorem pairs and the factorization certificate deserve explicit documentation in particular.

## Mathematical and proof audit (passed)

### ACK recurrence and induction

- The residue-class decomposition is exact, and (2.3) proves vanishing outside derivative roots by translating within a residue fibre and cancelling against a nontrivial additive character.
- (2.4) is an exact reindexing through the stationary translate. (2.5) is only used after proving the stationary translate nonzero; the child invariant supplies unchanged degree and primitivity, so recursive calls do not silently lose the induction hypotheses.
- The large-prime proof uses strong induction on the prime-power exponent. When `sigma < a`, the recursive exponent is `a - sigma < a`; when `a <= sigma`, the residue-class trivial bound closes the branch. Root-multiplicity weights sum to at most one after the middle-threshold estimate, so the total estimate closes without circular use of the target theorem.
- The small-prime proof uses a strong pair induction carrying both the total bound (2.13) and block-local bound (2.14). In the recursive branch, the normalized child's stationary mass is bounded by the parent root multiplicity. In the terminal branch, `a <= sigma <= d` gives the required power comparison. The low-block branch uses the derivative-content power bound and the trivial complete-sum estimate. The block hypothesis is present at every use of (2.14).
- `primePower_completeSum_bound_of_primeBound` covers all four local-factor regimes: `p <= d`, very large, middle, and `d < p` below the middle threshold. The prime input is genuinely the abstract `PolynomialPrimeSumBound`; no Weil theorem leaks into Chen.

### CRT certificate and factorization endpoint

- `polynomialCompleteSum_crt` proves the additive-character CRT phase identity and transports the sum through `ZMod.chineseRemainder`; it does not assume the desired product formula.
- `exists_completeSumFactorizationData` uses `Nat.recOnPosPrimePosCoprime`. The prime-power branch constructs the singleton-support certificate; the `q = 1` branch handles the empty support and proves norm one; and the coprime-product branch chooses Bezout twists, proves both twists nonzero, transports local primitivity, splits the support into disjoint left/right parts, and recombines the local norm products.
- The endpoint applies the conditional prime-power bound to every certified local polynomial, separates the product, uses `Nat.prod_factorization_pow_eq_self` through `factorization_rpow_product`, and bounds the finite local-factor product by `chenGlobalFactor`. The `q = 1` endpoint and finite-support logic are covered.

No mathematical gap, reversed inequality, circular induction, missing endpoint, or factorization-support defect was found in the frozen proofs.

## Boundary and API audit (passed except P2 above)

- For all 58 ledger-assigned Chen declarations and all 20 ledger-assigned terminal declarations, `#check @name` output with universes enabled is byte-for-byte identical between production and the generated signature package. The same check also passes for the two unledgered simp theorems.
- Full `#print` output is byte-for-byte identical for all 13 ledger definitions/abbreviations/structures, so this is definition-body conformance, not merely theorem-type conformance.
- PM1 ownership is correct in code: importing Chen exposes only the conditional `chen_prime_base_of`, `primePower_completeSum_bound_of_primeBound`, and `ack_theorem_2_2_finiteProduct_of_primeBound`; the Weil bridge and unsuffixed specializations are unknown until the terminal module is imported.
- PM2 ownership is correct in code: importing `QuadraticCompleteSum` exposes the prime-power Gauss-sum results but not the Chen certificate or composite quadratic wrappers; the terminal module owns `quadratic_polynomialCompleteSum_parity_bound` and `quadratic_polynomialCompleteSum_bound` and proves them through the Chen certificate.
- The effective core has the intended degree split: linear, quadratic, and degree at least three. The unconditional result supplies `polynomialPrimeSumBound`; the `_of_primeBound` variant keeps the incoming hypothesis abstract. The integral-phase terminal theorems are thin, checked transports through `integralCompleteSum_eq_polynomialCompleteSum`.
- The only downstream use found is the intended unconditional integral theorem in `Analysis/PolynomialRigidity.lean`.
- The project import DAG matches `module-sources.tsv`: Chen's only direct project import is `PolynomialCongruence`; the terminal module imports exactly Chen, Quadratic, and PolynomialWeil. Chen's explicit Mathlib imports match the generated source. Exact-name searches found no duplicate Mathlib API for the project-specific Chen/certificate/constants, while the implementation reuses Mathlib's CRT equivalence, positive/coprime factorization induction, factorization product theorem, finite products, polynomial content, and real-rpow infrastructure.

## Build, resource, and trust audit (passed)

- Direct warning-as-error compilation under the project/default Lean budget passed:
  - Chen: 16.990s wall, exit 0;
  - terminal: 7.520s wall, exit 0.
- Joint `lake build` passed: `Build completed successfully (3416 jobs)` in 7.387s wall.
- Lean 4.33's default `maxHeartbeats` is 200,000. Neither reviewed source contains `maxHeartbeats` or `maxRecDepth`; no resource override was used for the checks. The visible `maxSynthPendingDepth = 3` agrees with the package-wide `lakefile.toml` setting rather than increasing the package budget locally.
- A diagnostics-enabled terminal compile also passed and reported no pending-synthesis failure.
- The exact trust scan for `sorry`, `admit`, `axiom`, `unsafe`, `placeholder`, `opaque`, `native_decide`, validator imports, and resource overrides was empty.
- `#print axioms` was run on all 78 ledger declarations plus the two public simp exports. Every result used only a subset of the standard axioms `propext`, `Classical.choice`, and `Quot.sound`; no project axiom or validator axiom appeared.
- Recomputed production hashes after all checks were unchanged.

## Reproduction commands

Run from `/home/codex/Documents/Codex/2026-08-14/Tiling` unless noted:

```bash
sha256sum TranslationalTilings/NumberTheory/ChenCompleteSum.lean \
  TranslationalTilings/NumberTheory/CompleteExponentialSum.lean

TIMEFORMAT='DIRECT_CHEN elapsed=%3R user=%3U sys=%3S'
time lake env lean -DwarningAsError=true \
  TranslationalTilings/NumberTheory/ChenCompleteSum.lean

TIMEFORMAT='DIRECT_TERMINAL elapsed=%3R user=%3U sys=%3S'
time lake env lean -DwarningAsError=true \
  TranslationalTilings/NumberTheory/CompleteExponentialSum.lean

lake build TranslationalTilings.NumberTheory.ChenCompleteSum \
  TranslationalTilings.NumberTheory.CompleteExponentialSum

lake env lean -Ddiagnostics=true -DwarningAsError=true \
  TranslationalTilings/NumberTheory/CompleteExponentialSum.lean

rg -n --ignore-case \
  '\b(sorry|admit|axiom|unsafe|placeholder)\b|maxHeartbeats|maxRecDepth|BlueprintModuleValidation|native_decide|\bopaque\b' \
  TranslationalTilings/NumberTheory/ChenCompleteSum.lean \
  TranslationalTilings/NumberTheory/CompleteExponentialSum.lean

rg -n '^import |^set_option ' \
  TranslationalTilings/NumberTheory/ChenCompleteSum.lean \
  TranslationalTilings/NumberTheory/CompleteExponentialSum.lean

rg -n '^/-!|^/--' \
  TranslationalTilings/NumberTheory/ChenCompleteSum.lean \
  TranslationalTilings/NumberTheory/CompleteExponentialSum.lean
```

The API check was performed by generating `#check @<qualified-name>` commands from fields 5 and 9 of `declaration-modules.tsv`, importing both modules in production and in `BlueprintModuleValidation`, enabling `pp.universes`, and diffing the two process-substitution streams. The definition check used the same procedure with `#print` for ledger kinds `def`, `abbrev`, and `structure`. Both diffs exited 0 with empty output. The axiom check generated `#print axioms <qualified-name>` for the 78 ledger rows and the two additional simp declarations and exited 0.

## Acceptance gate

Do not accept these frozen hashes as a Tau-Ceti-standard boundary yet. Repair and regenerate the ownership ledger, add the missing Lean documentation, obtain an author-independent terminal review, then rerun the hash-bound API/build/trust/axiom commands above. No proof or mathematical repair is requested by this review.
