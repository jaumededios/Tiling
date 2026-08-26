# PM1-M1 and PM2 independent Lean/module-boundary follow-up

Date: 2026-08-24 UTC.

## Verdict

**APPROVE.** I found no P0, P1, P2, or P3 finding in the repaired PM1-M1
bridge, the three Chen specialization boundaries, the PM2 quadratic ownership
split, or the generator regression that enforces those boundaries.

This is a separate follow-up to the BLOCK verdict in
`pm1-pm2-lean-independent-rereview.md`. It approves generator SHA-256
`7c337766dea2d15034a0cb2c67a781edc747d1915ab83cd4293ea422f7eee65b`
and generated-hash-manifest SHA-256
`c85ee39a0039450e20091d440f35f17499fdf91579ab8024c94b7135d787f1c3`.
It does not retroactively alter the earlier hash-bound verdict.

Generated theorem axioms were treated only as exact signature/elaboration
witnesses, never as proof evidence.

## Reviewed identity

| Artifact | SHA-256 |
|---|---|
| `blueprint/05a-weil-stepanov.md` | `ec4ef69159642b17d44aa485b6e1eaa0e953f1d271461ed9c1765a16e1fc57da` |
| `blueprint/05b-chen-complete-sums.md` | `0ff0f36ad2157101ff5a35abebaf6e2cc6268e5a699af486e9c23277f014473d` |
| `blueprint/MODULE_LAYOUT.md` | `eb0b6ae1b9773739e727c8ee42c6c8e8d59f7370d1f0951636fd69bf42324dc9` |
| integrated validator | `3f1f3eeaae6ae3378d38317056d6853c014db18334423314e135a7c28ff55b92` |
| module generator | `7c337766dea2d15034a0cb2c67a781edc747d1915ab83cd4293ea422f7eee65b` |
| module map | `2703ec964cd52d577cf07331444a57ceb5cc038da4203bdc63d205311598d26a` |
| declaration ownership ledger | `eaaff70156c22cb43e2a6dc746c189cfc31f12afcc66147f23df5b8cb5293763` |
| module source ledger | `ea541eb2cc03bef54554937148bed8276cee1884b4a31a7252f4bb70f05b867c` |
| generated-hash manifest | `c85ee39a0039450e20091d440f35f17499fdf91579ab8024c94b7135d787f1c3` |
| generated `ChenCompleteSum.lean` | `506ab2d91e949601b73a4b2f2fb6b7245cfbbc890e421c58d525b79babb88b2d` |
| generated `QuadraticCompleteSum.lean` | `0613f7e21b942d075e9ad8f1a19e11ba92a7d4c26dc66d79e5b4e4b910a04083` |
| generated `CompleteExponentialSum.lean` | `bc5fec432964f7e3131c6b847cd62cf19b9c0e876070a70a44d248ec91c148fc` |
| module build report | `4901bc76f0c0e53e8175f9402d86d04864eb8096ac2aabfca5dc4d8cff42d8ac` |
| resolution log | `47903e552ef3bbf92de2fceae5ac4f90d2ab186efdc6f9d303dd41d42b596361` |

The environment remained production checkout commit
`b6744348ec0c2ab44788000b031721b861424c2f`, Lean 4.33.0, and Mathlib commit
`db584cd6d46c92f209a44c0f1c829460d327499d`.

I edited no chapter, validator, generator, generated module, ledger, build
report, resolution log, or production source. The only file written in this
follow-up is this report.

## PM2-L1 disposition

The generator docstring now literally identifies all six non-contiguous
Chapter 05b terminal declarations: the checked `PolynomialPrimeSumBound`
adapter, the three unconditional Chen wrappers, and the two composite quadratic
wrappers. Its executable exception set contains those same six identities.

The ownership regression table simultaneously requires those six declarations
in `CompleteExponentialSum` and the three conditional `_of_primeBound`
declarations in `ChenCompleteSum`. Its failure diagnostic is now the inclusive
`Chapter 05b terminal ownership regression`, rather than the stale
Weil/Chen-only label. This fully resolves PM2-L1 from the preceding review.

## Replayed Lean and boundary evidence

I freshly replayed the substantive checks instead of relying on unchanged
generated-module hashes.

- The literal `polynomialPrimeSumBound` body elaborated from the preterminal
  imports with `#check_failure polynomialPrimeSumBound` first confirming that
  the theorem was not already available. The body explicitly constructs
  `NeZero p` with `(Fact.out : p.Prime).ne_zero` and applies the 05a theorem.
- Complete restatements of all three unconditional signatures compiled with
  proof terms specializing `chen_prime_base_of`,
  `primePower_completeSum_bound_of_primeBound`, and
  `ack_theorem_2_2_finiteProduct_of_primeBound` at the checked bridge.
- `#print axioms polynomialPrimeSumBound` contains the validator signature
  `polynomial_addChar_sum_prime` but not a self-axiom for the bridge. This is
  exactly the declared signature-only validator trust boundary.
- The ledger still assigns exactly 19 declarations to
  `QuadraticCompleteSum`: two definitions and 17 theorem signatures. A fresh
  generated `#check` for every one of the 19 names compiled.
- Importing only `QuadraticCompleteSum` still leaves
  `CompleteSumFactorizationData` and the two composite wrappers unavailable.
  Both wrappers remain in `CompleteExponentialSum`.
- A fresh Lean witness obtained Chen's support-indexed factorization data,
  consumed `D.norm_eq_product`, `D.local_primitive`, and `D.scalar`, and applied
  `quadratic_oddPrimePower_norm` to the resulting exact local polynomial. Thus
  the APIs compose genuinely at the required local factor. The zero, two-adic,
  modulus-two, support-product, and empty-support APIs needed by the other proof
  branches remain visible in the same terminal join.

No import points back from the terminal module into either branch. The module
map and executable generator both confirm the acyclic join

```text
ChenCompleteSum ---------\
QuadraticCompleteSum ----- CompleteExponentialSum
PolynomialWeilBound -----/
```

with `QuadraticCompleteSum -> FiniteCyclicPhase` and
`ChenCompleteSum -> PolynomialCongruence -> FiniteCyclicPhase` below it.

## Replayed commands

All of these commands completed successfully on the hashes above:

```text
python3 blueprint/validation/generate_integrated.py --check
lake env lean -DrelaxedAutoImplicit=false -DmaxSynthPendingDepth=3
  -DmaxErrors=1000 /absolute/path/BlueprintIntegrated.lean
python3 blueprint/validation/modules/generate_modules.py --check
sha256sum -c blueprint/validation/modules/generated-hashes.sha256
python3 blueprint/validation/modules/generate_modules.py --build
cd blueprint/validation/modules/BlueprintModuleValidation
lake query TranslationalTilings
```

The generator reported `29 modules; 867 declarations; DAG acyclic`; the full
build completed successfully with 3446 jobs; and the target query exited zero.
Only the already documented generated long-line/header style warnings appeared.

Separate strict Lean inputs replayed the bridge, all three exact
specializations, all 19 local quadratic names, the negative visibility checks,
the axiom query, and the cross-branch factorization witness. A relevant-source
scan found no `sorry`, `admit`, `unsafe`, or `native_decide`.

The current build report, resolution log, module layout, ownership ledger,
generated modules, and executable behavior therefore agree, and no blocker
remains in this review's PM1-M1/PM2 scope.
