# PM1-M1 and PM2 independent mathematical rereview

Date: 2026-08-24 UTC.

## Verdict

**APPROVE.**  I found no P0, P1, P2, or P3 finding in the repaired PM1-M1
bridge or the PM2 quadratic ownership split.  In particular:

- the generated `polynomialPrimeSumBound` is a checked theorem body, not an
  axiom stub, and its annotated construction of `NeZero p` elaborates;
- specializing each of the three conditional Chen theorems at that bridge
  produces the exact corresponding unconditional theorem type;
- the dependency graph contains no route from the conditional Chen module to
  the Stepanov/Weil proof, and the terminal join introduces no cycle;
- `QuadraticCompleteSum` retains exactly the 19 local, linear, Gauss-sum,
  prime-power, and 2-primary declarations that its import closure can prove;
- the two composite quadratic wrappers are correctly owned by
  `CompleteExponentialSum`, because their documented proof genuinely consumes
  Chen's support-indexed factorization certificate; and
- no other theorem in the local quadratic module requires that certificate or
  is misplaced by this criterion.

This is a mathematical and dependency-sufficiency approval of the blueprint
interfaces.  As required, generated theorem axioms were treated only as
signature/elaboration witnesses, never as proof evidence.

## Reviewed identity

The rereview was performed on these exact current artifacts:

| Artifact | SHA-256 |
|---|---|
| `blueprint/05a-weil-stepanov.md` | `ec4ef69159642b17d44aa485b6e1eaa0e953f1d271461ed9c1765a16e1fc57da` |
| `blueprint/05b-chen-complete-sums.md` | `0ff0f36ad2157101ff5a35abebaf6e2cc6268e5a699af486e9c23277f014473d` |
| `blueprint/MODULE_LAYOUT.md` | `eb0b6ae1b9773739e727c8ee42c6c8e8d59f7370d1f0951636fd69bf42324dc9` |
| `blueprint/COMPARATOR.md` | `5375f6c9aead8c0790681ad1326bdac227df9cef791b1d1c4d80811dfaa7ccb5` |
| `blueprint/README.md` | `6a77334dfdf9a683c27b4cea05863153196e7d0e55d88b09447a685f8ba8a9e3` |
| `blueprint/validation/BlueprintIntegrated.lean` | `3f1f3eeaae6ae3378d38317056d6853c014db18334423314e135a7c28ff55b92` |
| `blueprint/validation/declaration-coverage.tsv` | `88d0a206b831a20eeeea8e55d44bd7127b7fae66ee4f862ff8d6735b67ffde96` |
| `blueprint/validation/modules/generate_modules.py` | `8e125c25a912be36ba977f3a2a2c4e283bfbdbbf51cb397f518281d163433a31` |
| `blueprint/validation/modules/module-map.json` | `2703ec964cd52d577cf07331444a57ceb5cc038da4203bdc63d205311598d26a` |
| `blueprint/validation/modules/declaration-modules.tsv` | `eaaff70156c22cb43e2a6dc746c189cfc31f12afcc66147f23df5b8cb5293763` |
| `blueprint/validation/modules/module-sources.tsv` | `ea541eb2cc03bef54554937148bed8276cee1884b4a31a7252f4bb70f05b867c` |
| `blueprint/validation/modules/build-report.md` | `d6e9f0e7dc7ac8cf5098fee1c730160cd0097fee37a7b7f534c7e3471417c437` |
| `blueprint/reviews/resolution-log.md` | `1a40c2be0c6f3bcd4b3a5bb2625dbf036763b8d34010e4663a6a39105f24a3b2` |
| first PM1 mathematical report | `45791846992f23317dbceaa77bfbb7ed21fa6faabf34b46c54ceb2ee6533df4b` |
| first PM1 boundary report | `9c8c7220e73a9a8fc8bc69b6b7ba1108723da093cc28a077c5ee6f89120aff7b` |
| generated `FiniteCyclicPhase.lean` | `02a4b9c18abf68280e3589f537efa617599d9908e1302daf9ffcad3a9920db0b` |
| generated `ChenCompleteSum.lean` | `506ab2d91e949601b73a4b2f2fb6b7245cfbbc890e421c58d525b79babb88b2d` |
| generated `QuadraticCompleteSum.lean` | `0613f7e21b942d075e9ad8f1a19e11ba92a7d4c26dc66d79e5b4e4b910a04083` |
| generated `PolynomialWeilBound.lean` | `b1379aa6cd282bb97cfb7bb30b3c26411fd55392cd8b4c34e76b2f6b3be62971` |
| generated `CompleteExponentialSum.lean` | `bc5fec432964f7e3131c6b847cd62cf19b9c0e876070a70a44d248ec91c148fc` |
| `generated-hashes.sha256` | `5f41eb041527f7e3131c6b847cd62cf19b9c0e876070a70a44d248ec91c148fc` |

The pinned environment reports Lean 4.33.0 and Mathlib commit
`db584cd6d46c92f209a44c0f1c829460d327499d`.  I did not edit any reviewed
chapter, validator, generated module, ledger, production source, or snapshot.

## PM1-M1: the checked Weil bridge

`PolynomialPrimeSumBound` deliberately asks for `[Fact p.Prime]`, whereas
`polynomial_addChar_sum_prime` deliberately asks for `[NeZero p]` and an
explicit proof `p.Prime`.  The repaired body is therefore the required
adapter:

```lean
theorem polynomialPrimeSumBound : PolynomialPrimeSumBound := by
  intro p _ f hpos hsmall
  let _ : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  exact polynomial_addChar_sum_prime
    (Fact.out : p.Prime) f hpos hsmall
```

The type annotation on `Fact.out` is substantive: it fixes the inference
failure reported in the first mathematical review.  Since primality implies
nonzeroness, the constructed `NeZero` instance is valid, and the remaining
arguments and conclusion are definitionally the fields of
`PolynomialPrimeSumBound`.

Three independent checks establish that this is not merely convincing prose:

1. The canonical coverage row marks `polynomialPrimeSumBound` as
   `checked-body`, and the generated terminal source contains the literal body.
2. Both the strict integrated artifact and the actual generated terminal
   module compile that body.
3. A separate strict import test recreated the literal body using only
   `ChenCompleteSum` and `PolynomialWeilBound`.  It elaborated with
   `relaxedAutoImplicit=false` and `maxSynthPendingDepth=3`.

Moreover, `#print axioms TranslationalTilings.polynomialPrimeSumBound` reports
only

```text
propext, Classical.choice, Quot.sound, polynomial_addChar_sum_prime
```

so the bridge is not itself an additional axiom.  Its only project-level
mathematical assumption in the validator is the generated signature for the
05a terminal theorem, exactly as intended by the validator trust boundary.

### Exact specializations

I compiled exact-type `example`s for all three terms, first with an
independently recreated bridge and then with the actual generated
`polynomialPrimeSumBound`:

| Conditional theorem | Specializing term | Exact resulting public type |
|---|---|---|
| `chen_prime_base_of` | `chen_prime_base_of polynomialPrimeSumBound` | `chen_prime_base` |
| `primePower_completeSum_bound_of_primeBound` | `primePower_completeSum_bound_of_primeBound polynomialPrimeSumBound` | `primePower_completeSum_bound` |
| `ack_theorem_2_2_finiteProduct_of_primeBound` | `ack_theorem_2_2_finiteProduct_of_primeBound polynomialPrimeSumBound` | `ack_theorem_2_2_finiteProduct` |

These tests restated every binder and conclusion of the unsuffixed signatures;
all elaborated without coercion or theorem-strength mismatch.  The generated
unsuffixed declarations themselves are exact-type axiom stubs, so I did not
count their existence as evidence of derivability; the explicit specialization
terms are the evidence.

### Dependency direction and exhaustiveness

The relevant graph is

```text
FiniteCyclicPhase (defines PolynomialPrimeSumBound)
        |
PolynomialCongruence
        |
ChenCompleteSum (three conditional hWeil theorems)
        |\
        | \____________________
        |                      \
PolynomialWeilBound ------> CompleteExponentialSum
                              (bridge and unsuffixed wrappers)
```

More precisely, `PolynomialWeilBound` is reached from the independent 05a
Stepanov chain, while `ChenCompleteSum` imports only `PolynomialCongruence`.
`CompleteExponentialSum` imports both, plus the independent local quadratic
module.  No edge points back from the terminal join, so the graph is acyclic.

A full text and ownership search found exactly three occurrences of
`hWeil : PolynomialPrimeSumBound` in generated `ChenCompleteSum`: the three
conditional theorems listed above.  It found no use of
`polynomial_addChar_sum_prime` there.  All later unsuffixed effective complete
sum results, together with their conditional variants, already live in the
terminal module.  Thus no other unsuffixed Weil-dependent declaration remains
in a dependency closure lacking the Weil proof.

## PM2: local quadratic API versus composite CRT wrappers

### Mathematical sufficiency of the composite proof

The two moved conclusions are genuinely global composite-modulus statements.
Their documented proof is complete at the blueprint/API level:

1. For `q=1`, `FactorizationPrimeSupport 1` is empty,
   `polynomialCompleteSum_one_norm` gives norm one, and the empty product is
   one.  This handles the constant-phase possibility forced by primitivity.
2. For `q>1`, `exists_completeSumFactorizationData` supplies a scalar on each
   support prime, scalar nonzeroness, local primitivity, and the exact equality
   between the global norm and the support-indexed product of local norms.
3. `Polynomial.natDegree_C_mul_eq` uses scalar nonzeroness to preserve the
   degree-at-most-two hypothesis for every local polynomial.
4. At an odd support prime, local primitivity says the two nonconstant
   coefficients are not both divisible by that prime.  If the quadratic
   coefficient is a unit, `quadratic_oddPrimePower_norm` gives
   `sqrt (p^a)`; otherwise the linear coefficient is a unit and
   `quadratic_primePower_linear_unit_eq_zero` gives zero.
5. At `p=2`, exponent one is covered by `quadratic_mod_two_bound`, whose bound
   `2` is exactly `sqrt (2 * 2)`.  For exponent at least two, an odd linear
   coefficient gives zero.  If the linear coefficient is even, primitivity
   forces the quadratic coefficient odd, and
   `quadratic_twoPower_quadratic_odd_norm` gives
   `sqrt (2 * 2^a)`.
6. `factorizationPrimeSupport_prod_eq` converts the subtype product to the
   factorization-support product.  The odd-primary square roots multiply to
   `sqrt q` when `q` is odd.  When `q` is even there is exactly one support
   prime equal to two, so its single extra `sqrt 2` produces
   `sqrt (2*q)`, never one extra factor per prime.
7. The parity theorem is therefore the sharp product conclusion.  The final
   `quadratic_polynomialCompleteSum_bound` follows by the stated monotonicity
   comparison with `sqrt (2*q)`.

The local lemmas cover every coefficient case forced by local primitivity, and
the factorization certificate supplies exactly the global data not available
in `QuadraticCompleteSum`.  No circular assumption of either moved wrapper is
needed.

### Ownership audit

The canonical ledger assigns exactly 19 declarations to
`QuadraticCompleteSum`: two definitions and seventeen theorem signatures.
They comprise the quadratic polynomial and Gauss sum, odd-prime and 2-adic
bases/recurrences/completing-square lemmas, modulus-two evaluation, polynomial
reconstruction, two arbitrary-modulus linear results, and the five final
prime-power/modulus-two case lemmas.  A strict import-only test successfully
resolved every one of these 19 names.

The same import-only test deliberately queried

```text
CompleteSumFactorizationData
quadratic_polynomialCompleteSum_parity_bound
quadratic_polynomialCompleteSum_bound
```

and Lean reported all three as unknown identifiers.  Importing
`CompleteExponentialSum` made all three visible.  This is direct evidence that
the generated module boundary matches the documented dependency split, not
merely that the ownership ledger says it does.

There is no overlooked composite quadratic theorem in the local module.  The
only arbitrary-`q` theorem declarations retained there are
`linear_polynomialCompleteSum_eq_zero` and
`linear_polynomialCompleteSum_bound`.  Their documented proof is direct
additive-character orthogonality (with the `q=1` constant case), so it needs no
CRT factorization certificate.  `quadraticGaussSum` is an arbitrary-modulus
definition, not a proof obligation.  Every remaining theorem has modulus one,
modulus two, or a single prime power.  Conversely, both declarations whose
proof takes the support-indexed product are in the terminal join.

### Acyclic dependency sufficiency

The frozen module map has the exact edges

```text
QuadraticCompleteSum  -> FiniteCyclicPhase
ChenCompleteSum       -> PolynomialCongruence -> FiniteCyclicPhase
PolynomialWeilBound   -> Stepanov.ReciprocalRoots -> ...
CompleteExponentialSum
  -> ChenCompleteSum
  -> QuadraticCompleteSum
  -> PolynomialWeilBound
```

Thus the local quadratic proof sees the shared phase/content definitions and
Mathlib but not Chen.  The terminal module sees both the local quadratic API
and `CompleteSumFactorizationData`.  Nothing below it imports the terminal
module, and the generator independently reports the complete 29-module DAG as
acyclic.

The move changes only the owning import boundary.  Namespace, declaration
names, binders, and theorem conclusions are unchanged.  Downstream analysis
already imports `CompleteExponentialSum`, and the comparator continues to
identify the exact terminal complete-sum estimate used for Lemma 4.2.  Hence
the exact paper-facing terminal results and API statements are preserved.

## Generator and ledger regression coverage

The generator has two independent protections:

- its non-contiguous terminal-specialization set names the PM1 bridge, the
  three unconditional Chen wrappers, and the two PM2 composite quadratic
  wrappers; and
- its ownership regression table simultaneously requires those six names in
  `CompleteExponentialSum` and the three conditional Chen names in
  `ChenCompleteSum`.

The generated ownership ledger agrees.  In particular,
`polynomialPrimeSumBound` is `checked-body`; the three conditional Chen
theorems remain in `ChenCompleteSum`; the three unsuffixed specializations and
both composite quadratic wrappers are in `CompleteExponentialSum`; and the 19
other Section 9 declarations are in `QuadraticCompleteSum`.

## Replayed validation

| Check | Result |
|---|---|
| `python3 blueprint/validation/generate_integrated.py --check` | exit 0; integrated artifact and canonical ledger current |
| direct pinned `lake env lean` on `BlueprintIntegrated.lean` | exit 0; no diagnostics |
| pinned Lean with `-DrelaxedAutoImplicit=false -DmaxSynthPendingDepth=3 -DmaxErrors=1000` | exit 0; no diagnostics |
| `python3 blueprint/validation/modules/generate_modules.py --check` | exit 0; 29 modules, 867 declarations, DAG acyclic |
| `sha256sum -c blueprint/validation/modules/generated-hashes.sha256` | exit 0; every listed artifact `OK` |
| `python3 blueprint/validation/modules/generate_modules.py --build` | exit 0; complete offline build, 3446 jobs |
| generated-package `lake query TranslationalTilings` | exit 0 |
| exact PM1 bridge-body test with prerequisite-only imports | exit 0 |
| all three exact PM1 specializations using the recreated bridge | exit 0 |
| all three exact PM1 specializations using the generated bridge | exit 0 |
| all 19 local quadratic declarations under a quadratic-only import | exit 0 |
| expected-negative quadratic-only import test for Chen certificate and moved wrappers | all three names rejected as unknown, as required |
| terminal import test for certificate and moved wrappers | all three names resolved |
| scan of affected generated modules for `sorry`, `admit`, `native_decide`, or relaxed auto-implicit enablement | no matches |

The full build and target query emitted only the already documented style
warnings from generated long source/signature lines and the generated `Main`
header.  There was no elaboration, module-resolution, ownership, hash, cycle,
or trust-boundary failure.  Those inherited validator-artifact warnings do not
constitute a PM1-M1 or PM2 defect.

## Findings

None.
