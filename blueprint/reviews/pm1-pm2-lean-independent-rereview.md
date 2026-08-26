# PM1-M1 and PM2 independent Lean/module-boundary rereview

Date: 2026-08-24 UTC.

## Verdict

**BLOCK.** I found no P0, P1, or P2 defect in the repaired PM1-M1 bridge,
the three Chen specializations, or the PM2 ownership split. Every requested
Lean, ownership, hash, and build check passed. I found one P3 documentation
regression in the module generator, however, and this review was commissioned
under the rule that a finding at any severity blocks.

This verdict is tied to generator SHA-256
`8e125c25a912be36ba977f3a2a2c4e283bfbdbbf51cb397f518281d163433a31`.

## Finding

### PM2-L1 [P3]: `module_for` documents only four of its six Chapter 05b exceptions

**Location.** `blueprint/validation/modules/generate_modules.py:170-174`,
against the actual exception set at lines 208-215 and its regression table at
lines 417-427.

**Evidence.** The `module_for` docstring says that the non-contiguous Chapter
05b exceptions are only `polynomialPrimeSumBound` and the three unconditional
Chen wrappers. The executable set additionally contains
`quadratic_polynomialCompleteSum_parity_bound` and
`quadratic_polynomialCompleteSum_bound`, which are precisely the two PM2
declarations whose non-contiguous terminal ownership this repair introduces.
The diagnostic at lines 432-433 is likewise still labelled only a
"Weil/Chen ownership regression" although the same regression loop now covers
the quadratic join.

**Impact.** The generated ownership is correct, so this does not undermine the
Lean evidence below. It does leave the generator's human-readable statement
of its own non-contiguous routing rule inconsistent with both the frozen module
layout and its executable behavior. That is a low-impact auditability defect in
the exact component responsible for enforcing PM2.

**Required repair.** Extend the docstring to name the two composite quadratic
wrappers as terminal exceptions and make the regression diagnostic inclusive
of PM2 (for example, "Chapter 05b terminal ownership regression"). Regenerate
the hashes, rerun the checks, and obtain a hash-bound follow-up review.

## Reviewed identity

The review covered the current uncommitted blueprint/validator working tree
over production checkout commit
`b6744348ec0c2ab44788000b031721b861424c2f`, Lean 4.33.0, and Mathlib commit
`db584cd6d46c92f209a44c0f1c829460d327499d`.

| Artifact | SHA-256 |
|---|---|
| `blueprint/05a-weil-stepanov.md` | `ec4ef69159642b17d44aa485b6e1eaa0e953f1d271461ed9c1765a16e1fc57da` |
| `blueprint/05b-chen-complete-sums.md` | `0ff0f36ad2157101ff5a35abebaf6e2cc6268e5a699af486e9c23277f014473d` |
| `blueprint/MODULE_LAYOUT.md` | `eb0b6ae1b9773739e727c8ee42c6c8e8d59f7370d1f0951636fd69bf42324dc9` |
| integrated validator | `3f1f3eeaae6ae3378d38317056d6853c014db18334423314e135a7c28ff55b92` |
| module generator | `8e125c25a912be36ba977f3a2a2c4e283bfbdbbf51cb397f518281d163433a31` |
| module map | `2703ec964cd52d577cf07331444a57ceb5cc038da4203bdc63d205311598d26a` |
| declaration ownership ledger | `eaaff70156c22cb43e2a6dc746c189cfc31f12afcc66147f23df5b8cb5293763` |
| module source ledger | `ea541eb2cc03bef54554937148bed8276cee1884b4a31a7252f4bb70f05b867c` |
| generated-hash manifest | `5f41eb041527f7d8bf4d4a5cb28b1677bbfa9e546d15e487e757c1483567f04d` |
| generated `ChenCompleteSum.lean` | `506ab2d91e949601b73a4b2f2fb6b7245cfbbc890e421c58d525b79babb88b2d` |
| generated `QuadraticCompleteSum.lean` | `0613f7e21b942d075e9ad8f1a19e11ba92a7d4c26dc66d79e5b4e4b910a04083` |
| generated `CompleteExponentialSum.lean` | `bc5fec432964f7e3131c6b847cd62cf19b9c0e876070a70a44d248ec91c148fc` |
| module build report | `d6e9f0e7dc7ac8cf5098fee1c730160cd0097fee37a7b7f534c7e3471417c437` |
| resolution log | `1a40c2be0c6f3bcd4b3a5bb2625dbf036763b8d34010e4663a6a39105f24a3b2` |

I made no edit to a chapter, generator, validator, generated module, ledger,
production source, build report, or resolution log. The only file written by
this review is this report.

## PM1-M1 evidence

### The bridge is an actually checked body

The declaration at `05b-chen-complete-sums.md:108-112`, the integrated
validator, and generated `CompleteExponentialSum.lean:28-32` all contain the
literal theorem body

```lean
theorem polynomialPrimeSumBound : PolynomialPrimeSumBound := by
  intro p _ f hpos hsmall
  let _ : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  exact polynomial_addChar_sum_prime
    (Fact.out : p.Prime) f hpos hsmall
```

In particular, the repaired annotation is present on both uses of `Fact.out`.
I recreated this body in a fresh strict Lean input importing only
`ChenCompleteSum`, `QuadraticCompleteSum`, and `PolynomialWeilBound`, not the
terminal module that already defines the theorem. It elaborated successfully.
Thus an existing terminal constant could not make the recreation pass.

`#print axioms polynomialPrimeSumBound` reports only `propext`,
`Classical.choice`, `Quot.sound`, and the validator signature
`polynomial_addChar_sum_prime`. It does not report
`polynomialPrimeSumBound` itself. This is the expected validator trust seam:
the 05a terminal theorem is a signature axiom here, while the PM1 adapter is a
real checked term.

### All three wrappers are exact specializations

I restated the complete public type of each unconditional theorem and compiled
these proof terms under the strict options:

```lean
chen_prime_base_of polynomialPrimeSumBound hp f hdegree hd hdp hprimitive

primePower_completeSum_bound_of_primeBound
  polynomialPrimeSumBound hp ha f hprimitive hdegree hd

ack_theorem_2_2_finiteProduct_of_primeBound
  polynomialPrimeSumBound d q hd hq f hdegree hprimitive
```

All three elaborated with exactly the unsuffixed conclusion. Their generated
unsuffixed declarations are exact-type axiom stubs, and I did not use those
stubs as proof evidence.

An import-only check of `ChenCompleteSum` resolved the proposition and all
three `_of_primeBound` declarations, while `#check_failure` confirmed that
`polynomialPrimeSumBound`, `polynomial_addChar_sum_prime`, and all three
unsuffixed wrappers are unavailable there. This verifies the intended
conditional boundary rather than merely reading it from the ledger.

## PM2 evidence

The declaration ledger and `module-sources.tsv` agree that
`QuadraticCompleteSum` owns exactly 19 declarations: two definitions and 17
theorem signatures. I generated and compiled a `#check` for every ledger name.
The local module imports only `FiniteCyclicPhase`; an import-only test confirmed
that `CompleteSumFactorizationData` and both composite wrappers are unavailable.

The two composite wrappers are instead owned by `CompleteExponentialSum`, whose
three direct imports are exactly `ChenCompleteSum`, `QuadraticCompleteSum`, and
`PolynomialWeilBound`. The generator reports the full 29-module graph acyclic.
There is no reverse edge from either local branch to this terminal join.

I also compiled a fresh witness of the substantive cross-branch interface. It
obtains `D : CompleteSumFactorizationData q hq f` from
`exists_completeSumFactorizationData`, uses `D.norm_eq_product` and
`D.local_primitive`, indexes a local polynomial by
`p : FactorizationPrimeSupport q` and `D.scalar p`, derives positivity of
`q.factorization p.1` from `p.property`, and applies
`quadratic_oddPrimePower_norm` to that exact local polynomial. This establishes
that the support-indexed Chen certificate and the local quadratic API are not
merely simultaneously visible: their types compose at the required local
factor. The local module also exports the zero, two-adic, and modulus-two cases
used by the remaining branches, and `factorizationPrimeSupport_prod_eq` exposes
the necessary product reindexing.

The blueprint's Section 9 proof plan routes the `q = 1`, odd-prime, unique
2-primary, and final square-root monotonicity branches through these APIs. The
two moved declarations are exactly the declarations that need the global CRT
certificate; the retained arbitrary-modulus linear lemmas have direct
orthogonality proofs and introduce no misplaced Chen dependency.

## Executable checks

The following fresh checks passed on the reviewed hashes:

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

The module check reported `29 modules; 867 declarations; DAG acyclic`. The full
build completed successfully with 3446 jobs. `lake query TranslationalTilings`
also exited successfully. The build/query output contains only the documented
generated long-line/header style warnings, with no elaboration, import,
resolution, cycle, or trust warning.

Fresh strict `/dev/stdin` Lean invocations separately checked the bridge body,
the three exact specialization terms, all 19 local quadratic names, both
negative module-visibility boundaries, the relevant `#print axioms` output,
and the cross-branch factorization witness described above.

Finally, a trust-gap scan found no `sorry`, `admit`, `unsafe`, or
`native_decide` in the relevant blueprint/validator sources. Generated `axiom`
declarations were treated only as exact signature witnesses throughout this
review. Consequently the sole blocker is PM2-L1, not an unacknowledged proof
claim about the validator stubs.
