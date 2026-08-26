# PM3 independent Lean/API review

Date: 2026-08-24 UTC.

## Verdict

**APPROVE.** I found no P0, P1, P2, or P3 finding in the repaired PM3
statement, its checked production proof route, the middle-prime recurrence,
or its downstream use.  The new premise

```lean
(hpB : (p : ℝ) ≤ chenMiddlePrimeThreshold d)
```

is both necessary for the implementation advertised by the conditional Chen
module and sufficient for every recursive call made by `ack_ineq_2_10`.
It is placed after `hdp`, agrees with `ack_eq_2_6`, and is supplied at the
terminal middle-prime consumer.  No paper-facing terminal theorem type
changes.

Generated theorem axioms were treated only as exact signature and elaboration
witnesses, never as proof evidence.

## Reviewed identity

| Artifact | SHA-256 |
|---|---|
| `blueprint/05b-chen-complete-sums.md` | `81b1799e2e08cdaa6639df75a16e15fb3c415793ee04f52cc3cdd2def5dd15a3` |
| `blueprint/MODULE_LAYOUT.md` | `eb0b6ae1b9773739e727c8ee42c6c8e8d59f7370d1f0951636fd69bf42324dc9` |
| integrated validator | `318a8e40e829627be34c28574abf56710eb62f18bd9bbaf4bf888bb473e2b809` |
| integrated generator | `a5e17e899bd01ef1922200bb737adb1129c015827e4f9043f135b2888e3450af` |
| module generator | `e9230f042900319ac1e1cbac42741531f3785f4536e14b7b2c96190afcab2337` |
| module map | `2703ec964cd52d577cf07331444a57ceb5cc038da4203bdc63d205311598d26a` |
| integrated declaration ledger | `c0ea4cf748b3428c436a367a10974dc9e83b6ba9b46082723b90d9cb0f5d466d` |
| module ownership ledger | `1ced9cce08d0db519eb8ec699b5db9e9d19f76f623a6437253dd451f481aaf57` |
| module source ledger | `497ef0b3af34fb6bfdf4bda0101fda69f8a9440a5f035963fcdc6c2255ef8215` |
| generated-hash manifest | `dee6bad6430242de362928c3a5ed9bea1c42d32ebd72573ff66f357b3a303ec5` |
| generated `ChenCompleteSum.lean` | `cd03788aa0b765957c87dcfeb797decdc966ffdfb74ba7c6f90b70f5eb5e03dc` |
| module build report | `980c898f204bdc8db215f5643a4fa9e4030609a4abacfa2fed69291f9e3f9f17` |
| resolution log | `c21906aa12ef8737f7a3af32785d4d86b37fcb9781622981d445b80692dfdd92` |

The environment was production checkout commit
`b6744348ec0c2ab44788000b031721b861424c2f`, Lean 4.33.0, and Mathlib commit
`db584cd6d46c92f209a44c0f1c829460d327499d`.

I edited no chapter, validator, generator, generated module, ledger, build
report, resolution log, or production source.  The only file written in this
review is this report.

## PM3 recurrence check

For an early derivative root, the checked production body sets

```text
sigma = stationaryOrder f p mu.val
b     = L + 1 - sigma.
```

Membership in `earlyDerivativeRoots` gives `sigma < L`, while the stationary
root theorem gives `2 ≤ sigma`.  Hence `2 ≤ b` and `b < L + 1`.  The
normalized child has the same advertised degree `d` and remains primitive by
`stationaryChildInvariant`.  Its recurrence bound is therefore exactly an
application of `ack_eq_2_6` at exponent `b`, and that theorem requires the
same middle-prime premise `hpB`.  The child root-mass comparison then changes
the coefficient to the parent multiplicity, and
`ack_ineq_2_7_of_inductionBound` supplies the displayed early-root term.
The private early/late assembly combines these terms with the trivial late
bound to obtain the exact public (2.10) conclusion.

Thus the old type without `hpB` was not implementable in the conditional
module by this recurrence: it had neither a middle-prime child induction
hypothesis nor an imported unconditional Weil-backed terminal theorem.  The
repaired hypothesis closes precisely that gap and adds no unrelated strength.

There is no circular proof dependency.  The actual engine
`ack_eq_2_6_induction` is a strong induction on the modulus exponent and uses
the private generic early/late assembly.  Public `ack_eq_2_6` packages that
engine.  Public `ack_ineq_2_10` may then invoke `ack_eq_2_6` on its strict
child exponent.  This ordering faithfully realizes the recurrence even
though the public statements are printed in paper order in the blueprint.

## Downstream and boundary check

The repaired public theorem remains owned by
`TranslationalTilings.NumberTheory.ChenCompleteSum`; both declaration ledgers
assign it uniquely there, immediately beside `ack_eq_2_6`.  No public source
outside that module directly consumes `ack_ineq_2_10`.  The substantive
downstream consumer is the same middle-prime recurrence exposed through
`ack_eq_2_6` and then `primePower_completeSum_bound_of_primeBound`.

In the terminal split of `primePower_completeSum_bound_of_primeBound`, the
branch `d < p` and `¬ chenMiddlePrimeThreshold d ≤ p` derives
`p ≤ chenMiddlePrimeThreshold d` by linear order and passes it literally to
`ack_eq_2_6`.  The adjacent large-prime branches instead use their separate
large-prime induction.  The repaired premise therefore matches the exact
branch boundary, including equality at the middle threshold, and does not
alter the unconditional wrapper in `CompleteExponentialSum`.

The current checked production `ack_ineq_2_10` body was inspected directly.
Its `hpB` occurs at the child call to `ack_eq_2_6`; all errors in the current
whole production-module replay were later in the independent large-prime
arithmetic block, after Lean had elaborated the PM3 declaration.  I do not
treat that incomplete whole-production build as proof evidence for PM3, and
the production gate remains separate from this blueprint/API verdict.

## Replayed validation evidence

The following fresh commands passed on the hashes above:

```text
python3 blueprint/validation/generate_integrated.py --check
lake env lean blueprint/validation/BlueprintIntegrated.lean
lake env lean -DrelaxedAutoImplicit=false -DmaxSynthPendingDepth=3
  -DmaxErrors=1000 blueprint/validation/BlueprintIntegrated.lean
python3 blueprint/validation/modules/generate_modules.py --check
sha256sum -c blueprint/validation/modules/generated-hashes.sha256
python3 blueprint/validation/modules/generate_modules.py --build
cd blueprint/validation/modules/BlueprintModuleValidation
lake query TranslationalTilings
```

The module generator reported `29 modules; 867 declarations; DAG acyclic`,
and the complete generated build finished successfully with 3446 jobs.  Only
the already documented generated long-line and header style warnings appeared.
A relevant production-source scan found no `sorry`, `admit`, `axiom`,
`unsafe`, `native_decide`, heartbeat override, or recursion-depth override.

The checked build report is historical author evidence for the boundary
design and predates this PM3 review; it was not used as proof evidence.  The
fresh independent commands above establish that the current repaired
signature, ownership, and module boundary elaborate successfully.
