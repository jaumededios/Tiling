# Independent review: PM1 Chen/Weil module boundary

## Verdict and reviewed snapshot

**Verdict: APPROVE.** I found no P0, P1, P2, or P3 issue in the PM1 repair.
The repair places the three unconditional wrappers in
`CompleteExponentialSum` and leaves their hypothesis-parametric counterparts
in `ChenCompleteSum`. This is the correct proof dependency boundary, preserves
the intended reusable conditional Chen layer, and is acyclic.

This verdict is tied to the following uncommitted blueprint snapshot:

| Artifact | SHA-256 |
|---|---|
| `blueprint/05b-chen-complete-sums.md` | `2fcfecf35daddd6f500a4da80c5296442c6566eb7b81f9d36fa55fe8bcbcb000` |
| `blueprint/MODULE_LAYOUT.md` | `b944e6fa0580f2d1af6f1210b83005a6035b17045da5eb91c764c6857ef45428` |
| `blueprint/validation/modules/generate_modules.py` | `e0e71c95379f7c490b9f6d95f404908410debee92961444b31c3773347b7cf8c` |
| `blueprint/validation/modules/module-map.json` | `2703ec964cd52d577cf07331444a57ceb5cc038da4203bdc63d205311598d26a` |
| `blueprint/validation/modules/declaration-modules.tsv` | `5c16e9f00b55b3a578b22edf5a8b8173e5f643c0ea42f7ae4b7e7ae0284fba4c` |
| `blueprint/validation/modules/build-report.md` | `d1f074004f844f33743b4b3dee6fd71eaee1c4de5cd0beb3897f625354b581db` |
| generated `ChenCompleteSum.lean` | `4aa2b774b9f21d00fce5fda2a1e5e9387f4dbcec8af52898a11f65a28f6df239` |
| generated `CompleteExponentialSum.lean` | `6fccdf2dfddd2ee2df906adfd5e12bb02bb540c4c757a83182ef5cb49d4037ec` |
| `blueprint/validation/BlueprintIntegrated.lean` | `2846cc0186f6c023bfdf1a3ca2e7eed296dccb8a47e21a4f8c785e116952947c` |
| `blueprint/validation/declaration-coverage.tsv` | `dce11a384c52166cd105f47db53dc0923befa3027f7b2cdc7711bcc6140905d7` |
| generated-hash manifest | `3a1108b7efeef8610d8f559d634da172c3f36f147eded5ab1bf66a0c9a0096a3` |

The production repository was dirty during this review because implementation
work was concurrent. Its branch tip was
`b6744348f547e58e4140732405cd8e896238b11a`; that commit does not identify the
reviewed working tree. The hashes above are therefore the authoritative review
identity. This report is a new review artifact and is not itself an input to
the reviewed snapshot.

## Scope and trust boundary

I independently read the complete approved 05b ownership discussion, the
module-layout specification, the generator (including its DAG and ownership
checks), the module map, both generated modules, the declaration-ownership
ledger, the build report, the PM1 resolution entry, the production blocker
message, and the actual current production import closure. I also inspected
the relevant generated `PolynomialWeilBound` API.

The generated validation theorems have axiom bodies. I used them only to test
names, exact types, namespace visibility, imports, and ownership. They are not
evidence that any theorem has been proved. The proof-boundary conclusion below
instead comes from the mathematical dependency described in 05b, the exact
theorem signatures, and the contents of the old production import closure.

## Proof-dependency audit

`PolynomialPrimeSumBound` is a proposition defined in `FiniteCyclicPhase`.
That makes the *interface* available to `ChenCompleteSum`; it does not supply
an inhabitant. The canonical inhabitant `polynomialPrimeSumBound` is obtained
from `polynomial_addChar_sum_prime`, whose proof belongs to
`PolynomialWeilBound` and is not in Chen's old dependency closure.

The public APIs then factor as follows:

| Unconditional declaration | Conditional implementation retained in `ChenCompleteSum` | Missing input discharged downstream | Correct owner |
|---|---|---|---|
| `chen_prime_base` | `chen_prime_base_of` | `PolynomialPrimeSumBound` | `CompleteExponentialSum` |
| `primePower_completeSum_bound` | `primePower_completeSum_bound_of_primeBound` | `PolynomialPrimeSumBound` | `CompleteExponentialSum` |
| `ack_theorem_2_2_finiteProduct` | `ack_theorem_2_2_finiteProduct_of_primeBound` | `PolynomialPrimeSumBound` | `CompleteExponentialSum` |

The dependency is direct for the prime-base theorem: its conditional form
takes `hWeil : PolynomialPrimeSumBound`. The prime-power estimate invokes the
prime-base estimate in its recursion, so its conditional form must thread the
same hypothesis. The finite-product result applies the prime-power estimate to
each factor, so it has the same transitive requirement. In each case the
unconditional wrapper is obtained by specializing the conditional theorem at
`polynomialPrimeSumBound`.

The old `ChenCompleteSum` production module imports only
`PolynomialCongruence`. A repository-wide inspection of that closure found the
definition of `PolynomialPrimeSumBound`, but no proof of it and no
`polynomial_addChar_sum_prime`. Consequently the three unconditional wrappers
are not proof-realizable in the frozen Chen decomposition without either:

1. importing `PolynomialWeilBound` into Chen, thereby destroying the intended
   hypothesis-parametric boundary; or
2. duplicating the Weil development inside Chen.

This is a module-contract conclusion rather than a claim of logical
independence from Lean's foundations. Under the project's approved theorem
decomposition and sorry-free/no-new-axiom standard, Chen has no admissible term
with which to discharge the hypothesis. The production implementer's blocker
therefore identified a genuine architectural defect that signature stubs could
not reveal.

Keeping all three conditional variants in `ChenCompleteSum` is equally
important: they express the reusable algebraic/recursive Chen argument under
an abstract prime-sum bound. Moving only the unconditional specializations
downstream repairs the defect without weakening, duplicating, or obscuring that
API.

## DAG and ownership audit

The repaired dependency shape is a terminal join:

```text
FiniteCyclicPhase -> PolynomialCongruence -> ChenCompleteSum ------+
                                                                  |
Stepanov auxiliary chain -> PolynomialWeilBound ------------------+--> CompleteExponentialSum
                                                                  |
QuadraticCompleteSum ---------------------------------------------+
```

`CompleteExponentialSum` directly imports `ChenCompleteSum`,
`QuadraticCompleteSum`, and `PolynomialWeilBound`. Neither Chen nor the Weil
chain imports `CompleteExponentialSum`, and no dependency points from the Weil
chain back through this terminal module. The generator's topological and DFS
checks agree that the resulting graph is acyclic.

All reviewed artifacts agree on the repaired ownership:

- the approved 05b prose and `MODULE_LAYOUT.md` assign the abstract
  `_of_primeBound` layer to Chen and the Weil specialization to the terminal
  module;
- `module-map.json` gives Chen only `PolynomialCongruence`, while the terminal
  module imports both Chen and `PolynomialWeilBound`;
- `generate_modules.py` has explicit terminal-owner exceptions for
  `polynomialPrimeSumBound` and the three unconditional wrappers, plus
  regression assertions that the three conditional variants remain in Chen;
- `declaration-modules.tsv` records those exact assignments;
- the generated Chen module contains the three conditional declarations and
  none of the four downstream names;
- the generated terminal module contains `polynomialPrimeSumBound`, all three
  unconditional wrappers, and re-exports access to the conditional APIs; and
- the build report describes the same production-discovered failure and the
  same repair.

Namespace and theorem types remain unchanged. The repair changes only the
import level at which unconditional specializations become available, which is
the semantically correct public API boundary.

## Validation evidence

I ran the following checks from the current blueprint and pinned production
environment:

| Check | Result |
|---|---|
| `python3 blueprint/validation/generate_integrated.py --check` | exit 0; integrated artifact current |
| direct `lake env lean` on `BlueprintIntegrated.lean` | exit 0 |
| direct Lean with `-DrelaxedAutoImplicit=false -DmaxSynthPendingDepth=3 -DmaxErrors=1000` | exit 0 |
| `python3 blueprint/validation/modules/generate_modules.py --check` | exit 0; 29 modules, 867 declarations, DAG acyclic |
| `sha256sum -c blueprint/validation/modules/generated-hashes.sha256` | exit 0; every listed artifact `OK` |
| `python3 blueprint/validation/modules/generate_modules.py --build` | exit 0; full offline build completed, 3446 jobs |
| `lake query TranslationalTilings` in the generated package | exit 0 |
| import-only Lean visibility test for generated Chen | exit 0; conditional names visible, proof and unconditional names correctly unknown |
| import-only Lean visibility test for generated terminal module | exit 0; proof, conditional names, and unconditional names visible |
| exact-type specialization test in the generated terminal module | exit 0; each conditional theorem specializes at `polynomialPrimeSumBound` to its unconditional signature |

The full build and query emitted only the already documented style warnings
caused by long generated source-location/signature lines and the generated
`Main` header. They reported no elaboration, module-resolution, ownership, or
cycle error. Those inherited generated-artifact warnings do not expose a PM1
defect.

The specialization test is signature-compatibility evidence only: because the
generated declarations are axiom stubs, it is deliberately not counted as
proof evidence.

## Referee findings and handoff constraints

There are **zero blocking findings at every severity (P0--P3)**. The repaired
boundary is mathematically motivated, minimally scoped, discoverable, and
compatible with the intended Mathlib-style separation between an abstract
hypothesis-driven theorem and its later concrete instance.

The production handoff should preserve these constraints:

- keep the proposition `PolynomialPrimeSumBound` at its existing foundational
  interface level;
- keep `chen_prime_base_of`,
  `primePower_completeSum_bound_of_primeBound`, and
  `ack_theorem_2_2_finiteProduct_of_primeBound` in `ChenCompleteSum`;
- prove `polynomialPrimeSumBound` from `polynomial_addChar_sum_prime` in
  `CompleteExponentialSum`; and
- define the three unconditional wrappers there by genuine specialization of
  the conditional theorems.

Do not repair production by adding a `PolynomialWeilBound` import to
`ChenCompleteSum`, duplicating the Weil proof, or treating generated axiom
stubs as implementation evidence.

## Final verdict

**APPROVE PM1 for the exact artifact hashes above.** The three unconditional
wrappers cannot be completed under Chen's old approved closure, their repaired
ownership in `CompleteExponentialSum` is correct and acyclic, and all three
`_of_primeBound` variants correctly remain in `ChenCompleteSum`. Any change to
the reviewed hashes or these ownership edges requires fresh review.
