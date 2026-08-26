# PM4 and PM5 independent production rereview

Date: 2026-08-24 UTC.

## Verdict

**APPROVE for the exact bounded snapshot below.** I found no P0, P1, P2, or
P3 defect in the PM4 target-periodicity repair, its complete production caller
chain, the PM5 Hasse-derivative API repair, or the attributed-declaration
parser regression. Because this review was commissioned with every severity
blocking, the verdict was held until `Algorithms.lean` had a source-current
strict build and an explicit sole-owner freeze.

The PM4 repair is substantive rather than cosmetic. The new hypothesis
`hE : SetScalarPeriodic ell E` is converted to periodicity on the weak lattice
and is used in both directions of both exhaustive branches of the real proof.
It excludes the former singleton countermodel, agrees with the periodic-target
step used in the paper, and is passed by every direct and transitive consumer.

PM5 is also exact: a fresh `Lean.Meta.isDefEq` comparison of the complete
elaborated regenerated-validator and production types of
`hasseDeriv_eval_frobenius` returned `true`.

This is deliberately a hash-bounded PM4/PM5 approval, not a new whole-project
snapshot approval. The historically frozen `blueprint/SNAPSHOT.sha256` is not
rewritten merely for a pending follow-up; the resolution log explicitly makes
the exact external review hashes authoritative in that situation.

## Reviewed identity

The production checkout was at Git commit
`b6744348ec0c2ab44788000b031721b861424c2f`, using Lean 4.33.0 and Mathlib
commit `db584cd6d46c92f209a44c0f1c829460d327499d`. The production and blueprint
trees contain concurrent uncommitted work, so the verdict is tied to the
following file hashes rather than to repository cleanliness.

| Artifact | SHA-256 |
|---|---|
| `blueprint/05a-weil-stepanov.md` | `23f3373f2f8c6f1bc5d7ac91e541a7cbb875f039c26b478fa70608a0d99c27d5` |
| `blueprint/06-weak-periodicity.md` | `4ad0ec2879696545635873cb4b6fab5ff9fe85bb902487927bd189221c4ac23a` |
| `blueprint/07-periodic-completion.md` | `8d1f5c269f26b6ded57492026a5c6dd65f659fdd42669d1797e69607a4f74afa` |
| `blueprint/08-algorithms.md` | `fb2e088b3a24017c4e393e4c2314e4df6648ea775ad41e238421b0ff2f0e43ea` |
| `blueprint/09-main-results.md` | `0468a1bc01ad7a76a4e135867ca23b531d7494121472e5f7153ff45d6f937846` |
| local arXiv v3 PDF | `2a3f035bb13718e47087a27233f5339ed8feb9fe8dabccb9dec93a95fae2a0a9` |
| integrated generator | `58d9f3039e5f56bed18f424810f155d4eea12437038e8378475bbfc577646d79` |
| integrated declaration ledger | `be8958dd0a96f1b5d97ddba66b1c52a4de74d5161e82d0d5864982958ae5749f` |
| integrated validator | `9dc79c498af10ea4ee0a0c66d98fffacb0534916e2f9ba0d2c1ae71f8a9e7d12` |
| module generator | `e9230f042900319ac1e1cbac42741531f3785f4536e14b7b2c96190afcab2337` |
| module declaration ledger | `8bd2eaabe9c99d04808fbc81d0d7ba4a78e6bdb17bc680b5b02896e922725bc6` |
| generated-hash manifest | `5fbaef2d6cac20c3afa1e011a4c4cc9e27cd63ab54f6bb6a5c0e0b03d1ee0142` |
| generated `WeakPeriodicity.lean` | `50b05d0f06673b1f7847f497ebebb6d6d9e995f11ce9f45a9db102b34f14b98d` |
| generated `PeriodicCompletion.lean` | `969b4b1248a45d7b07850c54bbbdd200adcc7af7f058796f723fe0371718a3e6` |
| generated `Algorithms.lean` | `0f74852831ed0a63ad674c7561a29eba69227f67e67ffdd0855418cac971049d` |
| generated `Main.lean` | `250b823e47cf5a9190b18a3ac13e7cd667af09dde2b4596b2ef4140c7d349be6` |
| generated `HasseMultiplicity.lean` | `b45c7ed8f846b3118b78aba289bdd6513579bcc74d0ea2b1357fcffadeb0c31c` |
| generated `ChenCompleteSum.lean` | `f5778232bf523c31aa66ef3635fc186e17f2e31655c09da2e19998a1fede6f8e` |
| production `WeakPeriodicity.lean` | `249885c54a6d1db40c048d7be2f39d3bb91a6ffe4469e76b713f2de4d188d950` |
| production `PeriodicCompletion.lean` | `50042b2e2a33b99a340f49373d2e36b0dae7bd3e234171d7f1134056170504d6` |
| production `Algorithms.lean` | `652c9cb48810aa1f7634bcabb2bb0bcaf3b86c4eb14ece52f1596731cd68930b` |
| production `Main.lean` | `410366b9f079319164e0ba73c15b1a83d2902a39c6c838cf09b6fa567b742536` |
| production `HasseMultiplicity.lean` | `75e3d66065bb209d8509e841d42cd3c7c2c5aaea54918186be50694689f67c1f` |

I made no edit to a reviewed chapter, validator, generator, ledger, manifest,
production source, or resolution log. The only persistent file written by this
review is this report.

## PM4: the repaired theorem is true for the stated reason

### The hypothesis reaches the actual proof obligation

`GroupedStructureDecomposition` does not store target periodicity. Its data
controls the decomposition functions and their periods, but without a separate
certificate it cannot identify `1_E` at two points of a weak-lattice coset.
The added `hE` is therefore necessary proof data, not redundant API noise.

The production proof has the following checked flow.

1. `setPeriodicOn_weakLattice_of_scalarPeriodic` at
   `WeakPeriodicity.lean:1452` takes `hE`, uses
   `weakLattice_le_scalar`, and produces
   `SetPeriodicOn (weakLattice ...) E`.
2. `coset_supremumOne_periodic` at line 1655 forms this result as `htarget`.
   In both implications of its final equivalence it passes
   `htarget period hperiodMem y` to
   `setIndicator_eq_of_target_and_phi_eq`; target and all component indicators
   are therefore compared at exactly the same translated points.
3. `coset_allSuprema_lt_one_periodic` at line 1752 does the same in the
   complementary branch, again in both implications.
4. The public theorem at line 1849 exhausts the cases
   `exists j, sSup (range ...) = 1` and `forall j, sSup (range ...) < 1`, and
   passes `hE` to the corresponding helper. Thus no branch silently falls back
   to the old unsupported statement.

The complete public type of `coset_one_dimensional_periodicity`, recreated
from the current generated validator, is definitionally equal to the
production declaration according to `Lean.Meta.isDefEq`.

### The old singleton countermodel is excluded

I replayed the decisive obstruction in a fresh strict Lean input. For
`E = {0} : Set Plane` and `ell = 1`, choose the nonzero first-coordinate vector
`z`. Instantiating scalar periodicity at `x = 0` would assert

```text
z in {0} iff 0 in {0},
```

whose sides are false and true. Lean proves

```lean
example : ¬ SetScalarPeriodic 1 ({0} : Set Plane) := by
  intro h
  let z : Plane := fun i => if i = 0 then 1 else 0
  have hz : z ≠ 0 := by
    intro hz
    have hz0 := congrFun hz (0 : Fin 2)
    simp [z] at hz0
  have hbad := h (0 : Plane) z
  simp [hz] at hbad
```

under `-DwarningAsError=true`. Consequently the former
`F = {0,e_1}`, `A = E = {0}`, one-direction, zero-`phi` countermodel cannot
instantiate the repaired theorem: it fails exactly the newly explicit `hE`
hypothesis.

### The repair agrees with the paper

I inspected the rendered local arXiv v3 PDF rather than relying on the
blueprint summary. Printed page 16 contains the end of Proposition 4.1 and
Lemmas 4.2--4.3. Proposition 4.4 begins on printed page 17, which is PDF page
index 16 in a zero-indexed renderer. That page states

```text
Lambda subset q Z^2 subset ell Z^2
```

and immediately before equation (29) uses three facts: `q` is a multiple of
`ell`, `e` is a multiple of `q`, and `E` is `ell Z^2`-periodic. It then replaces
the target indicator along `x + s e + t q N M h_1` by its value at `x`.
The Lean hypothesis `SetScalarPeriodic ell E`, restricted along
`weakLattice <= scalarLattice ell`, is precisely this paper step. Printed page
18 carries the two subsequent periodicity branches. The repaired signature is
therefore faithful to the actual proposition's ambient assumptions.

## PM4: complete caller audit

| Consumer | Evidence that `hE` is available and used |
|---|---|
| `exists_quantitativeWeakPeriodData` | The proof first constructs `D0` from the empty target only to freeze tile-dependent canonical directions. For arbitrary `E,A`, it constructs `D1` from `hE` and `htile`, proves the canonical directions agree, calls `coset_one_dimensional_periodicity D1 hell hE` at line 2344, and transports the result to the fixed data. This preserves the required quantifier order: the data precedes `E,A`, while the callback explicitly receives `hE`. |
| Theorem 1.4 wrappers | `theorem_1_4_uniform` quantifies `SetScalarPeriodic ell E` in its callback and delegates to `exists_quantitativeWeakPeriodData`; its concrete l1 and Euclidean wrappers pass their `hE`. Their public types are unchanged by PM4. |
| `Main.proposition_4_4` | The paper-facing declaration at `Main.lean:239` now binds `hE` and its complete body is `coset_one_dimensional_periodicity D hell hE` at line 246. A fresh exact-type `Meta.isDefEq` comparison with the generated validator returned `true`. |
| `exists_directionalTilingDecomposition_of_quantitativeData` | The bridge already receives `hE`. At lines 113--121 it lifts it to `SetScalarPeriodic (ell * W.multiplier) E`, stores that in `DirectionalTilingDecomposition.target_periodic`, and retains `htile`. Its complete public type is definitionally equal to the generated validator. |
| `quantitative_periodic_tiling_l1` | After normalizing the tile, it obtains uniform data, calls `hW E A0 hE htile0` at line 1732, and passes the same `hE` to the directional bridge at lines 1733--1735. Empty and singleton branches handle the target directly. |
| `directionalDecomposition_uniform_classifier` | The frozen production theorem at `Algorithms.lean:3364` accepts `hE`, builds the canonical grouped decomposition with it, calls the repaired core as `coset_one_dimensional_periodicity G E.period_pos hE` at line 3435, and passes `hE` to the directional bridge at line 3442. Its exact generated and production types are definitionally equal. |

An exhaustive production search found no other direct use of
`coset_one_dimensional_periodicity`. The two direct callers are the uniform
constructor and the Algorithms classifier; Main is the paper-facing wrapper,
and PeriodicCompletion consumes the uniform callback through its declared
interface.

## PM5: exact elaborated API equality

The repaired blueprint and regenerated validator now state the binders in the
same order as production:

```lean
{K : Type*} [Field K] {p : Nat} [CharP K p]
```

I imported frozen production `HasseMultiplicity`, declared a fresh expected
constant with the complete current regenerated-validator type, retrieved both
`ConstantInfo.type` values from the environment, and ran
`Lean.Meta.isDefEq`. The strict check logged

```text
PM5 Meta.isDefEq = true
```

A separate fully elaborated `#check @...` comparison with universe printing
also produced an empty diff. This closes the former `{p}{K}` versus `{K}{p}`
public-API mismatch; it is not merely a proposition-level equivalence claim.

## Attributed parser and 869-row ledger

The canonical parser defines

```python
DECL_ATTRIBUTES = r"(?:@\[[^\]\n]+\]\s+)*"
```

and prepends it to the declaration-recognition, named-declaration, declaration
start, and checked-body patterns. Its executable regression set explicitly
requires both

```text
TranslationalTilings.factorizationScalarLookup_of_mem
TranslationalTilings.factorizationScalarLookup_of_not_mem
```

The canonical and module ledgers each have 870 physical lines: one header and
869 declarations. The canonical split is 858 public, one private, and ten
anonymous declarations; by representation it is 356 definitions, 56 checked
bodies, and 457 exact-type axiom stubs. The two attributed lookup theorems are
separate public `checked-body` rows at Chapter 05b lines 964 and 971 and appear
as separate `@[simp] theorem` blocks in generated `ChenCompleteSum.lean`.
Thus the attribute syntax no longer causes the first declaration to absorb or
hide the second.

## Executable evidence

The following fresh checks passed on the hashes recorded above.

```text
python3 blueprint/validation/generate_integrated.py --check
python3 blueprint/validation/modules/generate_modules.py --check
sha256sum -c blueprint/validation/modules/generated-hashes.sha256
lake env lean -DwarningAsError=true /absolute/path/BlueprintIntegrated.lean
python3 blueprint/validation/modules/generate_modules.py --build

lake env lean -DwarningAsError=true -Dweak.linter.unusedDecidable=true
  TranslationalTilings/Algorithms.lean
lake env lean -DwarningAsError=true -Dweak.linter.unusedDecidable=true
  TranslationalTilings/Main.lean
lake build TranslationalTilings.Algorithms TranslationalTilings.Main
```

The module check reported `29 modules; 869 declarations; DAG acyclic`; every
generated hash verified; the strict integrated validator produced no output;
the full generated module build completed successfully with 3446 jobs; and the
frozen Algorithms/Main target build completed successfully with 3461 jobs.
I also independently reran strict direct compiles and Lake targets for frozen
WeakPeriodicity, PeriodicCompletion, and HasseMultiplicity.

Appending `#lint only docBlame` in ephemeral stdin checks found zero errors in
all five production modules: 145 declarations in WeakPeriodicity, 105 in
PeriodicCompletion, 261 in Algorithms, 30 in Main, and 72 in
HasseMultiplicity. The generated-module build still reports the project's
documented generated long-line/header style warnings; the strict integrated
artifact and all reviewed production modules are warning-free, and no PM4 or
PM5 declaration introduces such a warning.

Fresh `Meta.isDefEq` checks returned `true` for all five PM4 boundaries:

```text
coset_one_dimensional_periodicity
exists_quantitativeWeakPeriodData
exists_directionalTilingDecomposition_of_quantitativeData
directionalDecomposition_uniform_classifier
proposition_4_4
```

The PM5 comparison returned `true` separately. `#print axioms` for these
production results, both quantitative terminal consumers, and
`hasseDeriv_eval_frobenius` reports only `propext`, `Classical.choice`, and
`Quot.sound`. A static scan of every reviewed production source found no
`sorry`, `admit`, declared `axiom`, `unsafe`, `native_decide`,
`maxHeartbeats`, `maxRecDepth`, resource override, validator import, or
retained audit command.

## Findings by severity

### P0

None.

### P1

None.

### P2

None.

### P3

None.

The former PM4 P0 and PM5 P1 are resolved on the exact hashes above. No
additional refactor is required for these repairs.
