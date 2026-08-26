# Independent mathematical review: PM1 Chen/Weil repair

## Verdict

**BLOCK.**  The PM1 module-boundary repair is mathematically correct and its
dependency graph is acyclic, but I found one P3 Lean-suitability defect in the
only proof which constructs the incoming `PolynomialPrimeSumBound`.  The
blueprint advertises the term

```lean
letI : NeZero p := ⟨Fact.out.ne_zero⟩
```

and says that this is the explicit bridge used by
`polynomialPrimeSumBound`.  Under the frozen strict Lean 4.33 environment that
term does not elaborate: the type of `Fact.out` is not determined when field
notation `.ne_zero` is processed.  The annotation
`(Fact.out : p.Prime).ne_zero` repairs it.  Because the review protocol makes
every finding at every severity blocking, PM1 cannot be approved until that
exact bridge is repaired in the blueprint and the corrected artifacts are
regenerated.

Apart from this localized finding, I found no mathematical, dependency,
statement, ownership, or circularity defect in PM1.

## Reviewed uncommitted artifacts

This report reviews the current uncommitted corrected PM1 artifacts, not the
older common snapshot named by `blueprint/SNAPSHOT.sha256`.  The relevant
identity is:

| Artifact | SHA-256 |
|---|---|
| `blueprint/05a-weil-stepanov.md` | `ec4ef69159642b17d44aa485b6e1eaa0e953f1d271461ed9c1765a16e1fc57da` |
| `blueprint/05b-chen-complete-sums.md` | `2fcfecf35daddd6f500a4da80c5296442c6566eb7b81f9d36fa55fe8bcbcb000` |
| `blueprint/MODULE_LAYOUT.md` | `b944e6fa0580f2d1af6f1210b83005a6035b17045da5eb91c764c6857ef45428` |
| `blueprint/COMPARATOR.md` | `5375f6c9aead8c0790681ad1326bdac227df9cef791b1d1c4d80811dfaa7ccb5` |
| `blueprint/README.md` | `6a77334dfdf9a683c27b4cea05863153196e7d0e55d88b09447a685f8ba8a9e3` |
| `blueprint/validation/modules/module-map.json` | `2703ec964cd52d577cf07331444a57ceb5cc038da4203bdc63d205311598d26a` |
| `blueprint/validation/modules/generate_modules.py` | `e0e71c95379f7c490b9f6d95f404908410debee92961444b31c3773347b7cf8c` |
| `blueprint/validation/modules/declaration-modules.tsv` | `5c16e9f00b55b3a578b22edf5a8b8173e5f643c0ea42f7ae4b7e7ae0284fba4c` |
| `blueprint/validation/modules/module-sources.tsv` | `9d4063be87301808a5f224d17733731a054f4c398cf9651449049c346b01e3bb` |
| generated `ChenCompleteSum.lean` | `4aa2b774b9f21d00fce5fda2a1e5e9387f4dbcec8af52898a11f65a28f6df239` |
| generated `PolynomialWeilBound.lean` | `b1379aa6cd282bb97cfb7bb30b3c26411fd55392cd8b4c34e76b2f6b3be62971` |
| generated `CompleteExponentialSum.lean` | `6fccdf2dfddd2ee2df906adfd5e12bb02bb540c4c757a83182ef5cb49d4037ec` |
| `blueprint/validation/modules/build-report.md` | `d1f074004f844f33743b4b3dee6fd71eaee1c4de5cd0beb3897f625354b581db` |
| `blueprint/validation/BlueprintIntegrated.lean` | `2846cc0186f6c023bfdf1a3ca2e7eed296dccb8a47e21a4f8c785e116952947c` |
| `blueprint/validation/declaration-coverage.tsv` | `dce11a384c52166cd105f47db53dc0923befa3027f7b2cdc7711bcc6140905d7` |
| generated hash manifest | `3a1108b7efeef8610d8f559d634da172c3f36f147eded5ab1bf66a0c9a0096a3` |
| PM1 resolution log | `31ff049a84543166a5a4fbd8b01bec97da1c2fe6331d37be91cd04234d67dc25` |
| first independent PM1 report | `9c8c7220e73a9a8fc8bc69b6b7ba1108723da093cc28a077c5ee6f89120aff7b` |

The production repository was dirty and under concurrent implementation.  I
made no edit to it, the blueprint chapters, either validator, any generated
module, or the old common snapshot.  This report is a new review artifact and
is not evidence about theorem proofs.

## Scope and trust boundary

I read all of `05a-weil-stepanov.md` and all of
`05b-chen-complete-sums.md`, together with the complete module contract, the
comparator, the relevant README material, the module map, all ownership and
regression code in the module generator, every Chapter 05b ownership row, the
module-source ledger, the three generated modules at the repaired join, the
build report, the PM1 resolution entry, and the first independent PM1 report.

The generated theorem declarations are validator-only axioms.  I used them
only as exact signature and visibility evidence.  In particular, I did not
treat the generated axiom `polynomialPrimeSumBound` as evidence that the Weil
bridge can be proved.  Instead I separately tested that bridge from the
prerequisite imports, which is what exposed the finding below.

## Mathematical and dependency audit

### Conditional chain

The conditional decomposition is mathematically sufficient:

1. `chen_prime_base_of` takes exactly
   `hWeil : PolynomialPrimeSumBound`.  The blueprint explains that the
   trivial bound supplies the first side of its minimum and `hWeil` supplies
   the prime-field Weil side.
2. `primePower_completeSum_bound_of_primeBound` threads the same hypothesis
   through the exponent-one base and the stationary prime-power recursion.
   Its remaining large-, middle-, and small-prime steps are coefficient,
   congruence, valuation, root-mass, and real-inequality results already owned
   by the conditional Chen closure.
3. `ack_theorem_2_2_finiteProduct_of_primeBound` applies that conditional
   prime-power result to the support-indexed CRT factors and combines them by
   the exact rpow product.  It therefore needs no new analytic input beyond
   the same `hWeil`.

Their conclusions are definitionally the same as those of
`chen_prime_base`, `primePower_completeSum_bound`, and
`ack_theorem_2_2_finiteProduct`, respectively, after supplying the first
hypothesis.  A strict Lean test confirmed all three specializations.

### Concrete Weil inhabitant

`PolynomialPrimeSumBound` asks, for `p` with `[Fact p.Prime]`, for exactly the
standard-character estimate proved by
`polynomial_addChar_sum_prime`, whose API instead asks for `[NeZero p]` and
`hp : p.Prime`.  Primality supplies the missing instance.  With the explicit
annotation, the complete bridge is:

```lean
theorem polynomialPrimeSumBound : PolynomialPrimeSumBound := by
  intro p _ f hpos hsmall
  let _ : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  exact polynomial_addChar_sum_prime
    (Fact.out : p.Prime) f hpos hsmall
```

I compiled this body after importing only `ChenCompleteSum`,
`QuadraticCompleteSum`, and `PolynomialWeilBound`, not
`CompleteExponentialSum`.  I then used this local proved inhabitant to compile
all three wrapper specializations.  This establishes the mathematical and
type-theoretic sufficiency of the repaired join without relying on the
terminal module's validator axiom.

### Acyclicity and ownership

The relevant direct graph is:

```text
FiniteCyclicPhase -> PolynomialCongruence -> ChenCompleteSum ------+
                                                                  |
Stepanov chain -> PolynomialWeilBound ----------------------------+--> CompleteExponentialSum
                                                                  |
FiniteCyclicPhase -> QuadraticCompleteSum ------------------------+
```

`ChenCompleteSum` imports only `PolynomialCongruence`.  Consequently it sees
the proposition `PolynomialPrimeSumBound`, which is defined in
`FiniteCyclicPhase`, but it sees neither `polynomial_addChar_sum_prime` nor a
proof of the proposition.  Importing generated `ChenCompleteSum` confirms
that the proposition and all three conditional declarations are visible,
while `polynomialPrimeSumBound` and all three unconditional wrappers are
unknown identifiers there.

`CompleteExponentialSum` directly imports both independent proof branches and
the quadratic low-degree branch.  Neither branch imports the terminal join,
and the generator's topological-order and DFS checks report an acyclic graph.
The repair therefore introduces no circular proof or project import.

The ownership ledger and generator regression agree exactly:

| Declaration family | Owner |
|---|---|
| `PolynomialPrimeSumBound` proposition | `FiniteCyclicPhase` |
| three conditional Chen declarations | `ChenCompleteSum` |
| `polynomialPrimeSumBound` proof | `CompleteExponentialSum` |
| three unconditional wrappers | `CompleteExponentialSum` |

This is the minimal correction.  Importing `PolynomialWeilBound` into
`ChenCompleteSum` would erase the reusable hypothesis-parametric boundary;
duplicating the prime theorem would be worse and is unnecessary.

### Exhaustion of other Weil-dependent declarations

I checked every Chapter 05b ownership row, not only the regression's seven
names.  No other unsuffixed Weil-dependent theorem is stranded in the Chen
closure:

- the congruence, stationary, root-mass, real-inequality, CRT, content, and
  local-factor lemmas in `ChenCompleteSum` are independent of the prime Weil
  inhabitant;
- the entire quadratic/linear branch is independently owned by
  `QuadraticCompleteSum`;
- `polynomialCompleteSum_effective` and
  `integral_complete_exponential_sum_effective`, together with their
  `_of_primeBound` forms and degree-padding lemmas, already live in
  `CompleteExponentialSum`, where both the Chen and quadratic inputs are
  visible.

Thus the three moved declarations are exactly the misplaced unsuffixed
wrappers discovered by production.

### Terminal paper API

PM1 changes only declaration ownership and the import level at which the
unconditional specializations become visible.  Namespace, binder order,
hypotheses, conclusions, constants, exponents, and theorem names are
unchanged.  In particular, the terminal
`polynomialCompleteSum_effective` and
`integral_complete_exponential_sum_effective` statements retain the exact
degree-only constant and exponent used by the comparator's Lemma 4.2 chain.
The downstream `CirclePolynomial` module still imports only
`CompleteExponentialSum`, so the paper-facing analytic API is preserved.

## Blocking finding

### PM1-M1 [P3] -- advertised `Fact.out.ne_zero` bridge does not elaborate

**Locations:** `blueprint/05b-chen-complete-sums.md`, in the ownership and
module-boundary discussion immediately after `polynomialPrimeSumBound`; and
the C2 entry of `blueprint/reviews/resolution-log.md`.

**Evidence:** With the generated terminal module imported under
`relaxedAutoImplicit=false`, the blueprint's literal bridge fragment

```lean
example : PolynomialPrimeSumBound := by
  intro p _ f hpos hsmall
  letI : NeZero p := ⟨Fact.out.ne_zero⟩
  exact polynomial_addChar_sum_prime Fact.out f hpos hsmall
```

fails with:

```text
Invalid field notation: Type of Fact.out is not known; cannot resolve field
`ne_zero`
```

This gap is invisible to both validators because
`polynomialPrimeSumBound` is currently a bodyless exact-type axiom stub.

**Repair:** Give `Fact.out` the expected prime type explicitly.  Preferably
make `polynomialPrimeSumBound` the checked-body theorem displayed above, using
`let _ : NeZero p` to avoid the proof-valued `letI` style warning.  Update the
prose and C2 resolution wording, regenerate the integrated and module-aware
artifacts, and rerun both PM1 reviews.  The corrected body and all three
specializations already compile in the pinned environment, so the blast
radius is limited to this bridge and generated hashes; public theorem types
do not change.

## Validation results

| Check | Result |
|---|---|
| integrated generator `--check` | exit 0 |
| direct pinned Lean on `BlueprintIntegrated.lean` | exit 0 |
| explicit strict-option pinned Lean on the integrated artifact | exit 0 |
| module generator `--check` | exit 0; 29 modules, 867 declarations, DAG acyclic |
| generated SHA-256 manifest | exit 0; every entry `OK` |
| complete offline module generator `--build` | exit 0; 3446 jobs |
| generated-package `lake query TranslationalTilings` | exit 0 |
| positive Chen-only visibility check | exit 0; proposition and three conditional declarations visible |
| negative Chen-only visibility checks | expected exit 1; proof and three unconditional declarations each unknown |
| exact three-wrapper specialization at the generated terminal axiom | exit 0 |
| literal blueprint `Fact.out.ne_zero` bridge | **exit 1**, PM1-M1 |
| explicitly typed bridge, using only the three prerequisite imports | exit 0 |
| explicitly typed bridge plus all three wrapper specializations, without importing the terminal module | exit 0 |

The module build and query emit only the already documented generated-source
long-line/header warnings.  Those warnings are outside production and are not
a PM1 mathematical or dependency finding.

## Rubric disposition

- Mathematical intent: clear after the conditional/concrete split.
- Reusable seam: clear; `PolynomialPrimeSumBound` is the appropriate abstract
  boundary.
- Public API and theorem shape: clear; terminal types are preserved.
- Module and dependency design: clear and acyclic.
- Mathlib integration: clear for PM1; the bridge uses the existing project
  prime theorem and standard `Fact`/`NeZero` instances.
- Proof architecture: one P3 checked-body gap, PM1-M1.
- Cost and durability: clear; the repair localizes the heavy Weil import to
  the terminal join.
- Refactor risk: clear provided the public types remain frozen and only the
  bridge body/prose is repaired.

## Final disposition

**BLOCK PM1 on PM1-M1.**  The conditional Chen mathematics, the three
specializations, the terminal ownership, the no-circularity claim, and the
paper-facing terminal API are all correct.  Approval requires the one-line
prime-type annotation (ideally as a checked proof body), regenerated strict
artifacts, and fresh review of the resulting hashes.
