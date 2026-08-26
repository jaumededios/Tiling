# Independent refereeing standard

This project adapts the public review discipline of the
[Tau Ceti project](https://github.com/TauCetiProject/TauCeti) and its
[review repository](https://github.com/TauCetiProject/TauCetiReview).  In
particular, the project uses Tau Ceti's fixed-rubric, adversarial, clean-room
idea rather than treating successful elaboration or CI as proof that a
formalization says the intended mathematics.  The protocol below is adapted
to a paper formalization and does not claim Tau Ceti certification.

## Separation of roles

1. Blueprint authors decompose the paper, write the complete mathematical
   arguments, and expose the proposed Lean API.
2. Independent blueprint referees are read-only while reviewing.  They check
   the paper, the pinned Mathlib source, and the repository rather than relying
   on the authors' summaries.
3. Authors resolve every finding in `reviews/resolution-log.md`.
4. At least two referees re-read the corrected snapshot.  Approval names the
   inspected snapshot; any material later blueprint change invalidates it.
5. Lean implementation begins only after this gate.  The completed Lean code
   receives a fresh independent review under the same rubrics after all builds
   and linters pass.

Green CI is necessary but never sufficient.  Reviewers actively try to break
the statement and its correspondence with the paper.

The reviewed snapshot manifest includes the production contract
`MODULE_LAYOUT.md`, both validator generators, the strict integrated artifact
and declaration ledger, the module ownership/DAG ledgers, and every generated
module-validation source named by
`validation/modules/generated-hashes.sha256`.  For the final implementation
gate it additionally includes the production Lake/toolchain manifests, the
umbrella, and all 29 genuine source modules.  Generated Lean may use only
exact-type `axiom` stubs for bodyless blueprint theorems; both validation
trees are explicitly outside production source and must not be imported.  The
integrated header repeats all chapter hashes, while both generators compare
their complete outputs byte-for-byte, so stale artifacts fail the gate even
if a reviewer forgets to inspect timestamps.

## Required blueprint rubrics

### Scope and attribution

- Every labelled result in arXiv:2010.03254v3 occurs exactly once in the
  coverage table, with the paper's assumptions and conclusion.
- Every recursively required non-Mathlib result has a proof plan and a module
  home; no prerequisite is silently assumed.
- The paper, adapted sources, and reused Mathlib declarations are credited at
  the declaration or module that depends on them.
- The dependency graph contains no unrelated development or import cycle.

### Mathematical correctness

- Quantifiers, dependence of constants, signs, normalizations, and edge cases
  are compared against the paper line by line.
- Reviewers test empty and singleton tiles, zero periods, dimension zero,
  level zero, degenerate directions, and other boundary values whenever the
  public type permits them.
- A theorem is rejected if it is vacuous, tautological, weaker in the crucial
  direction, or made easy by moving the hard claim into a hypothesis,
  structure field, typeclass, certificate, or unexercised predicate.
- Each changed formulation (for example the `l1` executable bound or a weaker
  Weyl exponent) must have a proved bridge to the paper statement and must be
  shown sufficient for every downstream use.

### Lean statement and API correctness

- Every displayed public definition and declaration must be literal Lean 4
  syntax that elaborates against the pinned toolchain.  Ellipses, pseudocode,
  proof holes, invented imports, and unspecified instances fail the gate.
- The dependency-ordered validator and declaration ledger under `validation/`
  must be regenerated from, and hashed with, the reviewed snapshot.  Strict
  generation and pinned-toolchain elaboration must both succeed with
  `relaxedAutoImplicit=false` and `maxSynthPendingDepth=3`.  The independent
  module-aware validator must also assign every ledger row to exactly one
  frozen production module and build the complete `TranslationalTilings`
  umbrella through its acyclic direct-import graph.  An isolated file, a
  hand-written substitute signature, a global classical-instance shim, a
  module-stripping monolith by itself, or a vacuous stand-in such as
  `PairwiseIncommensurable := True` is not evidence for any declaration.
- Public structures expose the minimum characteristic data.  They may not
  carry an arbitrary result, period, decomposition, or correctness theorem
  merely to make a later theorem immediate.
- Characteristic lemmas, extensionality principles, and stable simplification
  normal forms are planned where downstream proofs need them.  Implementation
  details remain private.
- Names describe conclusions and follow Mathlib conventions; notation is
  scoped and minimal; public declarations and modules have documentation.

### Reuse, generality, and placement

- Every proposed helper is searched against both the pinned Mathlib source and
  pre-existing project code.  A reuse finding names the exact replacement and
  its required adapter; vague assertions that Mathlib “probably has it” do not
  count.
- Direct duplication of an applicable Mathlib theorem is blocking.
- Results use the weakest natural assumptions already required by their proof,
  without speculative abstraction that harms the paper-facing API.
- General lemmas live below tiling-specific modules and imports are no broader
  than needed.

### Constructivity and algorithms

- A claimed algorithm is executable data (`Bool` or a finite computation),
  with soundness and completeness theorems.  Classical `Decidable`, quotient
  choice, or a witness supplied as input is not an algorithm.
- Every finite search has an explicit finite type or enumeration and a theorem
  that it contains all candidates.
- Quantitative bounds are explicit computable functions with the exact allowed
  parameter dependence.  Complexity claims name a cost model and are not
  inferred from mere termination.

### Proof quality and final trust

- Proofs are robust under harmless refactors: no accidental definitional
  equality, uncontrolled simplification, or giant opaque tactic block.
- Repeated reasoning becomes a named reusable lemma; genuinely subtle steps
  receive local mathematical comments.
- The final audit checks for `sorry`, `admit`, project axioms, theorem-shaped
  `opaque` declarations, vacuous definitions, and unexpected axioms in every
  exported paper theorem.

## Finding format and severity

Every finding records:

1. severity (`P0` invalidates a main result, `P1` blocks implementation,
   `P2` materially harms the API/proof, `P3` is a localized improvement);
2. the user-visible or mathematical risk;
3. an exact file, heading, declaration, or line and concrete evidence;
4. a specific repair and, when relevant, the Mathlib replacement;
5. the disposition in `reviews/resolution-log.md`.

Referees return `approve`, `request changes`, or `block`.  Every P0--P3
finding blocks this formalization until it is repaired and independently
cleared.  The acceptance gate therefore requires no unresolved finding at
any severity and two approvals of the same corrected snapshot.

For each candidate snapshot, the two pre-proof referees must independently
run all of the following, not merely trust author logs:

```bash
sha256sum -c blueprint/SNAPSHOT.sha256
python3 blueprint/validation/generate_integrated.py --check
cd /home/codex/Documents/Codex/2026-08-14/Tiling
lake env lean -DrelaxedAutoImplicit=false -DmaxSynthPendingDepth=3 \
  -DmaxErrors=1000 \
  /home/codex/Documents/Codex/2026-08-24/usi/blueprint/validation/BlueprintIntegrated.lean
cd /home/codex/Documents/Codex/2026-08-24/usi
python3 blueprint/validation/modules/generate_modules.py --check
sha256sum -c blueprint/validation/modules/generated-hashes.sha256
python3 blueprint/validation/modules/generate_modules.py --build
```

One referee concentrates on mathematical fidelity and recursive proof
closure; the other concentrates on Lean/Mathlib suitability, production
module boundaries, package options, and trust.  Both still read every
manifest payload and may report findings in either category.

## Final Lean referee pass

After implementation and before claiming completion, independent referees
repeat these checks on the source rather than the blueprint.  In addition to
`lake build`, they run project linters, inspect theorem statements with
`#check`/`#print`, review `#print axioms` output, search the pinned library for
duplication, and spot-check downstream use so that definitions are validated
by integration rather than by author prose alone.

They also compile every production module with `warningAsError`, verify the
869-row blueprint-to-production type comparison, reject imports from either
validator tree, and check public documentation.  A successful build of the
older `Tiling` target is not a substitute for building the independent
`TranslationalTilings` library and umbrella.
