# PM7 independent production rereview: Chen and terminal complete sums

Date: 2026-08-24

Reviewer role: fully author-independent, read-only rereview of the production
`ChenCompleteSum` and `CompleteExponentialSum` modules and of the repaired,
attribute-aware signature validators.  The reviewer authored neither production
module and made no change to any reviewed production or validator source.  This
review applies the project Tau-Ceti-style production standard together with the
library-scale and local-proof rubrics.  Under the PM7 mandate, every P0--P3
finding is blocking.

## Snapshot and scope

The production repository was the dirty, concurrent working tree based at Git
commit `b6744348ec0c2ab44788000b031721b861424c2f`.  Both reviewed modules are
untracked relative to that commit, so this report is bound to their exact bytes:

- `TranslationalTilings/NumberTheory/ChenCompleteSum.lean`:
  `f1abbc61fcfe24e2dd2af845513c1f23c294ae2bcd47b1f8daeffa7a88a4d470`
  (4,071 lines);
- `TranslationalTilings/NumberTheory/CompleteExponentialSum.lean`:
  `49cb393764e53f1e89f373ca09245bb6fbd88fe858e8c77215d463f4da35098c`
  (556 lines).

The relevant validator bytes were:

- canonical integrated generator:
  `58d9f3039e5f56bed18f424810f155d4eea12437038e8378475bbfc577646d79`;
- module generator:
  `e9230f042900319ac1e1cbac42741531f3785f4536e14b7b2c96190afcab2337`;
- canonical 869-row ledger:
  `be8958dd0a96f1b5d97ddba66b1c52a4de74d5161e82d0d5864982958ae5749f`;
- module ownership ledger:
  `8bd2eaabe9c99d04808fbc81d0d7ba4a78e6bdb17bc680b5b02896e922725bc6`;
- module source manifest:
  `77f20a932a9a5821b698691c046802e379e1962c855bb24a7934b28f8981896c`;
- generated-hash manifest:
  `5fbaef2d6cac20c3afa1e011a4c4cc9e27cd63ab54f6bb6a5c0e0b03d1ee0142`;
- generated Chen module:
  `f5778232bf523c31aa66ef3635fc186e17f2e31655c09da2e19998a1fede6f8e`;
- generated terminal module:
  `3e00e09694654c195bfe84bc4ec31b0f1c3b7af66165b694a35d57cb3597248d`.

The repository-wide `blueprint/SNAPSHOT.sha256` describes an earlier global
snapshot and had 31 mismatches in this concurrent tree.  This report therefore
does not claim a global snapshot approval: its review identity is the bounded
hash list above.  The validator-local generated-hash manifest did verify
without error.

## Verdict

**BLOCK / REQUEST CHANGES.**

The prior P2 parser and ownership-ledger defect is genuinely repaired.  The
proofs, exact 60+20 API, definition bodies, attributes, builds, trust audit,
resource policy, and dependency boundary pass.  The prior P3 documentation
defect is materially improved but not fully repaired: three public docstrings
misdescribe their attached declarations.  Since PM7 treats P3 as blocking,
these exact production hashes cannot be approved.

## Blocking finding

### [P3] Three public docstrings state the wrong exported behavior or bound

File: `TranslationalTilings/NumberTheory/ChenCompleteSum.lean`.

1. At line 3479, the docstring for `factorizationScalarLookup` says the
   off-support default is `1`, while the definition is
   `if hp then u ⟨p, hp⟩ else 0`.
2. At line 3492, the docstring for
   `factorizationScalarLookup_of_not_mem` again says the default is `1`, while
   the theorem concludes `factorizationScalarLookup u p = 0`.
3. At line 3915, the docstring for `chenLargePrimeThreshold_le` advertises the
   cutoff `(d - 1) ^ 6`, while the public theorem concludes
   `chenLargePrimeThreshold d ≤ (d + 1 : ℝ) ^ 6`.  The proof contains the
   sharper intermediate `(d - 1) ^ 6`, but that is not the theorem's exported
   conclusion.

The first two comments directly contradict executable reduction and a public
`[simp]` theorem.  The third can mislead a downstream reader about the API they
can rewrite with.  `docBlame` checks presence, not semantic accuracy, so its
clean result does not detect this defect.

Required repair: change the first two occurrences of `1` to `0`, and make the
threshold docstring state `(d + 1) ^ 6` (or change the theorem itself and the
blueprint, which is neither necessary nor recommended).  Then freeze a new
hash and run a separate independent follow-up.

## Prior P2 parser/ledger finding: repaired

The repair was checked at every layer, rather than inferred from the final row
count.

- The canonical parser's declaration-start, named-declaration,
  declaration-kind, and theorem-start regular expressions all accept one or
  more leading `@[...]` attributes before declaration modifiers.
- The theorem-to-stub transformation retains the captured attribute prefix.
- The generator contains an explicit regression set for
  `factorizationScalarLookup_of_mem` and
  `factorizationScalarLookup_of_not_mem`.
- Both names occur at blueprint lines 964 and 971 in the canonical ledger, the
  module ledger, and the generated Chen source.  The generated declarations
  retain `@[simp]`.
- Independent source parsing found exactly 60 explicit public Chen
  declarations and exactly 20 explicit public terminal declarations.  These
  sets equal the two ledger-owned sets with no source-only or ledger-only
  names.
- A Lean environment query confirmed that both declarations belong to the
  `simp` extension in production and in the generated validator package.

`generate_integrated.py --check`, `generate_modules.py --check`, and
`sha256sum -c blueprint/validation/modules/generated-hashes.sha256 --quiet`
all exited zero.  The module check reported exactly 29 modules, 869
declarations, and an acyclic DAG.  The pinned offline validator build completed
successfully at 3,446 jobs.  Its pre-existing generated-source style warnings
do not indicate a signature, ownership, or trust gap.

## Exact API and definition audit: passed

- Generated `#check @name` streams with `pp.universes = true` were compared
  byte-for-byte between the production and validator environments for all 80
  ledger names.  `diff -u` exited zero with empty output.
- Generated `#print` streams were compared byte-for-byte for all 13 owned
  `def`, `abbrev`, and `structure` rows.  `diff -u` again exited zero with
  empty output.  Thus the public data definitions conform in body, not merely
  in type.
- The two attributed lookup theorems are present in both `simp` extensions.
- The public names, binder order, assumptions, conclusions, ownership, and
  imports agree with Chapter 05b and the module manifest.

No extra production export, missing ledger owner, type drift, definition-body
drift, or attribute loss was found.

## Mathematical and proof review: passed

The chapter proof and the production endpoints were reread independently.
The stationary descent has the required nonzero-translate premise at (2.5),
the middle-prime route carries the `hpB` threshold through recursive children,
and the small-prime paired induction keeps the block hypothesis on every use
of (2.14).  The four local-factor regimes have the source's strict and
non-strict endpoints.

The CRT proof establishes the additive-character identity before reindexing by
`ZMod.chineseRemainder`.  The positive/coprime factorization induction handles
prime powers, modulus one, and coprime products; it proves supported scalars
nonzero and transports local primitivity.  The final conditional theorem
applies the prime-power estimate to each supported factor, combines the real
powers back to the modulus, and bounds only the exceptional local-factor
product.

The terminal module discharges `PolynomialPrimeSumBound` with
`polynomial_addChar_sum_prime`, wraps the conditional prime and prime-power
theorems, treats the unique 2-primary quadratic factor separately, and pads
from the actual degree only after the linear, quadratic, and degree-at-least-
three split.  The integral endpoint is the checked transport through
`integralCompleteSum_eq_polynomialCompleteSum` and the polynomial content
bridge.  No circular induction, missing local regime, stronger hidden
hypothesis, vacuous certificate, or reversed inequality was found.

## Dependency boundary: passed

- Importing `ChenCompleteSum` exposes the three `_of_primeBound` declarations
  but Lean reports the unsuffixed `chen_prime_base`,
  `primePower_completeSum_bound`, `ack_theorem_2_2_finiteProduct`, and theorem
  `polynomialPrimeSumBound` as unknown.  Thus the conditional module does not
  import or leak the terminal Weil discharge.
- Importing `QuadraticCompleteSum` leaves both composite quadratic wrappers and
  `CompleteSumFactorizationData` unknown.  Their first common consumer is the
  terminal module, as specified.
- Exact-name search found one downstream use outside the two reviewed files:
  `Analysis/PolynomialRigidity.lean` consumes the unconditional integral
  endpoint.  A downstream build through that target completed successfully at
  3,432 jobs.

The direct project imports match the manifest: Chen imports only
`PolynomialCongruence`; the terminal module imports Chen, Quadratic, and
PolynomialWeil.

## Compilation, documentation-presence, resource, and trust checks: passed

- Chen direct warning-as-error compile: exit 0, no output, 7.24s wall.
- Terminal direct warning-as-error compile: exit 0, no output, 3.25s wall.
- Joint Lake build: success, 3,414 jobs.
- Chen source piped through an appended `#lint only docBlame`: zero errors in
  120 declarations plus 207 automatically generated declarations.
- Terminal source checked the same way: zero errors in 27 declarations plus
  16 automatically generated declarations.
- The retained-command and forbidden-trust scan was empty for `sorry`,
  `admit`, `axiom`, `unsafe`, `opaque`, `native_decide`, placeholders,
  validator imports, `#lint`, `docBlame`, `maxHeartbeats`, and `maxRecDepth`.
- Whitespace scan was empty.  Neither file changes the package's resource
  budget; both retain only the package-wide `relaxedAutoImplicit = false` and
  `maxSynthPendingDepth = 3` settings.
- `#print axioms` on all 80 owned declarations reported only subsets of
  `propext`, `Classical.choice`, and `Quot.sound`.

## Rubric disposition

- Mathematical intent: clear.
- Reusable seams and Mathlib integration: clear; the code uses the project
  polynomial-congruence layer, Mathlib CRT/factorization infrastructure, and
  the separate Weil and quadratic modules at the intended boundaries.
- Public API and theorem shape: clear apart from the P3 documentation finding.
- Module and dependency design: clear.
- Proof architecture, tactic robustness, goal hygiene, and performance:
  clear; no local proof change is requested.
- Cost and durability: clear; no resource override or pathological replay was
  observed.
- Refactor risk: do not refactor the mathematical API during this repair.  A
  three-comment doc-only patch is the bounded correction.

## Acceptance gate

Do not accept Chen hash `f1abbc...d470` as the PM7 production boundary.  Apply
the three doc-only corrections, freeze the resulting bytes, and obtain a
separate independent follow-up which rechecks the exact diff, documentation,
strict direct compilation, the 60+20 API/parser invariant, retained-command
scan, and a proportionate build.
