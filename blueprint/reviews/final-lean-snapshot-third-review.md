# Third independent Lean/Mathlib snapshot review

## Verdict

**BLOCK. Production Lean must not begin from this snapshot.**

The candidate is the 62-entry manifest `blueprint/SNAPSHOT.sha256`, whose
SHA-256 is

```text
de3b3f3d3625cfc6b17ea3965392e1e2aa2776b4beeb9d12ddf6ad0bddbc96c9
```

All 62 payload hashes verify, both before and after this review.  The strict
integrated validator, the independent module generator and hash validator, the
full offline 29-module umbrella build, and the registered-library query all
succeed against Lean 4.33.0 and Mathlib commit
`db584cd6d46c92f209a44c0f1c829460d327499d`.

There is nevertheless one unresolved P1.  The snapshot expressly claims to
compare arXiv:2010.03254v3 and to export stable paper-numbered declarations,
but four intermediate results use numbering from an earlier draft.  This is
not merely an imprecise citation in prose: the wrong numbers are frozen into
the public Lean names, comparator, chapter coverage, declaration ledgers, and
generated module API.  In the most hazardous case, the declaration named
`theorem_5_3` is actually v3 Theorem 5.4, while v3 Corollary 5.3 is represented
as `corollary_5_2`.  That violates this snapshot's own requirement that every
labelled v3 result occur exactly once with the paper's label.

I found no P0 and no additional P2 or P3 finding.  In particular, the earlier
FLSR1, FLSR2, FM1, and FMSR1 blockers are substantively repaired.  Successful
elaboration here is signature evidence only: the 458 validator axioms are not
proof evidence and were not treated as such.

## Review identity, scope, and method

This is a fresh read-only review of the manifest candidate, not a review of an
author summary or a continuation of the prior reports.  I read every manifest
payload.  The generated Lean sources were checked both as complete manifest
payloads and against their Markdown provenance, ownership ledger, generator,
and hashes.  I also read the full 28-page v3 paper extraction and checked the
relevant assertions directly against the v3 TeX source
`structure_tilings.tex` from `2010.03254v3.tar`.

The pinned production checkout was
`/home/codex/Documents/Codex/2026-08-14/Tiling` at commit
`b6744348ec0c2ab44788000b031721b861424c2f`.  It was already dirty before this
review:

```text
 M Tiling.lean
 M Tiling/Basic.lean
?? Tiling/Geometry/
?? Tiling/Topology/
?? blueprint/
```

I did not edit the Tiling checkout and did not edit any manifest-listed file.
The only file added by this review is this report, which is not in the
candidate manifest.

The audit covered:

- theorem fidelity, quantifiers, dependencies, bounds, edge cases, and all
  paper-facing aliases;
- every proposed definition and public declaration, including computability
  boundaries and certificate fields;
- all 857 declaration-ledger rows, ownership assignments, generated
  declarations, visibility classifications, and source coordinates;
- direct project imports, the 29-module DAG, umbrella reachability, package
  options, second-library registration, and the future `lakefile.toml` patch;
- likely reuse and name conflicts in pinned Mathlib and the dirty local
  project; and
- validator and future-production trust boundaries.

## P1 finding

### FLSR3-1 (P1): the paper-facing API uses pre-v3 numbering for four v3 results

**Risk.**  A user importing `TranslationalTilings.Main` would receive a public
API which claims the wrong correspondence to the explicitly targeted paper
version.  The names are intended to be stable paper-numbered names, so starting
production would freeze the error into downstream code.  This also makes the
v3 Section 5 API actively misleading rather than merely off by one:
`theorem_5_3` denotes v3 Theorem 5.4, whereas the actual v3 Corollary 5.3 is
published as `corollary_5_2` in the snapshot.

**Independent paper evidence.**  The current arXiv v3 PDF and its TeX source
label the results as follows:

| v3 result | v3 TeX evidence | Snapshot paper-facing name |
|---|---|---|
| Theorem 3.4, “Structure of tilings, II” | `structure_tilings.tex`, theorem beginning at source line 502; PDF text line 477 | `theorem_3_2` |
| Corollary 3.5, “Universal period of one-dimensional tiles” | TeX line 534; PDF text line 533 | `corollary_3_3` |
| Corollary 5.3, “Improving a tiling, I” | TeX line 743; PDF text line 804 | `corollary_5_2` |
| Theorem 5.4, “Improving a tiling, II” | TeX line 771; PDF text line 838 | `theorem_5_3` and its two strengthening names |

The intervening numbered remarks explain the automatic-numbering shifts.  The
same v3 source labels Proposition 4.4's defective displayed sum as equation
(29), not equation (23).

**Snapshot evidence.**  The mismatch is systematic:

- `blueprint/11-refereeing-standard.md:43` requires every labelled
  arXiv:2010.03254v3 result exactly once.
- `blueprint/COMPARATOR.md:3,9` says the comparator targets v3, but rows 45--46
  and 54--55 call these results Theorem 3.2, Corollary 3.3, Corollary 5.2, and
  Theorem 5.3.  Its source-errata row 114 also calls v3 equation (29) equation
  (23).
- `blueprint/09-main-results.md:1,10--12` promises stable paper-numbered names,
  while declarations at lines 187, 196, 287, 304, 313, and 323 freeze the old
  numbering.
- `blueprint/03-dilation-structure.md:20--21,226,242` and
  `blueprint/07-periodic-completion.md:3,78,92,605,620,628,651` use the same
  wrong paper labels throughout their coverage and proof plans.
- `blueprint/README.md:30,36,67,72`, the main-result proof-chain references in
  `blueprint/COMPARATOR.md:32--33`, both declaration ledgers, the integrated
  artifact, and the generated `Main.lean` all propagate the drift.

The mathematical types represented by those declarations otherwise match the
corresponding v3 results; this finding is about a false public correspondence
and API contract, not a counterexample to the underlying theorems.

**Required repair.**  Before implementation:

1. Make the v3 paper-facing canonical names `theorem_3_4`, `corollary_3_5`,
   `corollary_5_3`, `theorem_5_4`, `theorem_5_4_exact`, and
   `theorem_5_4_structural`.  Since production has not begun, clean renaming is
   preferable to permanently exporting obsolete paper aliases.  If any old
   compatibility alias is retained, it must be explicitly marked as
   compatibility-only and must not be counted as another occurrence of the
   paper result.
2. Correct every paper label and proof-chain citation in the README, Chapters
   03, 07, and 09, the recursive audit, comparator, and source-errata table;
   correct equation (23) to v3 equation (29).
3. Regenerate both validators, both declaration ledgers, all generated module
   sources, their hashes, and a new common snapshot manifest.
4. Record the disposition in `reviews/resolution-log.md` and obtain the
   required fresh independent approvals of that same corrected snapshot.

**Disposition:** unresolved; absent from the current resolution log.  This is
blocking under the snapshot's scope-and-attribution rubric and public-API
freeze.

## P0, P2, and P3 findings

- **P0:** none.
- **P2:** none beyond the systemic P1 above.
- **P3:** none.

The generated validator sources emit style warnings for long provenance lines
and a short generated header.  I do not classify those as a blueprint finding:
the files are generated, validator-only artifacts, and production source must
receive the ordinary Mathlib lint pass after real proofs replace stubs.

## Required command evidence

I ran every command required by `blueprint/11-refereeing-standard.md`, from the
workspace and pinned checkout named there.

| Check | Result |
|---|---|
| `sha256sum -c blueprint/SNAPSHOT.sha256` | success; all 62 entries `OK` |
| `python3 blueprint/validation/generate_integrated.py --check` | success; generated integrated artifact and coverage ledger current |
| pinned direct `lake env lean blueprint/validation/BlueprintIntegrated.lean` | success |
| pinned explicit strict `lake env lean -DrelaxedAutoImplicit=false -DmaxSynthPendingDepth=3 -DmaxErrors=1000 .../BlueprintIntegrated.lean` | success, no diagnostics |
| `python3 blueprint/validation/modules/generate_modules.py --check` | success: `29 modules; 857 declarations; DAG acyclic` |
| `sha256sum -c blueprint/validation/modules/generated-hashes.sha256` | success for all generated sources, ledgers, and package files |
| `python3 blueprint/validation/modules/generate_modules.py --build` | success: offline `Build completed successfully (3446 jobs)`; all 29 module `.olean` files exist |
| nested-package `lake query TranslationalTilings` | success; target is registered and resolves through the umbrella |

Lean reports version 4.33.0.  The pinned Mathlib checkout resolves to the exact
commit recorded by the comparator.  Cache downloads were disabled by the
module generator, and the nested manifest points at the already-pinned local
Mathlib dependency tree.

## Independent declaration, namespace, and ownership audit

I parsed the two TSV ledgers independently of the generators and checked their
rows against the cited Markdown source lines and generated provenance comments.

| Property | Independent result |
|---|---:|
| coverage rows | 857 |
| module-ledger rows | 857 |
| common first seven columns | exactly equal, row for row |
| public declarations | 846 |
| private declarations | 1 |
| anonymous instances/examples | 10 |
| definitions/structures/abbreviations | 353 |
| checked theorem/example/instance bodies | 46 |
| exact-type validator axiom stubs | 458 |
| distinct public qualified names | 846 |
| duplicate public names | 0 |
| distinct source coordinates | 857 |
| ownership modules | 29, all nonempty |
| umbrella rows in module-source ledger | 1, with zero declarations as intended |

The sole private declaration is
`TranslationalTilings.Stepanov.waringVariable` at
`blueprint/05a-weil-stepanov.md:338`.  Its identifier occurs only in its owner
module, `NumberTheory/Stepanov/NewtonWaring.lean`; there is no downstream
private-name leak.  The ten anonymous rows are seven instances and three
regression examples.  Every public name is unique, every declaration has one
source coordinate and one owner, every generated owner file exists, and its
provenance-comment count equals its ledger declaration count.  I found no
unassigned, duplicate, or missing declaration.

The generated tree contains exactly 458 declarations beginning with `axiom`,
matching exactly the 458 `exact-type-axiom-stub` ledger rows.  It contains no
`sorry`, `admit`, or theorem-shaped `opaque`.  These axioms validate types,
names, options, and imports only.  They give no evidence that any of the 458
proofs exists, and my mathematical/proof-feasibility assessment did not rely
on them.

## Module architecture and package integration

The module split is coherent and the prior FLSR2 failure is repaired.
Independent comparison of `module-map.json` with every generated module found
exact equality of direct project imports.  DFS from
`TranslationalTilings.Main` reaches all 29 modules, finds no missing target and
no cycle.  The number-theory chain is below analysis, tiling applications are
above it, and the counterexample remains independent of the structure and
completion chain.  In particular, the previously hidden edge

```text
TranslationalTilings.Dilation.Periodic
  -> TranslationalTilings.LatticeGeometry
```

is present.  No planned production module imports either validator tree.

`validation/modules/future-lakefile.toml` is exactly the current package
configuration plus:

- `TranslationalTilings` in `defaultTargets`; and
- a second `[[lean_lib]]` named `TranslationalTilings`.

It preserves `Tiling`, the v4.33.0 Mathlib requirement, and all current options.
The nested package repeats `relaxedAutoImplicit = false` and
`maxSynthPendingDepth = 3`; each generated source also sets the strict options.
This, the explicit command-line strict check, and the registered target query
close FLSR1 and FLSR2 at the signature/module level.

The actual dirty `Tiling` sources remain independent.  They contain a
pre-existing unrelated `sorry` at `Tiling/Geometry/Plate.lean:125`.  It is not
reachable from the planned new library and is not a defect in this blueprint,
so it is not an additional finding.  It does mean that a later claim that the
*entire dirty checkout*, rather than the new `TranslationalTilings` library, is
globally sorry-free must first resolve that owner code.

## Mathlib reuse, local conflicts, and the Prototile decision

I searched both the pinned Mathlib source and the local project for the
proposed core names and mathematical roles.  The blueprint correctly plans to
reuse, among other things:

- Mathlib `fwdDiff` and its iteration/Gregory--Newton lemmas, exposing only the
  paper's backward-difference adapter;
- root `primorial`, `Nat.Prime.dvd_primorial_iff`, and
  `primorial_lt_four_pow`/`primorial_le_four_pow`;
- `AddSubgroup.index`, `FiniteIndex`, and
  `AddSubgroup.index_range_nsmul`;
- `Polynomial.map_mul`, `Polynomial.roots_mul`, `Polynomial.Splits`, Hasse
  derivatives, finite-field characters, Gauss sums, and AddCircle/Fourier APIs.

Searches found no Mathlib or local declaration which directly replaces the
paper-specific finite tile convolution, grouped quantitative decomposition,
circle-polynomial rigidity, Greenfeld--Tao counterexample, periodic-completion
certificate, or chameleon classifier.  The new public qualified names do not
conflict with the current local source.

The decision not to reuse `Tiling.Prototile` is correct.  The existing
`Tiling.Basic` structure is a nonempty measurable support in a normed additive
group; its `IsPacking` is pairwise almost-everywhere disjointness and its
`IsCover` is almost-everywhere coverage.  This paper needs exact pointwise
integer representation counts for a finite subset of `Z^d`, including higher
tiling levels.  An adapter would import measure theory and still provide no
shared theorem.  The separate namespace and library are therefore a sound
boundary, not avoidable duplication.

## Mathematical and proof-feasibility audit

Apart from FLSR3-1's labels, the blueprint matches the corresponding v3
mathematics and makes the proof obligations unusually explicit.  I checked the
main statements, intermediate results, source errata, quantitative dependence,
and downstream consumers.  In particular:

- Lemma 3.1(ii) correctly uses coprimality, repairing the source proof's
  mistaken `r = 1 mod q` phrase; part (iii) has the required positive/congruence
  hypotheses and an explicit Følner route.
- The grouped structure theorem remains dimension-generic and its primitive
  grouping/common-multiple API is not accidentally planar.
- The one-dimensional universal period is the product `q*n`, not an lcm.
- Proposition 4.4 uses indexed `b_j`, both supremum branches, the exceptional
  summand transfer, and the advertised lattice membership.
- The recursive polynomial-exponential-sum development supplies rather than
  assumes the fixed-character Weil input and Chen prime-power/CRT chain.  The
  public complete-sum theorem has the exponent needed by Lemmas 4.2--4.3.
- FMSR1 is repaired: `monicWeight_mul` now assumes `[Field k]`, and its plan
  maps both monic factors to an algebraic closure, uses splitting,
  `Polynomial.map_mul` and `Polynomial.roots_mul`, and descends by injectivity.
  Downstream uses already live over fields.
- FM1 is repaired: `PaperCompletionResult` is singleton-safe; the exact
  `CompletionCertificate` constructor requires `1 < F.card`; the structural
  consumer derives that condition; and the checked
  `completion_singleton_bound_regression` at `k = 4096` prevents reinstating
  the false old bound.
- Theorem 1.5 has empty/singleton/one-part/multipart routes and an exact
  certificate rebasing argument.  Its explicit exponent implies the stated
  paper asymptotic.
- Both claimed algorithms are represented by finite data and Boolean
  computation, with coverage, soundness/completeness, termination, and a stated
  unit-cost arithmetic model.  The general-lattice input uses a checked HNF
  wire format and does not pretend that classical normalization is executable.

The remaining proof burden is large, especially the Stepanov/Artin--Schreier
and complete exponential sum modules, but it is decomposed into named,
well-typed obligations with a plausible dependency order.  I found no hard
mathematical step silently moved into certificate input, no vacuous predicate,
and no missing recursive prerequisite beyond implementing the displayed
bodyless theorems.

## Final decision

The signature, ownership, module, option, integration, computability, reuse,
and prior-blocker repairs are suitable for implementation.  The exact
paper-facing contract is not.  Because this project deliberately freezes the
public theorem numbers before proof work, the systemic v3 numbering mismatch
must be corrected and the generated common snapshot independently re-reviewed.

**Final verdict: BLOCK.**
