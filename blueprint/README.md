# Blueprint: The Structure of Translational Tilings in `Z^d`

This blueprint covers Rachel Greenfeld and Terence Tao, *The Structure of
Translational Tilings in `Z^d`*, arXiv:2010.03254v3.  The formalization target
is every labelled lemma, proposition, theorem, and corollary in the paper,
together with the auxiliary results needed to prove them without `sorry`,
`admit`, new axioms, or opaque certificates.

The paper uses `Z^d`; Lean uses

```lean
abbrev Lattice (d : ℕ) := Fin d → ℤ
abbrev Plane := Lattice 2
```

Finite tiles are `Finset (Lattice d)` and possibly infinite tiling sets are
`Set (Lattice d)`.  The basic convolution is a finite sum over the tile, so no
summability hypothesis is hidden in the definitions.

## Files and dependency order

The exact 29-file production manifest, all direct project imports, the
umbrella, and the Lake target are frozen in `MODULE_LAYOUT.md` and implemented
under `/home/codex/Documents/Codex/2026-08-14/Tiling/TranslationalTilings`.
This table is only the chapter-level view.

| Blueprint | Lean module | Paper content | Depends on |
|---|---|---|---|
| `01-foundations.md` | `TranslationalTilings.Basic`, `.FiniteDifference` | Sections 1.1-1.2 and notation | Mathlib |
| `02-lattice-geometry.md` | `.LatticeGeometry`, `.Arithmetic` | Cramer rule, commensurability, primitive vectors, bounds | `Basic` |
| `03-dilation-structure.md` | `.Dilation.Periodic`, `.Structure.Grouped` | Lemma 3.1; Theorems 1.7 and 3.4; Corollary 3.5 | `FiniteDifference`, `LatticeGeometry` |
| `04-counterexample.md` | `.Counterexample` | Lemma 2.1 and Theorem 1.3(ii) | `FiniteDifference`, `LatticeGeometry` |
| `05a-weil-stepanov.md` | `.NumberTheory.PolynomialWeilBound` | Fixed-character prime-field polynomial sum bound | Mathlib finite fields, polynomials, derivatives |
| `05b-chen-complete-sums.md` | `.NumberTheory.CompleteExponentialSum` and its four lower number-theory modules | A--C--K/Chen prime powers, CRT, low degrees, global `1-1/d` estimate | `PolynomialWeilBound`, Mathlib characters/Gauss sums/content |
| `05-polynomial-rigidity.md` | `.Analysis.PolynomialRigidity` and its three lower analysis modules | Lemmas 4.2 and 4.3; equidistribution, Fejer separation, rigidity | `CompleteExponentialSum`, `FiniteDifference`, Mathlib Fourier/AddCircle |
| `06-weak-periodicity.md` | `.WeakPeriodicity` | Proposition 4.1, Proposition 4.4, Theorems 1.3(i), 1.4 | `Structure`, `PolynomialRigidity` |
| `07-periodic-completion.md` | `.Slicing`, `.PeriodicCompletion` | Lemma 5.1, Corollary 5.3, singleton-safe Theorem 5.4, non-singleton exact completion certificates, Theorem 1.5 | `Dilation`, `WeakPeriodicity` |
| `08-algorithms.md` | `.Algorithms` | Corollary 1.6 and Theorem 6.2 | all preceding constructive modules |
| `09-main-results.md` | `.Main` | stable paper-facing API | all preceding modules |
| `COMPARATOR.md` | generated documentation target | paper/blueprint/Lean result and definition comparison | all blueprint files |
| `10-recursive-dependency-audit.md` | — | prerequisite, reuse, and trust audit | all blueprint files |
| `11-refereeing-standard.md` | — | independent-review protocol and acceptance gate | all blueprint files |

The Lean import graph must follow this table.  In particular, the
counterexample is independent of the structure theorem; the analytic-number-
theory layer is independent of tilings; and computability is downstream of
the structural mathematics.

## Scope decisions

1. The machine-facing quantitative theorems use explicit natural-number bound
   functions.  Separate corollaries recover the paper's `O_|F|` statements.
   This removes ambiguity from hidden constants and is required for Section 6.
2. The norm used for executable bounds is the integer `l1` norm.  Mathlib norm
   equivalence proves paper-facing Euclidean-diameter corollaries.  Since the
   paper hides constants depending on `|F|` (and dimension is fixed in the
   quantitative plane results), this is statement-equivalent at the published
   level of precision.
3. An interval in `R/Z` is represented invariantly by a metric open ball in
   `AddCircle 1`.  Every positive-length interval contains such a ball, and
   every such ball lifts to a positive-length interval.  The comparator records
   this harmless coordinate-free reformulation.
4. Four source errata are recorded separately from formalization repairs:
   - Dilation Lemma (ii) factors an integer *coprime to* the product of the
     small primes, not merely one congruent to `1` modulo that product.
   - Equation (29) in the proof of Proposition 4.4 uses
     `P_{x,j}(s + b_j t)` inside the sum, rather than a fixed `b_i`.
   - One line following Theorem 3.4 says `Z^2` although the theorem and the
     surrounding argument are in `Z^d`.
   - Section 6 contains two harmless unmatched-bracket/name slips in affine
     line notation; the formal API uses quotient fibers and cannot reproduce
     the ambiguity.
5. The paper-facing Theorem 5.4 result is valid for every nonempty tile and
   includes both its periodic-completion and component-convolution clauses.
   The stronger `CompletionCertificate`, which stores the exact
   `N,N_j,C_j,s_j,L_j,M` construction and its local bounds, requires
   `1<F.card`: the proof uses the positive slice exponent
   `F.card*(F.card-1)/2`.  Singleton tiles use the direct multiplier-one
   translate of the periodic target instead.

## Completion standard

The blueprint is accepted only after independent reviews for:

- faithfulness of every mathematical statement and proof dependency;
- suitability of the definitions and public API for Lean/mathlib;
- completeness of recursive prerequisites, especially compactness,
  polynomial equidistribution, complete exponential sums, and executable
  finite search;
- correctness of quantitative dependencies and computability claims.

Reviews follow the clean-room, adversarial protocol in
`11-refereeing-standard.md`.  All findings and their resolutions are recorded
in `reviews/resolution-log.md`; at least two independent referees must then
approve the corrected, identified blueprint snapshot before any `.lean`
declaration is implemented.

## Signature and module-boundary validators

The acceptance validator is generated from every chapter in dependency order;
its source, strict generated Lean file, and declaration-coverage ledger live in
`validation/`.  Run:

```bash
python3 blueprint/validation/generate_integrated.py --check
cd /home/codex/Documents/Codex/2026-08-14/Tiling
lake env lean \
  /home/codex/Documents/Codex/2026-08-24/usi/blueprint/validation/BlueprintIntegrated.lean
```

The generated module copies all proof-relevant data and definition bodies.
Bodyless theorem declarations become exact-type, validator-only `axiom` stubs
so later signatures can be checked without pretending that a proof exists.
This module is not project source and may never be imported by the Lean
formalization.  See `validation/README.md` for the strict and diagnostic modes.

The integrated artifact intentionally checks one combined declaration
environment.  The independent module-aware validator under
`validation/modules/` additionally assigns every declaration-ledger row to
its unique production source, checks the 29-module acyclic import graph, and
builds the generated `TranslationalTilings` umbrella through an offline Lake
package with the exact pinned options.  Run:

```bash
python3 blueprint/validation/modules/generate_modules.py --check
python3 blueprint/validation/modules/generate_modules.py --build
```

Its theorem axioms are validator-only as well.  Neither validation tree is
part of the production trust boundary.

## Production implementation

The production library implements all 869 ownership-ledger declarations in
29 modules plus `TranslationalTilings.lean`.  It is registered as the
`TranslationalTilings` Lake library and contains no `sorry`, `admit`, new
axiom, validator import, unsafe escape hatch, or proof-resource override.
The validator-only axiom stubs are not imported by production.

From the existing project root, the principal production gates are:

```bash
cd /home/codex/Documents/Codex/2026-08-14/Tiling
lake build TranslationalTilings
lake env lean -DwarningAsError=true TranslationalTilings/Main.lean
lake env lean -DwarningAsError=true TranslationalTilings.lean
```

The final combined snapshot manifest also names the production `lakefile`,
toolchain lock, package manifest, umbrella, and every source module.  The
pre-existing `Tiling` library remains a separate target; in particular, its
older `Tiling/Geometry/Plate.lean` placeholder is outside this formalization's
source and trust boundary.
