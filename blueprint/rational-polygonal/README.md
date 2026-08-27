# Rational polygonal translational tilings

This directory is the paper-to-Lean blueprint for Jaume de Dios Pont, Jan Grebík, Rachel
Greenfeld, and José Madrid, *Periodicity and decidability of translational tilings by rational
polygonal sets* (arXiv:2408.02151v2).

The intended end product has the same acceptance standard as the Greenfeld--Tao development in
this repository:

- every numbered definition, lemma, theorem, and corollary in the paper has an explicit comparator
  row;
- every comparator row is owned by one production module and one generated signature validator;
- all production proofs elaborate without `sorry`, project axioms, validator imports, or resource
  overrides;
- the paper-facing endpoint theorems are thin compositions of reusable intermediate APIs;
- production declarations are checked for exact type agreement, trust closure, documentation, and
  import direction; and
- the frozen final snapshot receives independent mathematical and Lean-library reviews.

The existing `Tiling.Geometry` development already proves the geometric core of Lemmas 2.5 and
2.7 in a stronger finite-family form.  The new development completes the monotile/integer wrappers,
the raster encoding, the executable compiler from rational coordinates, the discrete earthquake
argument, and the three headline results.

The paper works with bounded open polygonal sets.  `Tiling.Geometry` uses their regular-closed
representatives (finite unions of closed nondegenerate triangles), because the repository's tiling
relation is measure-theoretic.  For polygonal sets the open set and its regular-closed representative
agree almost everywhere.  The bridge is part of the public API and is never treated as definitional
equality.

## Files

- [`COMPARATOR.md`](COMPARATOR.md) records the exact paper correspondence and all representation
  choices.
- [`MODULE_LAYOUT.md`](MODULE_LAYOUT.md) freezes dependency direction and declaration ownership.
- [`01-model-and-normalization.md`](01-model-and-normalization.md) specifies the continuous and
  lattice interfaces.
- [`02-integer-reduction.md`](02-integer-reduction.md) specializes the connected-sliding
  development to Lemmas 2.2--2.7.
- [`03-raster.md`](03-raster.md) specifies the finite signature family, rigid marker, and all three
  parts of Lemma 3.1.
- [`04-earthquakes.md`](04-earthquakes.md) specifies the canonical earthquake graph and the proof of
  Lemma 4.2.
- [`05-main-results.md`](05-main-results.md) assembles Theorems 1.1 and 1.2 and Corollary 1.1.
- [`declaration-coverage.tsv`](declaration-coverage.tsv) is the generated 26-module public API
  ledger.  [`validate.py`](validate.py) regenerates it together with the exact signature dump,
  public-definition body dump, `#check` validator, and artifact hashes; `validate.py --check` also
  runs a fresh production build, strict source compilation, documentation lint, and trust gates.

Theorem 1.1 and Theorem 1.2 are proved at the semantic paper level.  Corollary 1.1 is a total
Boolean on `Raw.Code.Input`, whose runtime payload is a finite list of rational triangles.  The
verified pipeline computes common-denominator normalization, all positive-measure signature
types, an executable rigid marker raster, and the final bounded lattice decision.  The older
`RasterPresentation` API remains available as a reusable compiled-backend contract, but it is no
longer the paper-facing input boundary.

## Primary sources

- arXiv abstract and version record: <https://arxiv.org/abs/2408.02151>
- audited source version: `2408.02151v2`
- imported discrete structure/completion/decision results: the proved
  `TranslationalTilings.Main` API in this repository
