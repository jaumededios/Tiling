# A Mathlib-only comparator for rational polygonal tilings

This directory packages the periodic-tiling theorem of de Dios Pont, Grebík, Greenfeld, and Madrid
for [`leanprover/comparator`](https://github.com/leanprover/comparator). It is designed so that a
mathematician can audit **what is claimed** without reading or trusting any file under `Tiling/` or
`TranslationalTilings/`.

## What the trusted statement says

`Challenge.lean` imports only `Mathlib` and develops the entire vocabulary from
first principles before displaying the theorem:

1. `Packing Ω T` says distinct translates `t + Ω` overlap only on null sets;
2. `Covering Ω T` says those translates cover almost every point;
3. `Tiling Ω T` combines those conditions with countability of `T`;
4. a planar translation set is periodic when two linearly independent vectors preserve membership;
5. a polygon is a positive-area set expressed as a finite almost-disjoint union of closed
   triangles (zero-area pieces are permitted and mathematically irrelevant);
6. a rational triangle has three rational vertices;
7. a rational polygon is a polygon admitting a triangulation entirely by rational triangles.

The headline proposition is therefore literally:

```lean
∀ (Ω : Set Plane), RationalPolygon Ω →
  (∃ T : Set Plane, Tiling Ω T) →
    ∃ T : Set Plane, Periodic T ∧ Tiling Ω T
```

This is the forward implication of paper Theorem 1.1. The reverse implication is tautological.
The paper uses bounded open polygonal regions whereas the shim uses finite unions of closed
triangles. Finite polygon boundaries have Lebesgue measure zero, and the tiling relation is
explicitly an almost-everywhere relation, so the two representatives have the same tilings.

## Why there are two Lean modules

| file | role | trusted by the comparator? |
|---|---|---|
| `Challenge.lean` | all Mathlib-only definitions, followed by the theorem with a `sorry` proof | yes |
| `Solution.lean` | the same definitions and theorem, followed by the bridge to the full project | no; checked |

The definition block is repeated in `Solution.lean`; Comparator checks that the two independently
elaborated copies are identical. The solution bridge is intentionally explicit. It discards only
degenerate triangular pieces, proves that their union is null, and obtains an almost-everywhere
equal nondegenerate support. It then constructs the production library's common-denominator data
from the displayed rational vertices and converts the direct monotile packing/covering relation to
and from the project's unit-labelled placement relation. Only then does it invoke the production
theorem. None of this implementation-facing machinery appears in the challenge statement.

## Quick local checks

From the repository root:

```bash
lake build Solution
lake env lean comparator/rational-polygonal/PrintAxioms.lean
```

The axiom audit must mention no axioms beyond `propext`, `Classical.choice`, and `Quot.sound`.

## Full comparator check

Install `landrun`, a `lean4export` matching this repository's Lean toolchain, and Comparator itself
as described in the [official Comparator README](https://github.com/leanprover/comparator/blob/master/README.md).
Then, from the repository root, run:

```bash
systemd-run --property=RestrictAddressFamilies=~AF_UNIX --user --pty \
  -E PATH="$PATH" --working-directory "$(pwd)" -- \
  bash -c 'lake env /path/to/comparator comparator/rational-polygonal/config.json'
```

Comparator separately builds and exports `Challenge` and `Solution`, checks that every constant in
the theorem statements agrees, rejects any solution axiom outside the allow-list, and replays the
solution export through the Lean kernel. A successful run ends with `Your solution is okay!`.

For a non-sandboxed development smoke test only, Comparator ships `scripts/fake-landrun.sh`; the
real acceptance run should use `landrun` as in the official instructions.
