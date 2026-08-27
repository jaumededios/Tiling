# A Mathlib-only comparator for rational polygonal tilings

This directory packages the periodic-tiling theorem of de Dios Pont, Grebík, Greenfeld, and Madrid
for [`leanprover/comparator`](https://github.com/leanprover/comparator). It is designed so that a
mathematician can audit **what is claimed** without reading or trusting any file under `Tiling/` or
`TranslationalTilings/`.

## What the trusted statement says

`ChallengeDeps.lean` imports only seven named Mathlib modules. It develops the vocabulary from
first principles:

1. a prototile is a nonempty measurable set;
2. placements form a tiling when they are countable, pairwise almost-everywhere disjoint, and cover
   almost every point;
3. a monotile tiling specializes this definition to one set and a set of translation vectors;
4. a planar translation set is periodic when two linearly independent vectors preserve membership;
5. a polygonal set is a finite almost-disjoint union of nondegenerate closed triangles;
6. its intrinsic vertices are those seen by every triangulation;
7. it is rational when, relative to one intrinsic vertex, a single positive integer clears the
   denominators of all intrinsic vertices.

The headline proposition is therefore literally:

```lean
∀ (Ω : Set Plane), RationalPolygon Ω →
  (∃ T : Set Plane, TranslationTiling volume Ω T) →
    ∃ T : Set Plane, Periodic T ∧ TranslationTiling volume Ω T
```

This is the forward implication of paper Theorem 1.1. The reverse implication is tautological.
The paper uses bounded open polygonal regions whereas the shim uses their regular-closed supports;
finite polygon boundaries have Lebesgue measure zero, and the tiling relation is explicitly an
almost-everywhere relation, so the two representatives have the same tilings.

## Why there are three Lean modules

| file | role | trusted by the comparator? |
|---|---|---|
| `ChallengeDeps.lean` | Mathlib-only definitions and the proposition `PeriodicTilingTheorem` | yes |
| `Challenge.lean` | the theorem statement with a `sorry` proof | yes |
| `Solution.lean` | the exact same theorem, proved via the full project | no; checked |

The solution bridge is intentionally explicit. It converts triangulations in both directions,
proves that both notions of intrinsic vertex coincide, embeds coordinatewise integer points in the
project's integer lattice, and converts the direct monotile packing/covering relation to and from
the project's unit-labelled placement relation. Only then does it invoke the production theorem.

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
