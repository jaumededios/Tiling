# Translational tilings, formalized in Lean 4

[![Build and verify](https://github.com/jaumededios/Tiling/actions/workflows/lean_action_ci.yml/badge.svg?branch=main)](https://github.com/jaumededios/Tiling/actions/workflows/lean_action_ci.yml)

A Lean 4 / Mathlib formalization of periodicity, structure, and decidability
results for translational tilings. The development connects finite tiles in
$\mathbb{Z}^2$ with polygonal tiles in $\mathbb{R}^2$, including rational
polygons, axis-parallel polygons with arbitrary real coordinates, and polygons
whose boundary edges have rational slopes.

A set of translation centres $T$ tiles the plane by a tile $\Omega$ when the
translates $t+\Omega$, for $t\in T$, cover the plane and distinct translates
overlap only on sets of area zero. Only translations are allowed. Tiles may
have holes or disconnected components.

The most direct way to read the claims is through the
[comparator statements](#reading-the-statements): each challenge defines its
mathematical objects using Mathlib alone. The accompanying pages place the
paper statements beside the Lean declarations.

## What is proved

A set is **periodic** if it has two linearly independent periods. It is
**weakly periodic** if it is a finite disjoint union of sets each having a
nonzero period. It is **quasiperiodic** if those pieces each have two independent
periods; different pieces may have different period lattices. A set of centres
has **finite local complexity** when its difference set contains only finitely
many points in each bounded region.

**Rational polygons.** If a polygon with rational vertices tiles the plane,
it admits a periodic tiling. Every tiling by such a polygon is weakly periodic,
and tileability is decidable from finite rational input. These are the main
results of de Dios Pont, Grebík, Greenfeld, and Madrid,
[*Periodicity and decidability of translational tilings by rational polygonal
sets*](https://arxiv.org/abs/2408.02151). The public library statements are in
[Tiling/RationalPolygonal/Main.lean](Tiling/RationalPolygonal/Main.lean).

**Axis-parallel polygons.** For a polygon with horizontal and vertical edges,
a tiling of finite local complexity is weakly periodic and has a periodic
replacement. The development also proves the existence and structure of
minimal tilings, earthquake decompositions, periodicity of slabs, and
non-finite-local-complexity limit theorems. Several results apply to periodic
cylinders $X\times\mathbb{R}$ as well as to the whole plane. The
[geometry comparator](comparator/axis-parallel/README.md) states all thirteen
results with their precise hypotheses.

**Deciding tileability from coordinate comparisons.** One algorithm decides
whether the interior of a finite union of closed axis-parallel rectangles tiles
the plane, given an oracle for the signs of integer combinations of its corner
coordinates. The algorithm is uniform in both the rectangles and the oracle.
It asks finitely many questions on each valid input; there is no asserted
uniform bound on their number. For rational coordinates, the oracle can be
computed, giving a computable tileability predicate. Empty, degenerate, and
reversed rectangles are covered by the statement. See the
[computability comparator](comparator/axis-parallel-computability/README.md).

**Rational slopes.** The corresponding structure theory allows arbitrary real
vertex coordinates as long as boundary edges have rational directions. It
includes weak periodicity of minimal tilings, periodic replacements for tilings
of finite local complexity, and the existence of a quasiperiodic tiling whenever
the tile tiles the plane. The [rational-slopes comparator](comparator/rational-slopes/README.md)
distinguishes conclusions about the original centres from the existence of a
replacement tiling, and states the carrier and minimality assumptions explicitly.

**Discrete tilings.** The supporting development formalizes the main structure
and periodic-completion results of Greenfeld and Tao,
[*The structure of translational tilings in $\mathbb{Z}^d$*](https://arxiv.org/abs/2010.03254).
It includes weak periodicity in the plane, quantitative bounds, decision
procedures, and an eight-element tile with a level-four tiling that is not
weakly periodic. The paper-facing entry point is
[TranslationalTilings/Main.lean](TranslationalTilings/Main.lean).

The axis-parallel and rational-slopes developments follow supplied manuscripts.
Their comparator pages identify the source theorems and explain changes of
formulation. In particular, tiling is measured almost everywhere, while periods
and partitions of centres are exact. The computational input is a finite
rectangle family. The geometric axis-parallel challenge uses the paper's finite
boundary-segment description; its passage to rectangles is proved in
[BoundaryBridge.lean](Tiling/AxisParallel/SetFormulation/BoundaryBridge.lean).

## Reading the statements

| Subject | Mathematical exposition | Independent Lean challenge |
| --- | --- | --- |
| Rational polygons | [README](comparator/rational-polygonal/README.md) | [Challenge](comparator/rational-polygonal/Challenge.lean) |
| Axis-parallel geometry | [README](comparator/axis-parallel/README.md) | [Challenge](comparator/axis-parallel/AxisParallelComparator/Challenge.lean) |
| Axis-parallel computability | [README](comparator/axis-parallel-computability/README.md) | [Challenge](comparator/axis-parallel-computability/AxisParallelComputabilityComparator/Challenge.lean) |
| Rational slopes | [README](comparator/rational-slopes/README.md) | [Challenge](comparator/rational-slopes/RationalSlopesComparator/Challenge.lean) |

Challenges deliberately leave their theorem proofs as `sorry`. Each solution
is compiled independently and proves the same statements from the library;
it never imports its challenge. These specification placeholders are the only
intended proof holes. The proof dependencies are checked against the allow-list
`propext`, `Classical.choice`, and `Quot.sound`.

[Comparator](https://github.com/leanprover/comparator) checks the independently
elaborated statements and the definitions they depend on, then replays the
solution through Lean's kernel. This checks correspondence with the written
Lean challenge; assessing correspondence with the informal mathematics still
requires reading the definitions and source statements.

## Build and verify

The project pins **Lean 4.33.0** and **Mathlib v4.33.0**. Install
[elan](https://github.com/leanprover/elan), then run:

```sh
lake exe cache get
lake build
lake build Verification
```

`lake build` builds the mathematical libraries. `Verification` imports the
solutions and the paper-facing results, and fails if an audited theorem uses
an axiom outside the allow-list. It does not import the challenge placeholders.

To compile the independent challenges and the individual axiom reports:

```sh
lake build Challenge AxisParallelComparator AxisParallelComputabilityComparator RationalSlopesComparator
lake env lean comparator/rational-polygonal/PrintAxioms.lean
```

With a toolchain-compatible Comparator installation, run its executable through
`lake env` against each `comparator/*/config.json`. See the
[upstream setup instructions](https://github.com/leanprover/comparator#readme)
for the exporter and sandbox requirements. The release checks use independent
Lean kernel replay; local development runs without the OS sandbox are recorded
as such in [formalization.yaml](formalization.yaml).

The rendered pages can be checked without rebuilding Lean:

```sh
python3 comparator/axis-parallel/render_readme.py --check
python3 comparator/axis-parallel-computability/render_readme.py --check
python3 comparator/rational-slopes/render_readme.py --check
```

## Library layout

- [Tiling/](Tiling/) contains measurable tilings, planar geometry, topology of
  tiling spaces, and the rational-polygonal, axis-parallel, and rational-slopes
  theories. [Tiling.lean](Tiling.lean) is its umbrella import.
- [TranslationalTilings/](TranslationalTilings/) contains the discrete theory on
  integer lattices, including finite convolution, arithmetic, periodic
  completion, and algorithms. It is used by the continuous theory through
  rational approximation and rasterization.
- [comparator/](comparator/) contains the independent statements, their
  solutions, and the readable theorem pages.
- [Verification.lean](Verification.lean) checks the public theorem dependencies.

## Formalization and license

The formalization was developed with OpenAI Codex agents under Jaume de Dios
Pont's direction. The mathematical statements and presentation were iteratively
reviewed separately from the proofs. [formalization.yaml](formalization.yaml)
records the sources, scope, known automation details, and verification limits;
unknown costs and development times are not estimated.

The code is distributed under [Apache-2.0](LICENSE). The cited papers and
Mathlib retain their own licenses.
