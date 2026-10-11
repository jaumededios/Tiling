# Deciding tileability of axis-parallel polygons

The geometric input is a finite family of rectangles. The decision algorithm
accesses their coordinates through sign comparisons. Rational coordinates give
an ordinary computable decision problem.

<details>
<summary>Lean setup</summary>

```lean4
import Mathlib

set_option autoImplicit false

open Bornology MeasureTheory Set Submodule TopologicalSpace
open scoped Pointwise Topology

namespace AxisParallelComputabilityComparator
```

</details>

The Euclidean plane with its usual area measure. We use ℂ as a model of ℝ².

```lean4
abbrev Plane := ℂ
```

## Packing, covering, and tiling

Distinct translates overlap only on a set of area zero.

> **§2, “Packing”, p. 5.**
>
> Let $`\Omega\subseteq \mathbb{R}^d`$ be measurable, and $`S\subseteq \mathbb{R}^d`$. We say that
> $`\Omega+S`$ is a **packing** if the measure $`m_d((\Omega+s)\cap (\Omega+s'))`$ is zero for every
> $`s\neq s'\in S`$. We abbreviate the fact that $`\Omega+S`$ is a packing by using the direct sum
> notation $`\Omega\oplus S`$.

```lean4
def Packing (Ω T : Set Plane) : Prop :=
  T.Pairwise fun s t ↦ volume ((s +ᵥ Ω) ∩ (t +ᵥ Ω)) = 0
```

**Covering notation.** The union of the translates equals E almost everywhere.

```lean4
def CoversExactly (E Ω T : Set Plane) : Prop := E =ᵐ[volume] T +ᵥ Ω
```

A countable packing whose translates cover exactly E almost everywhere.

> **§2, “Tilings”, p. 5.**
>
> We say that **$`T`$ is a tiling of $`X\subseteq \mathbb{R}^d`$ by $`\Omega`$** if
> $`X=\Omega\oplus T`$ up to a null set.
>
> We denote as $`\mathrm{Tile}(\Omega;X)`$ the set of all tilings of $`X`$ by $`\Omega`$.

`Packing` and
`CoversExactly` together say that almost every point of E is covered exactly once
and that almost no point outside E is covered.

```lean4
def TilingOn (E Ω T : Set Plane) : Prop :=
  T.Countable ∧ Packing Ω T ∧ CoversExactly E Ω T
```

The whole-plane case.

> **Introduction, p. 1.**
>
> We say that a bounded measurable set $`\Omega\subset \mathbb{R}^d`$ **tiles $`\mathbb{R}^d`$ by
> translations** if there exists a countable set $`T\subset \mathbb{R}^d`$ such that the family
>
> ```math
> \Omega+t,\quad t\in T
> ```
>
> covers almost every point in $`\mathbb{R}^d`$ exactly once. We then say that **$`T`$ is a tiling
> of $`\mathbb{R}^d`$ by $`\Omega`$** and write $`\Omega\oplus T=\mathbb{R}^d`$. We denote by
> $`\mathrm{Tile}(\Omega;X)`$ the set of all tilings of $`X`$ by $`\Omega`$, and we say that
> $`\Omega`$ is a **(translational) tile** if
> $`\mathrm{Tile}(\Omega;\mathbb{R}^d)\not=\emptyset`$.

```lean4
def Tiling (Ω T : Set Plane) : Prop := TilingOn univ Ω T
```

The horizontal and vertical coordinate projections.

```lean4
abbrev p₁ (z : Plane) : ℝ := z.re
abbrev p₂ (z : Plane) : ℝ := z.im
```

## Finite unions of rectangles

> **“Tiling with a comparison oracle” — input, p. 72.**
>
> **Input.** An axes-parallel polygonal set $`\Omega`$, specified by its vertex set
> $`V(\Omega)`$ and edge set $`E(\Omega)`$.

**Rectangle formulation.** We describe the region by a finite union of closed
axis-parallel rectangles and take its interior, following the paper's open-set
convention. Each rectangle is given by its lower-left and upper-right corners.
This significantly simplifies the algorithmic input: the region is specified
directly, with no boundary reconstruction condition.

The paper uses vertices and edges. Every bounded regular-open axis-parallel
polygon admits such a rectangle decomposition, using its vertex coordinates
for the rectangle sides. Conversely, a nonempty interior of a finite union of
closed rectangles is an axis-parallel polygonal set.

The rectangle from a to b is the intersection
$`p_1^{-1}([a_1,b_1]) \cap p_2^{-1}([a_2,b_2])`$.

```lean4
def rectangle (a b : Plane) : Set Plane :=
  p₁ ⁻¹' Icc (p₁ a) (p₁ b) ∩ p₂ ⁻¹' Icc (p₂ a) (p₂ b)
```

Opposite corners of a finite family of rectangles; repetitions are allowed.

```lean4
abbrev TileData (n : ℕ) := (Fin n → Plane) × (Fin n → Plane)
```

The open region described by the rectangles.

```lean4
def TileData.region {n : ℕ} (data : TileData n) : Set Plane :=
  interior (⋃ i, rectangle (data.1 i) (data.2 i))

instance {n : ℕ} : CoeTC (TileData n) (Set Plane) := ⟨TileData.region⟩
```

## The uniform comparison-oracle theorem

> **“Tiling with a comparison oracle” — oracle and output, p. 72.**
>
> **Oracle access.** Given $`i\in\lbrace 1,2\rbrace`$ and finite sequences $`v_1,\dots,v_m`$ and
> $`w_1,\dots,w_n`$ of vertices of $`\Omega`$, the comparison oracle determines whether
>
> ```math
> \sum_{j=1}^{m} p_i(v_j) \le \sum_{k=1}^{n} p_i(w_k).
> ```
>
> Repetitions are allowed, and empty sums are interpreted as zero.
>
> **Required output.** Yes if $`\Omega`$ tiles $`\mathbb{R}^2`$ by translations, and No
> otherwise.
>
> The algorithm must halt on every input after finitely many computational steps and
> oracle queries.

The geometric data and the comparison oracle are separate. The algorithm sees
the number of rectangles and answers to comparisons; it does not receive the real
coordinates. Repeated corners and repeated rectangles are allowed.

Integer weights on the two corners of each rectangle.

```lean4
abbrev CornerWeights (n : ℕ) := Fin n × Fin 2 → ℤ
```

A potential test for nonnegativity of an integer combination of coordinates.

```lean4
abbrev OrderComparison (n : ℕ) := CornerWeights n → Bool
```

Separate comparison functions for horizontal and vertical coordinates.

```lean4
structure OrderComparisons (n : ℕ) where
  horizontal : OrderComparison n
  vertical : OrderComparison n
```

The comparison functions give the actual signs of the coordinate sums.

```lean4
def TileData.HasOrderComparisons {n : ℕ} (data : TileData n)
    (comparison : OrderComparisons n) : Prop :=
  (∀ a, comparison.horizontal a = true ↔
    0 ≤ ∑ i, (a (i, 0) • p₁ (data.1 i) + a (i, 1) • p₁ (data.2 i))) ∧
  (∀ a, comparison.vertical a = true ↔
    0 ≤ ∑ i, (a (i, 0) • p₂ (data.1 i) + a (i, 1) • p₂ (data.2 i)))
```

### Deciding from finitely many answers

The procedure receives the rectangle count and a finite initial segment of the
oracle's answers. It returns Yes, No, or `none` for “not yet”. We supply increasingly
long initial segments and stop at the first verdict, using Mathlib's `Nat.rfindOpt`.
Termination is required for correct comparison oracles only.

A computable decision procedure on finite initial segments of oracle answers.

```lean4
structure OracleAlgorithm where
  decide : ℕ × List Bool → Option Bool
  computable_decide : Computable decide
```

Number the two corners of rectangle i by 2i and 2i + 1.

```lean4
def cornerIndex {n : ℕ} (v : Fin n × Fin 2) : ℕ := 2 * v.1.val + v.2.val
```

A numerical query encodes a coordinate direction and a finite list of integer
coefficients, using Mathlib's existing encoding. Missing coefficients are zero;
coefficients beyond the supplied corners are ignored. The direction `false`
selects horizontal comparisons and `true` selects vertical comparisons.

Enumerate the answers to the two kinds of coordinate comparison.

```lean4
def OrderComparisons.oracle {n : ℕ} (comparison : OrderComparisons n) : ℕ → Bool :=
  fun code => match Encodable.decode (α := Bool × List ℤ) code with
    | none => false
    | some (vertical, coefficients) =>
      (if vertical then comparison.vertical else comparison.horizontal)
        (fun v => coefficients.getD (cornerIndex v) 0)
```

The oracle computation terminates with the indicated Boolean answer.

```lean4
def OracleAlgorithm.Returns {n : ℕ} (algorithm : OracleAlgorithm)
    (comparison : OrderComparisons n) (answer : Bool) : Prop :=
  answer ∈ Nat.rfindOpt (fun k =>
    algorithm.decide (n, (List.range k).map comparison.oracle))
```

> **Theorem 12.3, p. 72.**
>
> The problem whether a given axes-parallel polygonal set $`\Omega`$ tiles $`\mathbb{R}^2`$ by
> translations is decidable relative to the comparison oracle described above.

**Rectangle formulation.** There is a single algorithm deciding tileability for
finite unions of axis-parallel rectangles, using only sign comparisons of integer
combinations of their horizontal and vertical corner coordinates. It terminates
for every input; the comparison oracles need not be computable.

The same algorithm works for every rectangle family and every correct comparison
oracle. The equivalence below gives both soundness and termination: the computation
returns exactly the correct verdict. Its only geometric information comes from
the comparison oracle.

The paper specifies polygons by vertices and edges; here the input is a rectangle
decomposition. Rectangle corners may introduce additional coordinates, and the
oracle covers the supplied corners. A decomposition using only vertex coordinates
recovers the paper's comparison access. Empty regions cannot tile; degenerate or
reversed rectangles contribute no area. Taking the interior of the union removes
any lower-dimensional remnants.

```lean4
theorem tiling_computable_relative :
    ∃ algorithm : OracleAlgorithm,
      ∀ n (data : TileData n) (comparison : OrderComparisons n),
        data.HasOrderComparisons comparison → ∀ answer,
          algorithm.Returns comparison answer ↔
            (answer = true ↔ ∃ T, Tiling (data : Set Plane) T) := by
  sorry
```

When the sign comparisons are computable, the oracle theorem gives an ordinary
decision algorithm.

**Rational-coordinate consequence.** Tileability is computable for finite unions
of rectangles with rational corner coordinates. The input lists their opposite corners.

```lean4
theorem rational_tiling_computable :
    ComputablePred (fun R : List ((ℚ × ℚ) × (ℚ × ℚ)) =>
      ∃ T, Tiling (interior (⋃ r ∈ R,
        rectangle ⟨r.1.1, r.1.2⟩ ⟨r.2.1, r.2.2⟩)) T) := by
  sorry

end AxisParallelComputabilityComparator
```
