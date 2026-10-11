# Tilings by axis-parallel polygonal sets

Ω is the tile, T its set of translation centres, and E the region being tiled.
The notation t +ᵥ Ω means a translate; T +ᵥ Ω is the union of these translates.
Packing and coverage are understood up to sets of area zero. Periods and
partitions are exact. The basic predicates apply to arbitrary sets; the theorems
use nonempty open tiles, so the paper's measurability conditions hold.

<details>
<summary>Lean setup</summary>

```lean4
import Mathlib

set_option autoImplicit false

open Bornology MeasureTheory Set Submodule TopologicalSpace
open scoped Pointwise Topology

namespace AxisParallelComparator
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

We will consider the interior of the closure in order to fill the missing seams
between adjacent open tiles. This is the regular-open
representative of the region covered by a polygonal packing.

> **Remark 6.5, p. 26.**
>
> In the arguments below, we freely pass between the sets $`\Omega\oplus P`$,
> $`\mathrm{int}(\overline{\Omega}\oplus P)`$, $`\mathrm{int}(\overline{\Omega\oplus P})`$ and $`X_P\times \mathbb{R}`$. In particular, when talking about the boundary of
> $`\Omega\oplus P`$, where $`P\in \mathrm{Plates}(\Omega,T)`$, or $`P=T_c`$, we always mean the
> boundary of $`X_P\times \mathbb{R}`$.

**Lean formulation.** We fix the representative
$`\mathrm{int}(\mathrm{cl}(\Omega\oplus T))`$.
For the paper's column and plate regions, the quoted equalities justify this choice;
subsequent assertions of invariance concern this regular-open representative.

```lean4
def coveredRegion (Ω T : Set Plane) : Set Plane :=
  interior (closure (T +ᵥ Ω))
```

## Periods and finite partitions

Translation by p leaves the set unchanged; p = 0 is allowed.

> **§2, “Periodic sets”, p. 5.**
>
> For a closed set $`Z\subseteq \mathbb{R}^d`$, we set $`\Gamma(Z)`$ to be the group of
> translational symmetries of $`Z\subseteq \mathbb{R}^d`$, that is,
>
> ```math
> \Gamma(Z)=\lbrace g\in \mathbb{R}^d:Z+g=Z\rbrace .
> ```

**Lean formulation.** `IsPeriod A p` is the condition $`p\in\Gamma(A)`$ in the displayed formula.

```lean4
def IsPeriod (A : Set Plane) (p : Plane) : Prop := p +ᵥ A = A
```

A set is *periodic*, or *fully periodic*, if it has two real-linearly-independent periods.

> **Introduction, p. 1.**
>
> A tiling $`T`$ is **fully periodic**, or simply **periodic**, if it is invariant under a
> full-rank lattice.

**Lean formulation.** In the plane, invariance under a full-rank lattice is equivalent to having two
real-linearly independent periods. The Lean definition states this basis criterion.

```lean4
def IsDoublyPeriodic (A : Set Plane) : Prop :=
  ∃ p q, LinearIndependent ℝ ![p, q] ∧ IsPeriod A p ∧ IsPeriod A q
```

A finite partition may have a different period or period lattice on each part.

> **Introduction, p. 1.**
>
> It is **weakly periodic** if it is a finite disjoint union of sets with nonzero periods, and
> **quasi-periodic** if it is a finite disjoint union of periodic sets.

**Lean formulation.** The two Lean definitions correspond, in order, to weak and quasi-periodicity.
`Finpartition` expresses the finite disjoint union; each part has its own periods.

```lean4
def WeaklyPeriodic (A : Set Plane) : Prop :=
  ∃ P : Finpartition A, ∀ S ∈ P.parts, ∃ p, p ≠ 0 ∧ IsPeriod S p

def QuasiPeriodic (A : Set Plane) : Prop :=
  ∃ P : Finpartition A, ∀ S ∈ P.parts, IsDoublyPeriodic S
```

## Tiles and local complexity

**Coordinate notation.** The horizontal and vertical unit vectors.

```lean4
abbrev e₁ : Plane := ⟨1, 0⟩
abbrev e₂ : Plane := ⟨0, 1⟩
```

The coordinate projections.

> **§2, p. 5.**
>
> For $`i\in \lbrace 1,2\rbrace`$, let $`p_i\colon \mathbb{R}^2\to \mathbb{R}`$ be the **orthogonal
> projection**, defined by $`p_i(u)=u_i`$ for every $`u=(u_1,u_2)\in \mathbb{R}^2`$.

```lean4
abbrev p₁ (z : Plane) : ℝ := z.re
abbrev p₂ (z : Plane) : ℝ := z.im
```

A set equal to the interior of its closure.

> **§2, p. 4.**
>
> An open set $`X\subseteq\mathbb{R}^d`$ is called regular open if
> $`\mathrm{int}(\overline{X})=X`$.

```lean4
def IsRegularOpen {X : Type*} [TopologicalSpace X] (U : Set X) : Prop :=
  interior (closure U) = U
```

A nonempty bounded regular-open set whose boundary is a finite union of
horizontal and vertical segments. Holes, disconnected components, and arbitrary
real coordinates are allowed.

> **§2, “Polygonal sets” and “Axes-parallel polygonal sets”, p. 5.**
>
> A **polygonal set** is a bounded regular open set $`\Omega\subseteq \mathbb{R}^2`$, whose
> boundary is a finite union of segments. Note that a polygonal set can certainly be
> disconnected and its connected components are not necessarily simply connected. We denote the
> vertices of $`\Omega`$ by $`V(\Omega)`$, and the edges of $`\Omega`$ by $`E(\Omega)`$.
>
> We say that a polygonal set $`\Omega`$ is **axes-parallel** if every line segment $`\omega`$ in
> $`E(\Omega)`$ lies in a coset of either the $`x`$-axis, or the $`y`$-axis; i.e., there exists
> $`s=s(\omega)\in \mathbb{R}^2`$ such that $`\omega \subseteq (\mathbb{R}\times \lbrace 0\rbrace ) \cup (\lbrace 0\rbrace \times \mathbb{R}) +s`$.

**Lean formulation.** We restrict to nonempty sets and specify each boundary
segment by its endpoints. Equality of the first coordinates makes a segment
vertical; equality of the second coordinates makes it horizontal.

```lean4
def IsAxisParallelTile (Ω : Set Plane) : Prop :=
  Ω.Nonempty ∧ IsBounded Ω ∧ IsRegularOpen Ω ∧
    ∃ edges : Finset (Plane × Plane),
      (∀ e ∈ edges, p₁ e.1 = p₁ e.2 ∨ p₂ e.1 = p₂ e.2) ∧
      frontier Ω = ⋃ e ∈ edges, segment ℝ e.1 e.2
```

> **Definition 1.1, p. 2.**
>
> A discrete set $`A\subseteq \mathbb{R}^d`$ has **finite local complexity** if for every $`R>0`$
> the collection
>
> ```math
> \lbrace ((\mathcal{B}_R+a)\cap A)-a:a\in A\rbrace ,
> ```
>
> where $`\mathcal{B}_R`$ is the open ball of radius $`R`$ around the origin, is finite.

**Lean formulation.** This is the equivalent bounded-difference criterion. It implies uniform
discreteness, so a separate discreteness hypothesis is unnecessary. On discrete
sets it is equivalent to the quoted finite-patch definition.

```lean4
def HasFiniteLocalComplexity {V : Type*} [NormedAddCommGroup V] (T : Set V) : Prop :=
  ∀ B, IsBounded B → ((T - T) ∩ B).Finite
```

## Finite local complexity forces periodicity

The region is the cylinder $`E=X\times\mathbb{R}`$. Taking $`X=\mathbb{R}`$ gives
the whole-plane conclusions. The first conclusion concerns the given tiling;
the second gives a doubly periodic replacement tiling of the same region.

> **Theorem 11.1, p. 53.**
>
> Let $`X\not=\emptyset`$ be a regular open periodic subset of $`\mathbb{R}`$, $`\Omega`$ be an
> axes-parallel polygonal set and $`E=X\times \mathbb{R}`$. Then:
>
> (i) Any $`T\in \mathrm{Tile}(\Omega;E)`$ that has finite local complexity is weakly
> periodic.
>
> (ii) If there is $`T\in \mathrm{Tile}(\Omega;E)`$ that has finite local complexity,
> then there is $`S\in \mathrm{Tile}(\Omega;E)`$ that is periodic.

**Lean formulation.** The two Lean statements are clauses (i) and (ii), respectively.
The cylinder $`X\times\mathbb{R}`$ is `p₁ ⁻¹' X`. A positive period β specifies
a one-dimensional period lattice $`\beta\mathbb{Z}`$ of X.

```lean4
theorem flc_tiling_weakly_periodic
    (Ω : Set Plane) (hΩ : IsAxisParallelTile Ω)
    (X : Set ℝ) (hX : X.Nonempty) (hXregular : IsRegularOpen X)
    (β : ℝ) (hβ : 0 < β) (hperiod : β +ᵥ X = X)
    (T : Set Plane) (hT : TilingOn (p₁ ⁻¹' X) Ω T)
    (hFLC : HasFiniteLocalComplexity T) :
    WeaklyPeriodic T := by
  sorry

theorem periodic_tiling_of_flc
    (Ω : Set Plane) (hΩ : IsAxisParallelTile Ω)
    (X : Set ℝ) (hX : X.Nonempty) (hXregular : IsRegularOpen X)
    (β : ℝ) (hβ : 0 < β) (hperiod : β +ᵥ X = X) :
    (∃ T, TilingOn (p₁ ⁻¹' X) Ω T ∧ HasFiniteLocalComplexity T) →
      ∃ S, TilingOn (p₁ ⁻¹' X) Ω S ∧ IsDoublyPeriodic S := by
  sorry
```

## Limits of tilings and minimality

The hull consists of limits of translates of the centre set. For a tiling of E,
only translations preserving E are allowed. We use the Fell topology on closed
sets: configurations meet specified open sets and avoid specified compact sets.

**Topological notation.** Closed sets meeting U.

```lean4
def hit (U : Set Plane) : Set (Closeds Plane) :=
  {F | ((F : Set Plane) ∩ U).Nonempty}
```

Closed sets avoiding K.

```lean4
def miss (K : Set Plane) : Set (Closeds Plane) :=
  {F | Disjoint (F : Set Plane) K}
```

The topology is generated by hit-open and miss-compact conditions.

> **§7.1, p. 31.**
>
> We say that a sequence of uniformly discrete sets $`S_n`$ *converges weakly* to $`S`$, in symbols
> $`S_n\to S`$, if for every $`R>0`$ and $`\epsilon >0`$, there exists $`N`$ such that
>
> ```math
> S_n \cap \mathcal{B}_R \subseteq S+\mathcal{B}_\epsilon \quad \text{ and } \quad S \cap \mathcal{B}_R
> \subseteq S_n+\mathcal{B}_\epsilon
> ```
>
> for every $`n\geq N`$.

**Lean formulation.** This is an alternative description of the topology, not the displayed sequence
definition. On configurations with a common positive separation constant, Fell
convergence is exactly the quoted weak convergence. Tiling centres have such a
constant (§7.1), and the supporting library proves the topology correspondence.

```lean4
abbrev fellTopology : TopologicalSpace (Closeds Plane) :=
  TopologicalSpace.generateFrom
    ((hit '' {U : Set Plane | IsOpen U}) ∪ (miss '' {K : Set Plane | IsCompact K}))
```

**Restricted hull notation.** Limits of translates by vectors in G.
This will also let us restrict the translating vectors to a prescribed lattice.

```lean4
def orbitHullUnder (G T : Set Plane) : Set (Closeds Plane) :=
  closure[fellTopology] {S | ∃ p ∈ G, (S : Set Plane) = p +ᵥ T}
```

The closure of the translation orbit under periods of E.

> **§7.1, equation (7.1), p. 32.**
>
> For $`T\in \mathrm{Tile}(\Omega;E)`$, we define $`\mathcal{O}_{T}(\Omega;E)`$ as the weak
> closure of the orbit of $`T`$ under the action of $`\Gamma(E)`$. As
> $`\mathrm{Tile}(\Omega;E)`$ endowed with weak topology is metrizable by Lemma 7.1, we have
> that
>
> ```math
> \mathcal{O}_{T}(\Omega;E)\coloneqq
> \bigl\lbrace S \subseteq \mathbb{R}^2 :
> \text{There exists}\quad \lbrace g_n\rbrace _{n\in\mathbb{N}}\subseteq\Gamma(E)
> \quad\text{s.t.}\quad T+g_n\to S\bigr\rbrace.
> ```

**Lean formulation.** We take topological closure in the Fell topology instead of quantifying over
sequences. For tiling centres these give the same hull. Using `Closeds Plane`
records that these configurations are closed subsets of the plane.

```lean4
def orbitHull (E T : Set Plane) : Set (Closeds Plane) :=
  orbitHullUnder {p | IsPeriod E p} T
```

Minimality means that every configuration in the hull has the same hull.

> **Definition 9.1, p. 46.**
>
> Let $`X\not=\emptyset`$ be a regular open periodic subset of $`\mathbb{R}`$, $`E=X\times \mathbb{R}`$, $`\Omega`$ be a polygonal set and $`T\in \mathrm{Tile}(\Omega;E)`$. We say that
> $`T`$ is **topologically minimal** if for every $`S\in \mathcal{O}_{T}(\Omega;E)`$ we have
> $`\mathcal{O}_{T}(\Omega;E)=\mathcal{O}_{S}(\Omega;E)`$.

**Lean formulation.** The equality of hulls is exactly the quoted condition,
with its sides reversed.
`IsClosed T` is automatic for the tilings under consideration: their centres are
uniformly discrete (§7.1). It makes this predicate meaningful beyond that setting.

```lean4
def IsMinimal (E T : Set Plane) : Prop :=
  IsClosed T ∧ ∀ S ∈ orbitHull E T, orbitHull E S = orbitHull E T
```

### A minimal tiling exists in every tiling hull

This consequence of compactness and Birkhoff's theorem applies to every periodic
cylinder, including the whole plane.

> **following Definition 9.1, p. 46.**
>
> A classical theorem of Birkhoff asserts that for any tiling $`T`$ of $`E`$ by $`\Omega`$ there
> exists $`S\in \mathcal{O}_{T}(\Omega;E)`$ that is topologically minimal.

**Lean formulation.** This specializes the quoted existence statement to axis-parallel tiles.
The assumptions on X are those in Definition 9.1; the cylinder is `p₁ ⁻¹' X`.

```lean4
theorem exists_minimal_tiling_in_hull
    (Ω : Set Plane) (hΩ : IsAxisParallelTile Ω)
    (X : Set ℝ) (hX : X.Nonempty) (hXregular : IsRegularOpen X)
    (β : ℝ) (hβ : 0 < β) (hperiod : β +ᵥ X = X)
    (T : Set Plane) (hT : TilingOn (p₁ ⁻¹' X) Ω T) :
    ∃ S ∈ orbitHull (p₁ ⁻¹' X) T,
      TilingOn (p₁ ⁻¹' X) Ω S ∧
      IsMinimal (p₁ ⁻¹' X) S := by
  sorry
```

## Columns and earthquake components

A direction is represented by a vector v. The choices e₁ and e₂ are horizontal
and vertical. Allowing either choice expresses “after possibly swapping the axes”.

**Directional invariance notation.** Every real translation along v is a period.

```lean4
def IsInvariantAlong (E : Set Plane) (v : Plane) : Prop :=
  ∀ r : ℝ, IsPeriod E (r • v)
```

**Line notation.** The centres on the line through t parallel to v.

```lean4
def lineFibre (v : Plane) (T : Set Plane) (t : Plane) : Set Plane :=
  T ∩ (t +ᵥ (span ℝ {v} : Set Plane))
```

Components are the smallest nonempty families covering an invariant slab.

> **Lemma 6.2, p. 24.**
>
> Let $`T`$ be a tiling of $`\mathbb{R}^2`$ by $`\Omega`$ and
> $`P\in \mathrm{Plates}(\Omega,T)`$. Then:
>
> (i) There exists a (unique) regular open set $`X_P\subseteq \mathbb{R}`$ such that
> $`\Omega\oplus P=X_P\times \mathbb{R}`$ up to null sets. In fact, we have
> $`\mathrm{int}(\overline{\Omega}\oplus P)= \mathrm{int}(\overline{\Omega\oplus P})=X_P\times \mathbb{R}`$.
>
> (ii) $`P`$ is minimal with respect to property (i); i.e., if $`P'\subseteq P`$ satisfies (i)
> then $`P'\in \lbrace \emptyset ,P\rbrace`$.

**Lean formulation.** This definition uses the lemma's geometric characterization, rather than the
paper's original equivalence classes of proper edge contacts. For a tiling, those
classes partition T into the minimal nonempty invariant slabs, so the two
characterizations agree. For v = e₂, invariance means a region of the form
$`X_P\times\mathbb{R}`$; v = e₁ gives the coordinate-swapped version.

```lean4
def IsEarthquakeComponent (Ω : Set Plane) (v : Plane) (T S : Set Plane) : Prop :=
  S.Nonempty ∧ S ⊆ T ∧ IsInvariantAlong (coveredRegion Ω S) v ∧
    ∀ R, R.Nonempty → R ⊆ S → IsInvariantAlong (coveredRegion Ω R) v → R = S
```

Columns, non-column plates, and the earthquake decomposition.

> **Definition 6.4, pp. 25–26.**
>
> Let $`\Omega\subset\mathbb{R}^2`$ be an axes-parallel polygonal tile, $`T\in \mathrm{Tile}(\Omega;\mathbb{R}^2)`$, and $`P\in \mathrm{Plates}(\Omega,T)`$.
>
> - We say that $`P`$ is a **vertical column of $`(\Omega,T)`$** if there exists $`x\in \mathbb{R}`$
> such that $`P \subseteq \lbrace x\rbrace \times \mathbb{R}`$. (In particular, we have $`\Omega+ P= X\times \mathbb{R}`$, where $`X=p_1(\Omega)+x`$.) We denote by $`T_c`$ the union of vertical columns of
> $`T`$.
>
> - We say that $`P`$ is in $`\mathrm{Plates}_{\mathrm{nc}}(\Omega,T)`$ if
> $`P\subseteq T\setminus T_c`$.
>
> - Finally, the **(vertical) earthquake decomposition of $`T`$**
> (with respect to $`\Omega`$) is the decomposition
>
> ```math
> T=T_{c}\sqcup \left(\bigsqcup_{P\in \mathrm{Plates}_{\mathrm{nc}}(\Omega,T)} P
> \right).
> ```
>
> We say that the earthquake decomposition of $`T`$ is **non-trivial** if $`T\not\in \mathrm{Plates}_{\mathrm{nc}}(\Omega,T)`$.
>
> Note that the decomposition is well-defined due to Lemma 6.2.

**Lean formulation.** The first definition collects complete line fibres;
under the tiling hypotheses
these are exactly the paper's columns. The second selects the non-column components.
The theorem records the displayed disjoint union as coverage and pairwise
disjointness. The quoted vertical version is v = e₂; v = e₁ follows by swapping axes.

```lean4
def columnPart (Ω : Set Plane) (v : Plane) (T : Set Plane) : Set Plane :=
  {t ∈ T | IsInvariantAlong (coveredRegion Ω (lineFibre v T t)) v}

def tectonicPlates (Ω : Set Plane) (v : Plane) (T : Set Plane) : Set (Set Plane) :=
  {S | IsEarthquakeComponent Ω v T S ∧ S ⊆ T \ columnPart Ω v T}

theorem earthquake_decomposition
    (Ω : Set Plane) (hΩ : IsAxisParallelTile Ω)
    (T : Set Plane) (hT : Tiling Ω T)
    (v : Plane) (hv : v ∈ ({e₁, e₂} : Set Plane)) :
    columnPart Ω v T ∪ ⋃₀ tectonicPlates Ω v T = T ∧
      Disjoint (columnPart Ω v T) (⋃₀ tectonicPlates Ω v T) ∧
      (tectonicPlates Ω v T).Pairwise Disjoint := by
  sorry
```

## Structure of a minimal tiling

> **Theorem 9.1, p. 47.**
>
> Let $`T`$ be a topologically minimal tiling of $`\mathbb{R}^2`$ by an axes-parallel
> polygonal set $`\Omega`$. Then, after possibly swapping the vertical and horizontal axes,
> there is $`m\ge 0`$ and a decomposition
>
> ```math
> T=T_c\sqcup T_1\sqcup\dots\sqcup T_m
> ```
>
> such that for every $`1\le j\le m`$, the set $`T_j`$ has finite local complexity and
> $`\Omega\oplus T_j`$ is periodic and $`\mathbb{R}(0,1)`$-invariant.

**Lean formulation.** The finite partition of $`T\setminus T_c`$ replaces the indexed list
$`T_1,\ldots,T_m`$, and the choice of v expresses the possible axis swap.
The Lean conclusion also includes periodicity of the region covered by $`T_c`$.
That is an additional consequence, established in the proof of Theorem 12.1
(p. 70) and used in the proof of Theorem 12.2 (p. 71); it is not an extra clause
of the displayed Theorem 9.1.

```lean4
theorem minimal_tiling_structure
    (Ω : Set Plane) (hΩ : IsAxisParallelTile Ω)
    (T : Set Plane) (hT : Tiling Ω T) (hminimal : IsMinimal univ T) :
    ∃ v ∈ ({e₁, e₂} : Set Plane),
      ∃ P : Finpartition (T \ columnPart Ω v T),
        IsDoublyPeriodic (coveredRegion Ω (columnPart Ω v T)) ∧
        ∀ S ∈ P.parts,
          HasFiniteLocalComplexity S ∧
          IsDoublyPeriodic (coveredRegion Ω S) ∧ IsInvariantAlong (coveredRegion Ω S) v := by
  sorry
```

## Every minimal tiling is weakly periodic

> **Theorem 12.1, p. 70.**
>
> Let $`T`$ be a tiling of $`\mathbb{R}^2`$ by an axes-parallel polygonal set $`\Omega`$ that is
> topologically minimal. Then $`T`$ is weakly periodic.

```lean4
theorem minimal_tiling_weakly_periodic
    (Ω : Set Plane) (hΩ : IsAxisParallelTile Ω)
    (T : Set Plane) (hT : Tiling Ω T) (hminimal : IsMinimal univ T) :
    WeaklyPeriodic T := by
  sorry
```

## A quasi-periodic replacement with a common period

The nonzero period belongs to the whole replacement tiling. Quasi-periodicity
alone does not assert this: the lattices of its pieces may be incommensurable.

> **Theorem 12.2, p. 71.**
>
> Let $`T`$ be a tiling of $`\mathbb{R}^2`$ by an axes-parallel polygonal set $`\Omega`$. Then
> there is a tiling $`S`$ of $`\mathbb{R}^2`$ by $`\Omega`$ that is quasi periodic and
> $`\langle \vec v\rangle`$-periodic for some $`\vec v\in \mathbb{R}^2\setminus \lbrace (0,0)\rbrace`$.

```lean4
theorem quasi_periodic_tiling_with_common_period
    (Ω : Set Plane) (hΩ : IsAxisParallelTile Ω) :
    (∃ T, Tiling Ω T) →
      ∃ S, Tiling Ω S ∧ QuasiPeriodic S ∧ ∃ p, p ≠ 0 ∧ IsPeriod S p := by
  sorry
```

## Further earthquake results

### Finitely many tectonic plates

> **Corollary 8.4, p. 38.**
>
> Let $`T`$ be a tiling of $`\mathbb{R}^2`$ by an axes-parallel polygonal set $`\Omega`$. Then
> the set $`\mathrm{Plates}_{\mathrm{nc}}(\Omega,T)`$ is finite.

**Lean formulation.** The quoted corollary concerns vertical plates (v = e₂).
The Lean statement also
includes horizontal plates (v = e₁), obtained by swapping the coordinates.

```lean4
theorem finitely_many_tectonic_plates
    (Ω : Set Plane) (hΩ : IsAxisParallelTile Ω)
    (T : Set Plane) (hT : Tiling Ω T)
    (v : Plane) (hv : v ∈ ({e₁, e₂} : Set Plane)) :
    (tectonicPlates Ω v T).Finite := by
  sorry
```

### One horizontal period for all vertical slabs

> **Theorem 6.1, p. 26.**
>
> Let $`T`$ be a tiling of $`\mathbb{R}^2`$ by an axes-parallel polygonal set $`\Omega`$ that
> has finite horizontal complexity and
>
> ```math
> T=T_{c}\sqcup
> \left(\bigsqcup_{P\in \mathrm{Plates}_{\mathrm{nc}}(\Omega,T)} P\right)
> ```
>
> be the earthquake decomposition of $`T`$. Then there is $`\beta>0`$ such that the sets
>
> ```math
> \Omega\oplus T_{c} \text{ and } \Omega\oplus P
> ```
>
> are $`(\beta,0)\mathbb{Z}`$-periodic for every
> $`P\in \mathrm{Plates}_{\mathrm{nc}}(\Omega,T)`$.

> **Remark 6.9, p. 26.**
>
> By tracing the proof of Theorem 6.1 we see that the statement
> generalizes to tilings of any periodic set of the form $`E=X\times \mathbb{R}`$ for a
> regular open periodic $`X\subseteq \mathbb{R}`$. In fact, it turns out that when a
> regular open periodic set $`X`$ is a *strict* subset of $`\mathbb{R}`$, *all* tilings in
> $`\mathrm{Tile}(\Omega;E)`$ have finite horizontal complexity; see Remark
> 8.7.

**Lean formulation.** The first Lean statement includes the cylinder extension in Remark 6.9;
the second is the proper-cylinder consequence in that remark. Finite horizontal
complexity is written as `HasFiniteLocalComplexity (p₁ '' T)`; this condition already
implies discreteness. A period β • e₁ gives the stated $`(\beta,0)\mathbb{Z}`$-invariance.
The covered regions are regularized as in Remark 6.5.

```lean4
theorem earthquake_slabs_periodic
    (Ω : Set Plane) (hΩ : IsAxisParallelTile Ω)
    (X : Set ℝ) (hX : X.Nonempty) (hXregular : IsRegularOpen X)
    (β₀ : ℝ) (hβ₀ : 0 < β₀) (hperiod : β₀ +ᵥ X = X)
    (T : Set Plane) (hT : TilingOn (p₁ ⁻¹' X) Ω T)
    (hcomplexity : HasFiniteLocalComplexity (p₁ '' T)) :
    ∃ β : ℝ, 0 < β ∧
      IsPeriod (coveredRegion Ω (columnPart Ω e₂ T)) (β • e₁) ∧
      ∀ P ∈ tectonicPlates Ω e₂ T, IsPeriod (coveredRegion Ω P) (β • e₁) := by
  sorry

theorem proper_cylinder_finite_horizontal_complexity
    (Ω : Set Plane) (hΩ : IsAxisParallelTile Ω)
    (X : Set ℝ) (hX : X.Nonempty) (hXregular : IsRegularOpen X) (hproper : X ≠ univ)
    (β : ℝ) (hβ : 0 < β) (hperiod : β +ᵥ X = X)
    (T : Set Plane) (hT : TilingOn (p₁ ⁻¹' X) Ω T) :
    HasFiniteLocalComplexity (p₁ '' T) := by
  sorry
```

**Split notation.** Two nonempty families which can slide independently along v.
Their regularized covered regions are invariant in that direction. This helper
packages the split in the next theorem.

```lean4
def IsEarthquakeSplit (Ω S S₀ S₁ : Set Plane) (v : Plane) : Prop :=
  S₀.Nonempty ∧ S₁.Nonempty ∧ Disjoint S₀ S₁ ∧ S₀ ∪ S₁ = S ∧
    IsInvariantAlong (coveredRegion Ω S₀) v ∧ IsInvariantAlong (coveredRegion Ω S₁) v
```

### Infinite complexity produces an earthquake in a limit

> **Theorem 7.1, p. 32.**
>
> Let $`T`$ be a tiling of $`E=X\times \mathbb{R}`$ by an axes-parallel polygonal set $`\Omega`$
> that does not have finite local complexity. Then there is
> $`S\in \mathcal{O}_{T}(\Omega;E)`$ and a decomposition $`S=S_0\sqcup S_1`$ such that
> $`S_i\not=\emptyset`$ for $`i\in \lbrace 0,1\rbrace`$ and
>
> - if $`X\not=\mathbb{R}`$, then $`\Omega\oplus S_0`$ and $`\Omega\oplus S_1`$ are
> $`\mathbb{R}(0,1)`$-invariant,
>
> - if $`X=\mathbb{R}`$, then $`\Omega\oplus S_0`$ and $`\Omega\oplus S_1`$ are both either
> $`\mathbb{R}(0,1)`$-invariant, or $`\mathbb{R}(1,0)`$-invariant.
>
> Moreover, if $`\Lambda\subseteq \Gamma(E)`$ is a lattice, then we may choose $`S`$ to be a
> weak limit of a sequence $`\lbrace T+\lambda_n\rbrace _{n\in \mathbb{N}}`$, where
> $`\lambda_n\in \Lambda`$ for every $`n\in \mathbb{N}`$.

**Lean formulation.** The first Lean statement expresses the main conclusion; the second includes
the “Moreover” clause. The changes of notation are:

- Nonemptiness, regular openness and periodicity of X are standing assumptions
  at the beginning of §7 (p. 31). Lean makes them explicit using hX, hXregular,
  and a positive period β.
- `p₁ ⁻¹' X` is $`X\times\mathbb{R}`$. The vectors e₁ and e₂ are $`(1,0)`$ and $`(0,1)`$.
- The prescribed lattice is written $`\Lambda=\mathbb{Z}p+\mathbb{Z}q`$, with p and q
  real-linearly independent. Requiring both to be periods gives
  $`\Lambda\subseteq\Gamma(E)`$.
- Membership in `orbitHullUnder Λ T` replaces the explicit weakly convergent
  sequence. These are equivalent on the uniformly discrete tiling configurations.
- `IsEarthquakeSplit` packages $`S=S_0\sqcup S_1`$, nonemptiness of both parts,
  and directional invariance of their regularized covered regions. This uses
  the paper's null-set convention and Remark 6.5.

```lean4
theorem non_flc_earthquake_limit
    (Ω : Set Plane) (hΩ : IsAxisParallelTile Ω)
    (X : Set ℝ) (hX : X.Nonempty) (hXregular : IsRegularOpen X)
    (β : ℝ) (hβ : 0 < β) (hperiod : β +ᵥ X = X)
    (T : Set Plane) (hT : TilingOn (p₁ ⁻¹' X) Ω T)
    (hFLC : ¬ HasFiniteLocalComplexity T) :
    ∃ S ∈ orbitHull (p₁ ⁻¹' X) T,
      TilingOn (p₁ ⁻¹' X) Ω S ∧
      ∃ v ∈ ({e₁, e₂} : Set Plane), ∃ S₀ S₁,
        (X ≠ univ → v = e₂) ∧ IsEarthquakeSplit Ω S S₀ S₁ v := by
  sorry

theorem non_flc_earthquake_limit_in_lattice
    (Ω : Set Plane) (hΩ : IsAxisParallelTile Ω)
    (X : Set ℝ) (hX : X.Nonempty) (hXregular : IsRegularOpen X)
    (β : ℝ) (hβ : 0 < β) (hperiod : β +ᵥ X = X)
    (T : Set Plane) (hT : TilingOn (p₁ ⁻¹' X) Ω T)
    (hFLC : ¬ HasFiniteLocalComplexity T)
    (p q : Plane) (hpq : LinearIndependent ℝ ![p, q])
    (hp : IsPeriod (p₁ ⁻¹' X) p) (hq : IsPeriod (p₁ ⁻¹' X) q) :
    ∃ S ∈ orbitHullUnder (span ℤ {p, q} : Set Plane) T,
      TilingOn (p₁ ⁻¹' X) Ω S ∧
      ∃ v ∈ ({e₁, e₂} : Set Plane), ∃ S₀ S₁,
        (X ≠ univ → v = e₂) ∧ IsEarthquakeSplit Ω S S₀ S₁ v := by
  sorry
```

### A limit with finite complexity in one coordinate

> **Theorem 8.1, p. 36.**
>
> Let $`T`$ be a tiling of $`\mathbb{R}^2`$ by an axes-parallel polygonal set $`\Omega`$ that
> does not have finite local complexity. Then, after possibly swapping the vertical and
> horizontal axes, there is $`S\in \mathcal{O}_{T}(\Omega;\mathbb{R}^2)`$ such that $`S`$ has
> finite horizontal complexity and the vertical earthquake decomposition of $`S`$ is
> non-trivial.

**Lean formulation.** The two alternatives express the possible swap of axes. In Definition 6.4,
nontriviality means that the whole centre set is not a single non-column plate;
this is the membership condition in the Lean conclusion. The projected finite
local complexity condition includes the required discreteness.

```lean4
theorem non_flc_finite_horizontal_complexity_limit
    (Ω : Set Plane) (hΩ : IsAxisParallelTile Ω)
    (T : Set Plane) (hT : Tiling Ω T) (hFLC : ¬ HasFiniteLocalComplexity T) :
    ∃ S ∈ orbitHull univ T,
      Tiling Ω S ∧
      ((HasFiniteLocalComplexity (p₁ '' S) ∧
          (S : Set Plane) ∉ tectonicPlates Ω e₂ S) ∨
       (HasFiniteLocalComplexity (p₂ '' S) ∧
          (S : Set Plane) ∉ tectonicPlates Ω e₁ S)) := by
  sorry
```

## Vertices

First we identify which boundary points are vertices: points in the middle of a
straight edge are excluded, while corners and boundary junctions are included.

> **§2, “Proper vertices”, p. 6.**
>
> We will use the notion of proper vertex from [Section 2 of the rational-slopes paper]: A point
> $`x\in \partial \overline{D}`$ is a **proper vertex of $`D\subseteq \mathbb{R}^2`$** if for every
> $`\epsilon>0`$, the intersection $`(\mathcal{B}_\epsilon + x) \cap \partial \overline{D}`$ is
> *not* a line segment. We denote by $`W(D)`$ the set of proper vertices of $`D`$.

**Lean formulation.** We specialize proper vertices to regular-open axis-parallel polygonal sets.
For these sets, $`\partial\overline{\Omega}=\partial\Omega`$, and the two coordinate
witnesses are equivalent to the local boundary failing to be a line segment.

```lean4
def vertices (Ω : Set Plane) : Set Plane :=
  {v ∈ frontier Ω | ∀ ε > 0,
    (∃ a ∈ frontier Ω ∩ Metric.ball v ε, p₁ a ≠ p₁ v) ∧
    (∃ b ∈ frontier Ω ∩ Metric.ball v ε, p₂ b ≠ p₂ v)}

end AxisParallelComparator
```
