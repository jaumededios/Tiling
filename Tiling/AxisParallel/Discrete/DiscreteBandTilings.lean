import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Tiling.AxisParallel.Discrete.DiscreteTilingsAndPlates
import Tiling.AxisParallel.Discrete.DiscretePlatePeriodicity

/-!
# Exact tilings of periodized finite discrete bands

The first band lemma is proved directly from pointwise unique representations.  The construction
uses the existing translated sets and exact `Tiles` predicate.
-/

open Set
open TranslationalTilings

namespace Tiling.AxisParallel.Discrete

private def periodizedBandCentres
    (A : Set TranslationalTilings.Plane) (R : ℕ) :
    Set TranslationalTilings.Plane :=
  ⋃ d : ℤ, TranslationalTilings.translateSet
    ((d * (R : ℤ)) • horizontalDiscreteUnit) A

private def bandCopyGraph
    (F : Finset TranslationalTilings.Plane)
    (A : Set TranslationalTilings.Plane) : SimpleGraph (A × ℤ) where
  Adj x y :=
    (Tiling.RationalPolygonal.quakeGraph F A verticalDiscreteUnit).Adj x.1 y.1 ∧
      x.2 = y.2
  symm := ⟨fun _ _ h ↦ ⟨h.1.symm, h.2.symm⟩⟩
  loopless := ⟨fun x h ↦
    (Tiling.RationalPolygonal.quakeGraph F A verticalDiscreteUnit).loopless.irrefl x.1 h.1⟩

private def bandCopyEmbedding
    (F : Finset TranslationalTilings.Plane)
    (A : Set TranslationalTilings.Plane) (d : ℤ) :
    Tiling.RationalPolygonal.quakeGraph F A verticalDiscreteUnit →g
      bandCopyGraph F A where
  toFun a := (a, d)
  map_rel' := by
    intro a b hab
    exact ⟨hab, rfl⟩

private def bandCopyProjection
    (F : Finset TranslationalTilings.Plane)
    (A : Set TranslationalTilings.Plane) :
    bandCopyGraph F A →g
      Tiling.RationalPolygonal.quakeGraph F A verticalDiscreteUnit where
  toFun := Prod.fst
  map_rel' := fun h ↦ h.1

private theorem bandCopyGraph_walk_snd
    {F : Finset TranslationalTilings.Plane}
    {A : Set TranslationalTilings.Plane} {x y : A × ℤ}
    (w : (bandCopyGraph F A).Walk x y) : x.2 = y.2 := by
  induction w with
  | nil => rfl
  | cons h _ ih => exact h.2.trans ih

private def bandCopyComponentIndex
    {F : Finset TranslationalTilings.Plane}
    {A : Set TranslationalTilings.Plane}
    (C : (bandCopyGraph F A).ConnectedComponent) : ℤ :=
  C.lift Prod.snd fun _ _ p _ ↦ bandCopyGraph_walk_snd p

private noncomputable def bandCopyComponentEquiv
    (F : Finset TranslationalTilings.Plane)
    (A : Set TranslationalTilings.Plane) :
    (Tiling.RationalPolygonal.QuakePlate F A verticalDiscreteUnit × ℤ) ≃
      (bandCopyGraph F A).ConnectedComponent where
  toFun x := x.1.map (bandCopyEmbedding F A x.2)
  invFun C :=
    (C.map (bandCopyProjection F A), bandCopyComponentIndex C)
  left_inv := by
    rintro ⟨C, d⟩
    apply Prod.ext
    · exact C.ind fun _ ↦ rfl
    · exact C.ind fun _ ↦ rfl
  right_inv := by
    intro C
    exact C.ind fun _ ↦ rfl

private theorem verticalDiscreteCylinder_periodic
    (B : Set ℤ) :
    Tiling.RationalPolygonal.DiscretePeriodicBy
      (verticalDiscreteCylinder B) verticalDiscreteUnit := by
  intro z
  rw [mem_verticalDiscreteCylinder_iff, mem_verticalDiscreteCylinder_iff]
  simp [firstDiscreteCoordinate, verticalDiscreteUnit]

private theorem add_mem_target_of_tiles
    {G : Type*} [AddCommGroup G]
    {F : Finset G} {A E : Set G}
    (hTile : TranslationalTilings.Tiles F A E)
    {f a : G} (hf : f ∈ F) (ha : a ∈ A) : f + a ∈ E := by
  classical
  by_contra hnot
  have hcount :=
    (TranslationalTilings.tilesAtLevel_iff_representation_count F A E 1).mp
      hTile (f + a)
  have hzero : (F.filter fun g ↦ f + a - g ∈ A).card = 0 := by
    simpa [hnot] using hcount
  have hmem : f ∈ F.filter fun g ↦ f + a - g ∈ A := by
    simp only [Finset.mem_filter, hf, true_and]
    simpa only [add_sub_cancel_left] using ha
  rw [Finset.card_eq_zero.mp hzero] at hmem
  simp at hmem

private noncomputable def bandCopyVertexEquiv
    {B : Set ℤ} {F : Finset TranslationalTilings.Plane}
    {A : Set TranslationalTilings.Plane} {R : ℕ}
    (hF : F.Nonempty)
    (hTile : TranslationalTilings.Tiles F A (verticalDiscreteCylinder B))
    (hCopies : ∀ p : ℤ × ℤ, p.1 ≠ p.2 →
      Disjoint
        (TranslationalTilings.translateSet
          ((p.1 * (R : ℤ)) • horizontalDiscreteUnit)
          (verticalDiscreteCylinder B))
        (TranslationalTilings.translateSet
          ((p.2 * (R : ℤ)) • horizontalDiscreteUnit)
          (verticalDiscreteCylinder B))) :
    A × ℤ ≃ ↑(periodizedBandCentres A R) := by
  classical
  let copyPoint : A × ℤ → ↑(periodizedBandCentres A R) := fun x ↦
    ⟨(x.2 * (R : ℤ)) • horizontalDiscreteUnit + (x.1 : TranslationalTilings.Plane), by
      apply Set.mem_iUnion.mpr
      refine ⟨x.2, ?_⟩
      change (x.2 * (R : ℤ)) • horizontalDiscreteUnit +
          (x.1 : TranslationalTilings.Plane) -
          (x.2 * (R : ℤ)) • horizontalDiscreteUnit ∈ A
      simpa only [add_sub_cancel_left] using x.1.2⟩
  apply Equiv.ofBijective copyPoint
  constructor
  · rintro ⟨a, d⟩ ⟨b, e⟩ hde
    have hpoint :
        (d * (R : ℤ)) • horizontalDiscreteUnit +
            (a : TranslationalTilings.Plane) =
          (e * (R : ℤ)) • horizontalDiscreteUnit +
            (b : TranslationalTilings.Plane) :=
      congrArg Subtype.val hde
    obtain ⟨f, hf⟩ := hF
    have hfa := add_mem_target_of_tiles hTile hf a.2
    have hfb := add_mem_target_of_tiles hTile hf b.2
    have hxD : f + ((d * (R : ℤ)) • horizontalDiscreteUnit +
          (a : TranslationalTilings.Plane)) ∈
        TranslationalTilings.translateSet
          ((d * (R : ℤ)) • horizontalDiscreteUnit)
          (verticalDiscreteCylinder B) := by
      change f + ((d * (R : ℤ)) • horizontalDiscreteUnit +
          (a : TranslationalTilings.Plane)) -
          (d * (R : ℤ)) • horizontalDiscreteUnit ∈
        verticalDiscreteCylinder B
      convert hfa using 1
      all_goals abel
    have hxE : f + ((d * (R : ℤ)) • horizontalDiscreteUnit +
          (a : TranslationalTilings.Plane)) ∈
        TranslationalTilings.translateSet
          ((e * (R : ℤ)) • horizontalDiscreteUnit)
          (verticalDiscreteCylinder B) := by
      rw [hpoint]
      change f + ((e * (R : ℤ)) • horizontalDiscreteUnit +
          (b : TranslationalTilings.Plane)) -
          (e * (R : ℤ)) • horizontalDiscreteUnit ∈
        verticalDiscreteCylinder B
      convert hfb using 1
      all_goals abel
    have hed : d = e := by
      by_contra hne
      exact (Set.disjoint_left.mp (hCopies (d, e) hne)) hxD hxE
    subst e
    apply Prod.ext
    · apply Subtype.ext
      exact add_left_cancel hpoint
    · rfl
  · rintro ⟨x, hx⟩
    obtain ⟨d, hxd⟩ := Set.mem_iUnion.mp hx
    let a : A := ⟨x - (d * (R : ℤ)) • horizontalDiscreteUnit, hxd⟩
    refine ⟨(a, d), ?_⟩
    apply Subtype.ext
    dsimp only [copyPoint, a]
    abel

@[simp]
private theorem bandCopyVertexEquiv_apply
    {B : Set ℤ} {F : Finset TranslationalTilings.Plane}
    {A : Set TranslationalTilings.Plane} {R : ℕ}
    (hF : F.Nonempty)
    (hTile : TranslationalTilings.Tiles F A (verticalDiscreteCylinder B))
    (hCopies : ∀ p : ℤ × ℤ, p.1 ≠ p.2 →
      Disjoint
        (TranslationalTilings.translateSet
          ((p.1 * (R : ℤ)) • horizontalDiscreteUnit)
          (verticalDiscreteCylinder B))
        (TranslationalTilings.translateSet
          ((p.2 * (R : ℤ)) • horizontalDiscreteUnit)
          (verticalDiscreteCylinder B)))
    (x : A × ℤ) :
    ((bandCopyVertexEquiv hF hTile hCopies x :
      ↑(periodizedBandCentres A R)) : TranslationalTilings.Plane) =
      (x.2 * (R : ℤ)) • horizontalDiscreteUnit +
        (x.1 : TranslationalTilings.Plane) :=
  rfl

private theorem bandCopyQuakeTransfer_iff
    {B : Set ℤ} {F : Finset TranslationalTilings.Plane}
    {A : Set TranslationalTilings.Plane} {R : ℕ}
    (hF : F.Nonempty)
    (hTile : TranslationalTilings.Tiles F A (verticalDiscreteCylinder B))
    (hCopies : ∀ p : ℤ × ℤ, p.1 ≠ p.2 →
      Disjoint
        (TranslationalTilings.translateSet
          ((p.1 * (R : ℤ)) • horizontalDiscreteUnit)
          (verticalDiscreteCylinder B))
        (TranslationalTilings.translateSet
          ((p.2 * (R : ℤ)) • horizontalDiscreteUnit)
          (verticalDiscreteCylinder B)))
    (x y : A × ℤ) :
    Tiling.RationalPolygonal.quakeTransfer F (periodizedBandCentres A R)
        verticalDiscreteUnit
        (bandCopyVertexEquiv hF hTile hCopies x)
        (bandCopyVertexEquiv hF hTile hCopies y) ↔
      x.2 = y.2 ∧
        Tiling.RationalPolygonal.quakeTransfer F A verticalDiscreteUnit x.1 y.1 := by
  classical
  constructor
  · rintro ⟨f, hf, g, hg, heq⟩
    have hfa := add_mem_target_of_tiles hTile hf x.1.2
    have hfb := add_mem_target_of_tiles hTile hg y.1.2
    have hfav := (verticalDiscreteCylinder_periodic B (f + x.1)).2 hfa
    have hxCopy :
        f + (bandCopyVertexEquiv hF hTile hCopies x :
          TranslationalTilings.Plane) + verticalDiscreteUnit ∈
          TranslationalTilings.translateSet
            ((x.2 * (R : ℤ)) • horizontalDiscreteUnit)
            (verticalDiscreteCylinder B) := by
      rw [bandCopyVertexEquiv_apply]
      change f + ((x.2 * (R : ℤ)) • horizontalDiscreteUnit +
          (x.1 : TranslationalTilings.Plane)) + verticalDiscreteUnit -
          (x.2 * (R : ℤ)) • horizontalDiscreteUnit ∈
        verticalDiscreteCylinder B
      convert hfav using 1
      all_goals abel
    have hyCopy :
        f + (bandCopyVertexEquiv hF hTile hCopies x :
          TranslationalTilings.Plane) + verticalDiscreteUnit ∈
          TranslationalTilings.translateSet
            ((y.2 * (R : ℤ)) • horizontalDiscreteUnit)
            (verticalDiscreteCylinder B) := by
      rw [heq, bandCopyVertexEquiv_apply]
      change g + ((y.2 * (R : ℤ)) • horizontalDiscreteUnit +
          (y.1 : TranslationalTilings.Plane)) -
          (y.2 * (R : ℤ)) • horizontalDiscreteUnit ∈
        verticalDiscreteCylinder B
      convert hfb using 1
      all_goals abel
    have hxy : x.2 = y.2 := by
      by_contra hne
      exact (Set.disjoint_left.mp (hCopies (x.2, y.2) hne)) hxCopy hyCopy
    refine ⟨hxy, f, hf, g, hg, ?_⟩
    rw [bandCopyVertexEquiv_apply, bandCopyVertexEquiv_apply] at heq
    rw [hxy] at heq
    let shift := (y.2 * (R : ℤ)) • horizontalDiscreteUnit
    apply add_left_cancel (a := shift)
    calc
      shift + (f + (x.1 : TranslationalTilings.Plane) + verticalDiscreteUnit) =
          f + (shift + (x.1 : TranslationalTilings.Plane)) + verticalDiscreteUnit := by
            abel
      _ = g + (shift + (y.1 : TranslationalTilings.Plane)) := heq
      _ = shift + (g + (y.1 : TranslationalTilings.Plane)) := by abel
  · rintro ⟨hxy, f, hf, g, hg, heq⟩
    refine ⟨f, hf, g, hg, ?_⟩
    rw [bandCopyVertexEquiv_apply, bandCopyVertexEquiv_apply, hxy]
    calc
      f + ((y.2 * (R : ℤ)) • horizontalDiscreteUnit +
          (x.1 : TranslationalTilings.Plane)) + verticalDiscreteUnit =
        (y.2 * (R : ℤ)) • horizontalDiscreteUnit +
          (f + (x.1 : TranslationalTilings.Plane) + verticalDiscreteUnit) := by abel
      _ = (y.2 * (R : ℤ)) • horizontalDiscreteUnit +
          (g + (y.1 : TranslationalTilings.Plane)) := congrArg _ heq
      _ = g + ((y.2 * (R : ℤ)) • horizontalDiscreteUnit +
          (y.1 : TranslationalTilings.Plane)) := by abel

private noncomputable def bandCopyGraphIso
    {B : Set ℤ} {F : Finset TranslationalTilings.Plane}
    {A : Set TranslationalTilings.Plane} {R : ℕ}
    (hF : F.Nonempty)
    (hTile : TranslationalTilings.Tiles F A (verticalDiscreteCylinder B))
    (hCopies : ∀ p : ℤ × ℤ, p.1 ≠ p.2 →
      Disjoint
        (TranslationalTilings.translateSet
          ((p.1 * (R : ℤ)) • horizontalDiscreteUnit)
          (verticalDiscreteCylinder B))
        (TranslationalTilings.translateSet
          ((p.2 * (R : ℤ)) • horizontalDiscreteUnit)
          (verticalDiscreteCylinder B))) :
    bandCopyGraph F A ≃g
      Tiling.RationalPolygonal.quakeGraph F (periodizedBandCentres A R)
        verticalDiscreteUnit where
  toEquiv := bandCopyVertexEquiv hF hTile hCopies
  map_rel_iff' := by
    intro x y
    change
      (Tiling.RationalPolygonal.quakeGraph F (periodizedBandCentres A R)
          verticalDiscreteUnit).Adj
          (bandCopyVertexEquiv hF hTile hCopies x)
          (bandCopyVertexEquiv hF hTile hCopies y) ↔
        (Tiling.RationalPolygonal.quakeGraph F A verticalDiscreteUnit).Adj x.1 y.1 ∧
          x.2 = y.2
    simp only [Tiling.RationalPolygonal.quakeGraph, SimpleGraph.fromRel_adj]
    rw [bandCopyQuakeTransfer_iff hF hTile hCopies,
      bandCopyQuakeTransfer_iff hF hTile hCopies]
    constructor
    · rintro ⟨hne, h | h⟩
      · refine ⟨⟨?_, Or.inl h.2⟩, h.1⟩
        intro hfirst
        apply hne
        exact congrArg (bandCopyVertexEquiv hF hTile hCopies)
          (Prod.ext hfirst h.1)
      · refine ⟨⟨?_, Or.inr h.2⟩, h.1.symm⟩
        intro hfirst
        apply hne
        exact congrArg (bandCopyVertexEquiv hF hTile hCopies)
          (Prod.ext hfirst h.1.symm)
    · rintro ⟨⟨hne, htrans⟩, hxy⟩
      refine ⟨?_, ?_⟩
      · apply (bandCopyVertexEquiv hF hTile hCopies).injective.ne
        intro hprod
        exact hne (congrArg Prod.fst hprod)
      · rcases htrans with h | h
        · exact Or.inl ⟨hxy, h⟩
        · exact Or.inr ⟨hxy.symm, h⟩

private noncomputable def periodizedBandPlateEquiv
    {B : Set ℤ} {F : Finset TranslationalTilings.Plane}
    {A : Set TranslationalTilings.Plane} {R : ℕ}
    (hF : F.Nonempty)
    (hTile : TranslationalTilings.Tiles F A (verticalDiscreteCylinder B))
    (hCopies : ∀ p : ℤ × ℤ, p.1 ≠ p.2 →
      Disjoint
        (TranslationalTilings.translateSet
          ((p.1 * (R : ℤ)) • horizontalDiscreteUnit)
          (verticalDiscreteCylinder B))
        (TranslationalTilings.translateSet
          ((p.2 * (R : ℤ)) • horizontalDiscreteUnit)
          (verticalDiscreteCylinder B))) :
    (Tiling.RationalPolygonal.QuakePlate F A verticalDiscreteUnit × ℤ) ≃
      Tiling.RationalPolygonal.QuakePlate F
        (periodizedBandCentres A R) verticalDiscreteUnit :=
  (bandCopyComponentEquiv F A).trans
    (bandCopyGraphIso hF hTile hCopies).connectedComponentEquiv

@[simp]
private theorem periodizedBandPlateEquiv_mk
    {B : Set ℤ} {F : Finset TranslationalTilings.Plane}
    {A : Set TranslationalTilings.Plane} {R : ℕ}
    (hF : F.Nonempty)
    (hTile : TranslationalTilings.Tiles F A (verticalDiscreteCylinder B))
    (hCopies : ∀ p : ℤ × ℤ, p.1 ≠ p.2 →
      Disjoint
        (TranslationalTilings.translateSet
          ((p.1 * (R : ℤ)) • horizontalDiscreteUnit)
          (verticalDiscreteCylinder B))
        (TranslationalTilings.translateSet
          ((p.2 * (R : ℤ)) • horizontalDiscreteUnit)
          (verticalDiscreteCylinder B)))
    (a : A) (d : ℤ) :
    periodizedBandPlateEquiv hF hTile hCopies
        ((Tiling.RationalPolygonal.quakeGraph F A verticalDiscreteUnit).connectedComponentMk a,
          d) =
      (Tiling.RationalPolygonal.quakeGraph F (periodizedBandCentres A R)
        verticalDiscreteUnit).connectedComponentMk
          (bandCopyVertexEquiv hF hTile hCopies (a, d)) :=
  rfl

private theorem periodizedBandPlateEquiv_translations
    {B : Set ℤ} {F : Finset TranslationalTilings.Plane}
    {A : Set TranslationalTilings.Plane} {R : ℕ}
    (hF : F.Nonempty)
    (hTile : TranslationalTilings.Tiles F A (verticalDiscreteCylinder B))
    (hCopies : ∀ p : ℤ × ℤ, p.1 ≠ p.2 →
      Disjoint
        (TranslationalTilings.translateSet
          ((p.1 * (R : ℤ)) • horizontalDiscreteUnit)
          (verticalDiscreteCylinder B))
        (TranslationalTilings.translateSet
          ((p.2 * (R : ℤ)) • horizontalDiscreteUnit)
          (verticalDiscreteCylinder B)))
    (P : Tiling.RationalPolygonal.QuakePlate F A verticalDiscreteUnit)
    (d : ℤ) :
    Tiling.RationalPolygonal.quakePlateTranslations
        (periodizedBandPlateEquiv hF hTile hCopies (P, d)) =
      TranslationalTilings.translateSet
        ((d * (R : ℤ)) • horizontalDiscreteUnit)
        (Tiling.RationalPolygonal.quakePlateTranslations P) := by
  classical
  ext z
  constructor
  · rintro ⟨hzUnion, hzComponent⟩
    let q : ↑(periodizedBandCentres A R) := ⟨z, hzUnion⟩
    let x : A × ℤ := (bandCopyVertexEquiv hF hTile hCopies).symm q
    have hxVertex : bandCopyVertexEquiv hF hTile hCopies x = q :=
      (bandCopyVertexEquiv hF hTile hCopies).apply_symm_apply q
    have hxComponent :
        periodizedBandPlateEquiv hF hTile hCopies
            ((Tiling.RationalPolygonal.quakeGraph F A verticalDiscreteUnit
              ).connectedComponentMk x.1, x.2) =
          periodizedBandPlateEquiv hF hTile hCopies (P, d) := by
      rw [periodizedBandPlateEquiv_mk]
      rw [hxVertex]
      exact hzComponent
    have hxPair := (periodizedBandPlateEquiv hF hTile hCopies).injective hxComponent
    have hxPlate :
        (Tiling.RationalPolygonal.quakeGraph F A verticalDiscreteUnit
          ).connectedComponentMk x.1 = P :=
      congrArg Prod.fst hxPair
    have hxIndex : x.2 = d := congrArg Prod.snd hxPair
    change z - (d * (R : ℤ)) • horizontalDiscreteUnit ∈
      Tiling.RationalPolygonal.quakePlateTranslations P
    have hval := congrArg Subtype.val hxVertex
    rw [bandCopyVertexEquiv_apply] at hval
    dsimp only [q] at hval
    rw [hxIndex] at hval
    have hxPoint : z - (d * (R : ℤ)) • horizontalDiscreteUnit =
        (x.1 : TranslationalTilings.Plane) := by
      rw [← hval]
      abel
    have hzA : z - (d * (R : ℤ)) • horizontalDiscreteUnit ∈ A := by
      rw [hxPoint]
      exact x.1.2
    refine ⟨hzA, ?_⟩
    have hsubtype :
        (⟨z - (d * (R : ℤ)) • horizontalDiscreteUnit, hzA⟩ : A) = x.1 :=
      Subtype.ext hxPoint
    rw [hsubtype]
    exact hxPlate
  · intro hz
    change z - (d * (R : ℤ)) • horizontalDiscreteUnit ∈
      Tiling.RationalPolygonal.quakePlateTranslations P at hz
    let a : A :=
      ⟨z - (d * (R : ℤ)) • horizontalDiscreteUnit,
        Classical.choose hz⟩
    have haComponent :
        (Tiling.RationalPolygonal.quakeGraph F A verticalDiscreteUnit
          ).connectedComponentMk a = P := by
      exact Classical.choose_spec hz
    have hzUnion : z ∈ periodizedBandCentres A R := by
      apply Set.mem_iUnion.mpr
      refine ⟨d, ?_⟩
      exact Classical.choose hz
    refine ⟨hzUnion, ?_⟩
    rw [← haComponent, periodizedBandPlateEquiv_mk]
    apply congrArg
    apply Subtype.ext
    rw [bandCopyVertexEquiv_apply]
    dsimp only [a]
    abel

private theorem existsUnique_representation_of_mem
    {G : Type*} [AddCommGroup G]
    {F : Finset G} {A E : Set G}
    (hTile : TranslationalTilings.Tiles F A E)
    {x : G} (hx : x ∈ E) :
    ∃! f : G, f ∈ F ∧ x - f ∈ A := by
  classical
  have hcount :=
    (TranslationalTilings.tilesAtLevel_iff_representation_count F A E 1).mp hTile x
  have hcard : (F.filter fun f ↦ x - f ∈ A).card = 1 := by
    simpa [hx] using hcount
  obtain ⟨f, hfilter⟩ := Finset.card_eq_one.mp hcard
  refine ⟨f, ?_, ?_⟩
  · have : f ∈ F.filter fun g ↦ x - g ∈ A := by simp [hfilter]
    simpa using this
  · intro g hg
    have hgm : g ∈ F.filter fun f ↦ x - f ∈ A := by simpa using hg
    simpa [hfilter] using hgm

private theorem tiles_of_existsUnique_on_target
    {G : Type*} [AddCommGroup G]
    {F : Finset G} {A E : Set G}
    (hrep : ∀ x, x ∈ E → ∃! f : G, f ∈ F ∧ x - f ∈ A)
    (houtside : ∀ x, x ∉ E → ∀ f ∈ F, x - f ∉ A) :
    TranslationalTilings.Tiles F A E := by
  classical
  apply (TranslationalTilings.tilesAtLevel_iff_representation_count F A E 1).mpr
  intro x
  by_cases hx : x ∈ E
  · obtain ⟨f, hf, hunique⟩ := hrep x hx
    have hfilter : (F.filter fun g ↦ x - g ∈ A) = {f} := by
      ext g
      constructor
      · intro hg
        have hg' : g ∈ F ∧ x - g ∈ A := by simpa using hg
        simpa only [Finset.mem_singleton] using hunique g hg'
      · intro hg
        have hgf : g = f := by simpa only [Finset.mem_singleton] using hg
        subst g
        simpa using hf
    rw [if_pos hx, hfilter]
    simp
  · have hfilter : (F.filter fun f ↦ x - f ∈ A) = ∅ :=
      Finset.filter_eq_empty_iff.mpr fun f hf ↦ houtside x hx f hf
    rw [if_neg hx, hfilter]
    simp

theorem periodizeFiniteBand_tiles_general
    {B : Finset ℤ} {F : Finset TranslationalTilings.Plane}
    {A : Set TranslationalTilings.Plane} {R : ℕ}
    (hTile : TranslationalTilings.Tiles F A
      (verticalDiscreteCylinder (B : Set ℤ)))
    (_hR : 0 < R)
    (hCopies : ∀ p : ℤ × ℤ, p.1 ≠ p.2 →
      Disjoint
        (TranslationalTilings.translateSet
          ((p.1 * (R : ℤ)) • horizontalDiscreteUnit)
          (verticalDiscreteCylinder (B : Set ℤ)))
        (TranslationalTilings.translateSet
          ((p.2 * (R : ℤ)) • horizontalDiscreteUnit)
          (verticalDiscreteCylinder (B : Set ℤ)))) :
    TranslationalTilings.Tiles F
        (⋃ d : ℤ, TranslationalTilings.translateSet
          ((d * (R : ℤ)) • horizontalDiscreteUnit) A)
        (⋃ d : ℤ, TranslationalTilings.translateSet
          ((d * (R : ℤ)) • horizontalDiscreteUnit)
          (verticalDiscreteCylinder (B : Set ℤ))) ∧
      Tiling.RationalPolygonal.DiscretePeriodicBy
        (⋃ d : ℤ, TranslationalTilings.translateSet
          ((d * (R : ℤ)) • horizontalDiscreteUnit)
          (verticalDiscreteCylinder (B : Set ℤ)))
        verticalDiscreteUnit ∧
      TranslationalTilings.SetScalarPeriodic R
        (⋃ d : ℤ, TranslationalTilings.translateSet
          ((d * (R : ℤ)) • horizontalDiscreteUnit)
          (verticalDiscreteCylinder (B : Set ℤ))) := by
  classical
  let centreUnion : Set TranslationalTilings.Plane :=
    ⋃ d : ℤ, TranslationalTilings.translateSet
      ((d * (R : ℤ)) • horizontalDiscreteUnit) A
  let targetUnion : Set TranslationalTilings.Plane :=
    ⋃ d : ℤ, TranslationalTilings.translateSet
      ((d * (R : ℤ)) • horizontalDiscreteUnit)
      (verticalDiscreteCylinder (B : Set ℤ))
  have hperiodized : TranslationalTilings.Tiles F centreUnion targetUnion := by
    apply tiles_of_existsUnique_on_target
    · intro x hx
      obtain ⟨d, hxd⟩ := Set.mem_iUnion.mp hx
      have hxBase : x - (d * (R : ℤ)) • horizontalDiscreteUnit ∈
          verticalDiscreteCylinder (B : Set ℤ) := hxd
      obtain ⟨f, hf, hfunique⟩ := existsUnique_representation_of_mem hTile hxBase
      refine ⟨f, ⟨hf.1, ?_⟩, ?_⟩
      · apply Set.mem_iUnion.mpr
        refine ⟨d, ?_⟩
        change x - f - (d * (R : ℤ)) • horizontalDiscreteUnit ∈ A
        convert hf.2 using 1
        all_goals abel
      · intro g hg
        obtain ⟨e, hge⟩ := Set.mem_iUnion.mp hg.2
        have hxBaseE : x - (e * (R : ℤ)) • horizontalDiscreteUnit ∈
            verticalDiscreteCylinder (B : Set ℤ) := by
          have hsum := add_mem_target_of_tiles hTile hg.1 hge
          convert hsum using 1
          all_goals abel
        have hxCopyE : x ∈ TranslationalTilings.translateSet
            ((e * (R : ℤ)) • horizontalDiscreteUnit)
            (verticalDiscreteCylinder (B : Set ℤ)) := hxBaseE
        have hed : e = d := by
          by_contra hne
          exact (Set.disjoint_left.mp (hCopies (e, d) hne)) hxCopyE hxd
        subst e
        apply hfunique g
        refine ⟨hg.1, ?_⟩
        change x - g - (d * (R : ℤ)) • horizontalDiscreteUnit ∈ A at hge
        change x - (d * (R : ℤ)) • horizontalDiscreteUnit - g ∈ A
        convert hge using 1
        all_goals abel
    · intro x hx f hf hxf
      obtain ⟨d, hxfd⟩ := Set.mem_iUnion.mp hxf
      apply hx
      apply Set.mem_iUnion.mpr
      refine ⟨d, ?_⟩
      change x - f - (d * (R : ℤ)) • horizontalDiscreteUnit ∈ A at hxfd
      have hsum := add_mem_target_of_tiles hTile hf hxfd
      change x - (d * (R : ℤ)) • horizontalDiscreteUnit ∈
        verticalDiscreteCylinder (B : Set ℤ)
      convert hsum using 1
      all_goals abel
  refine ⟨hperiodized, ?_, ?_⟩
  · intro z
    simp only [Set.mem_iUnion]
    constructor
    · rintro ⟨d, hzd⟩
      refine ⟨d, ?_⟩
      apply (mem_verticalDiscreteCylinder_iff _ _).mpr
      have hcoord := (mem_verticalDiscreteCylinder_iff
        (z + verticalDiscreteUnit - (d * (R : ℤ)) • horizontalDiscreteUnit)
        (B : Set ℤ)).mp hzd
      simpa [firstDiscreteCoordinate, horizontalDiscreteUnit, verticalDiscreteUnit,
        Matrix.vecHead, Matrix.vecTail] using hcoord
    · rintro ⟨d, hzd⟩
      refine ⟨d, ?_⟩
      apply (mem_verticalDiscreteCylinder_iff _ _).mpr
      have hcoord := (mem_verticalDiscreteCylinder_iff
        (z - (d * (R : ℤ)) • horizontalDiscreteUnit)
        (B : Set ℤ)).mp hzd
      simpa [firstDiscreteCoordinate, horizontalDiscreteUnit, verticalDiscreteUnit,
        Matrix.vecHead, Matrix.vecTail] using hcoord
  · intro z w
    simp only [Set.mem_iUnion]
    constructor
    · rintro ⟨d, hzd⟩
      refine ⟨d - w 0, ?_⟩
      apply (mem_verticalDiscreteCylinder_iff _ _).mpr
      have hcoord := (mem_verticalDiscreteCylinder_iff
        (z + (R : ℤ) • w - (d * (R : ℤ)) • horizontalDiscreteUnit)
        (B : Set ℤ)).mp hzd
      have hcoord' : z 0 + (R : ℤ) * w 0 - d * (R : ℤ) ∈ (B : Set ℤ) := by
        simpa [firstDiscreteCoordinate, horizontalDiscreteUnit, Matrix.vecHead,
          Matrix.vecTail] using hcoord
      have heq : z 0 - (d - w 0) * (R : ℤ) =
          z 0 + (R : ℤ) * w 0 - d * (R : ℤ) := by ring
      simpa [firstDiscreteCoordinate, horizontalDiscreteUnit, Matrix.vecHead,
        Matrix.vecTail, heq] using hcoord'
    · rintro ⟨d, hzd⟩
      refine ⟨d + w 0, ?_⟩
      apply (mem_verticalDiscreteCylinder_iff _ _).mpr
      have hcoord := (mem_verticalDiscreteCylinder_iff
        (z - (d * (R : ℤ)) • horizontalDiscreteUnit)
        (B : Set ℤ)).mp hzd
      have hcoord' : z 0 - d * (R : ℤ) ∈ (B : Set ℤ) := by
        simpa [firstDiscreteCoordinate, horizontalDiscreteUnit, Matrix.vecHead,
          Matrix.vecTail] using hcoord
      have heq : z 0 + (R : ℤ) * w 0 - (d + w 0) * (R : ℤ) =
          z 0 - d * (R : ℤ) := by ring
      simpa [firstDiscreteCoordinate, horizontalDiscreteUnit, Matrix.vecHead,
        Matrix.vecTail, heq] using hcoord'

theorem periodizeFiniteBand_tiles
    {B : Finset ℤ} {F : Finset TranslationalTilings.Plane}
    {A : Set TranslationalTilings.Plane} {R : ℕ}
    (_hF : F.Nonempty)
    (_hFB : (F : Set TranslationalTilings.Plane) ⊆
      verticalDiscreteCylinder (B : Set ℤ))
    (hTile : TranslationalTilings.Tiles F A
      (verticalDiscreteCylinder (B : Set ℤ)))
    (hR : 0 < R)
    (hCopies : ∀ p : ℤ × ℤ, p.1 ≠ p.2 →
      Disjoint
        (TranslationalTilings.translateSet
          ((p.1 * (R : ℤ)) • horizontalDiscreteUnit)
          (verticalDiscreteCylinder (B : Set ℤ)))
        (TranslationalTilings.translateSet
          ((p.2 * (R : ℤ)) • horizontalDiscreteUnit)
          (verticalDiscreteCylinder (B : Set ℤ)))) :
    TranslationalTilings.Tiles F
        (⋃ d : ℤ, TranslationalTilings.translateSet
          ((d * (R : ℤ)) • horizontalDiscreteUnit) A)
        (⋃ d : ℤ, TranslationalTilings.translateSet
          ((d * (R : ℤ)) • horizontalDiscreteUnit)
          (verticalDiscreteCylinder (B : Set ℤ))) ∧
      Tiling.RationalPolygonal.DiscretePeriodicBy
        (⋃ d : ℤ, TranslationalTilings.translateSet
          ((d * (R : ℤ)) • horizontalDiscreteUnit)
          (verticalDiscreteCylinder (B : Set ℤ)))
        verticalDiscreteUnit ∧
      TranslationalTilings.SetScalarPeriodic R
        (⋃ d : ℤ, TranslationalTilings.translateSet
          ((d * (R : ℤ)) • horizontalDiscreteUnit)
          (verticalDiscreteCylinder (B : Set ℤ))) :=
    periodizeFiniteBand_tiles_general hTile hR hCopies

theorem periodizeFiniteBand_verticalPlates_general
    {B : Finset ℤ} {F : Finset TranslationalTilings.Plane}
    {A : Set TranslationalTilings.Plane} {R : ℕ}
    (hF : F.Nonempty)
    (hTile : TranslationalTilings.Tiles F A
      (verticalDiscreteCylinder (B : Set ℤ)))
    (hR : 0 < R)
    (hCopies : ∀ p : ℤ × ℤ, p.1 ≠ p.2 →
      Disjoint
        (TranslationalTilings.translateSet
          ((p.1 * (R : ℤ)) • horizontalDiscreteUnit)
          (verticalDiscreteCylinder (B : Set ℤ)))
        (TranslationalTilings.translateSet
          ((p.2 * (R : ℤ)) • horizontalDiscreteUnit)
          (verticalDiscreteCylinder (B : Set ℤ)))) :
    ∃ plateEquiv :
        (Tiling.RationalPolygonal.QuakePlate F A verticalDiscreteUnit × ℤ) ≃
          Tiling.RationalPolygonal.QuakePlate F
            (⋃ d : ℤ, TranslationalTilings.translateSet
              ((d * (R : ℤ)) • horizontalDiscreteUnit) A)
            verticalDiscreteUnit,
      ∀ (P : Tiling.RationalPolygonal.QuakePlate F A verticalDiscreteUnit)
          (d : ℤ),
        Tiling.RationalPolygonal.quakePlateTranslations
            (plateEquiv (P, d)) =
          TranslationalTilings.translateSet
            ((d * (R : ℤ)) • horizontalDiscreteUnit)
            (Tiling.RationalPolygonal.quakePlateTranslations P) ∧
          (IsDiscreteVerticalColumn (plateEquiv (P, d)) ↔
            IsDiscreteVerticalColumn P) := by
  classical
  have _hPeriodized := periodizeFiniteBand_tiles_general hTile hR hCopies
  let plateEquiv :
      (Tiling.RationalPolygonal.QuakePlate F A verticalDiscreteUnit × ℤ) ≃
        Tiling.RationalPolygonal.QuakePlate F
          (⋃ d : ℤ, TranslationalTilings.translateSet
            ((d * (R : ℤ)) • horizontalDiscreteUnit) A)
          verticalDiscreteUnit :=
    periodizedBandPlateEquiv hF hTile hCopies
  refine ⟨plateEquiv, ?_⟩
  intro P d
  have hTranslations :
      Tiling.RationalPolygonal.quakePlateTranslations (plateEquiv (P, d)) =
        TranslationalTilings.translateSet
          ((d * (R : ℤ)) • horizontalDiscreteUnit)
          (Tiling.RationalPolygonal.quakePlateTranslations P) := by
    dsimp only [plateEquiv]
    exact periodizedBandPlateEquiv_translations hF hTile hCopies P d
  refine ⟨hTranslations, ?_⟩
  have hImage :
      firstDiscreteCoordinate ''
          Tiling.RationalPolygonal.quakePlateTranslations (plateEquiv (P, d)) =
        (fun c : ℤ ↦ d * (R : ℤ) + c) ''
          (firstDiscreteCoordinate ''
            Tiling.RationalPolygonal.quakePlateTranslations P) := by
    ext c
    constructor
    · rintro ⟨z, hz, rfl⟩
      rw [hTranslations] at hz
      refine ⟨firstDiscreteCoordinate
          (z - (d * (R : ℤ)) • horizontalDiscreteUnit), ⟨?_, ?_⟩⟩
      · exact ⟨z - (d * (R : ℤ)) • horizontalDiscreteUnit, hz, rfl⟩
      · simp [firstDiscreteCoordinate, horizontalDiscreteUnit]
    · rintro ⟨c, ⟨z, hz, rfl⟩, rfl⟩
      refine ⟨(d * (R : ℤ)) • horizontalDiscreteUnit + z, ?_, ?_⟩
      · rw [hTranslations]
        change (d * (R : ℤ)) • horizontalDiscreteUnit + z -
            (d * (R : ℤ)) • horizontalDiscreteUnit ∈
          Tiling.RationalPolygonal.quakePlateTranslations P
        simpa only [add_sub_cancel_left] using hz
      · simp [firstDiscreteCoordinate, horizontalDiscreteUnit]
  constructor
  · rintro ⟨c, hc⟩
    refine ⟨c - d * (R : ℤ), ?_⟩
    ext u
    constructor
    · intro hu
      have huk : d * (R : ℤ) + u ∈
          firstDiscreteCoordinate ''
            Tiling.RationalPolygonal.quakePlateTranslations (plateEquiv (P, d)) := by
        rw [hImage]
        exact ⟨u, hu, rfl⟩
      rw [hc] at huk
      have : d * (R : ℤ) + u = c := Set.mem_singleton_iff.mp huk
      exact Set.mem_singleton_iff.mpr (by omega)
    · intro hu
      have hcImage : c ∈
          firstDiscreteCoordinate ''
            Tiling.RationalPolygonal.quakePlateTranslations (plateEquiv (P, d)) := by
        rw [hc]
        exact Set.mem_singleton c
      rw [hImage] at hcImage
      obtain ⟨v, hv, rfl⟩ := hcImage
      have huEq : u = d * (R : ℤ) + v - d * (R : ℤ) :=
        Set.mem_singleton_iff.mp hu
      have huv : u = v := by omega
      rwa [huv]
  · rintro ⟨c, hc⟩
    refine ⟨d * (R : ℤ) + c, ?_⟩
    rw [hImage, hc]
    ext u
    simp only [Set.mem_image, Set.mem_singleton_iff]
    constructor
    · rintro ⟨v, rfl, rfl⟩
      rfl
    · intro hu
      exact ⟨c, rfl, hu.symm⟩

theorem periodizeFiniteBand_verticalPlates
    {B : Finset ℤ} {F : Finset TranslationalTilings.Plane}
    {A : Set TranslationalTilings.Plane} {R : ℕ}
    (hF : F.Nonempty)
    (_hFB : (F : Set TranslationalTilings.Plane) ⊆
      verticalDiscreteCylinder (B : Set ℤ))
    (hTile : TranslationalTilings.Tiles F A
      (verticalDiscreteCylinder (B : Set ℤ)))
    (hR : 0 < R)
    (hCopies : ∀ p : ℤ × ℤ, p.1 ≠ p.2 →
      Disjoint
        (TranslationalTilings.translateSet
          ((p.1 * (R : ℤ)) • horizontalDiscreteUnit)
          (verticalDiscreteCylinder (B : Set ℤ)))
        (TranslationalTilings.translateSet
          ((p.2 * (R : ℤ)) • horizontalDiscreteUnit)
          (verticalDiscreteCylinder (B : Set ℤ)))) :
    ∃ plateEquiv :
        (Tiling.RationalPolygonal.QuakePlate F A verticalDiscreteUnit × ℤ) ≃
          Tiling.RationalPolygonal.QuakePlate F
            (⋃ d : ℤ, TranslationalTilings.translateSet
              ((d * (R : ℤ)) • horizontalDiscreteUnit) A)
            verticalDiscreteUnit,
      ∀ (P : Tiling.RationalPolygonal.QuakePlate F A verticalDiscreteUnit)
          (d : ℤ),
        Tiling.RationalPolygonal.quakePlateTranslations
            (plateEquiv (P, d)) =
          TranslationalTilings.translateSet
            ((d * (R : ℤ)) • horizontalDiscreteUnit)
            (Tiling.RationalPolygonal.quakePlateTranslations P) ∧
          (IsDiscreteVerticalColumn (plateEquiv (P, d)) ↔
            IsDiscreteVerticalColumn P) :=
  periodizeFiniteBand_verticalPlates_general hF hTile hR hCopies

theorem exists_bandSpacing
    (B : Finset ℤ) (hB : B.Nonempty) :
      ∃ R : ℕ, 0 < R ∧
        ∀ p : ℤ × ℤ, p.1 ≠ p.2 →
          Disjoint
            (TranslationalTilings.translateSet
              ((p.1 * (R : ℤ)) • horizontalDiscreteUnit)
              (verticalDiscreteCylinder (B : Set ℤ)))
            (TranslationalTilings.translateSet
              ((p.2 * (R : ℤ)) • horizontalDiscreteUnit)
              (verticalDiscreteCylinder (B : Set ℤ))) := by
  classical
  let R : ℕ := Int.natAbs (B.max' hB - B.min' hB) + 1
  refine ⟨R, by omega, ?_⟩
  rintro ⟨d, e⟩ hde
  rw [Set.disjoint_left]
  intro z hzd hze
  have hdB := (mem_verticalDiscreteCylinder_iff
    (z - (d * (R : ℤ)) • horizontalDiscreteUnit) (B : Set ℤ)).mp hzd
  have heB := (mem_verticalDiscreteCylinder_iff
    (z - (e * (R : ℤ)) • horizontalDiscreteUnit) (B : Set ℤ)).mp hze
  have hcoordd : firstDiscreteCoordinate z - d * (R : ℤ) ∈ (B : Set ℤ) := by
    simpa [firstDiscreteCoordinate, horizontalDiscreteUnit, Matrix.vecHead, Matrix.vecTail]
      using hdB
  have hcoorde : firstDiscreteCoordinate z - e * (R : ℤ) ∈ (B : Set ℤ) := by
    simpa [firstDiscreteCoordinate, horizontalDiscreteUnit, Matrix.vecHead, Matrix.vecTail]
      using heB
  have hdmin := B.min'_le _ hcoordd
  have hdmax := B.le_max' _ hcoordd
  have hemin := B.min'_le _ hcoorde
  have hemax := B.le_max' _ hcoorde
  have hR : (R : ℤ) = B.max' hB - B.min' hB + 1 := by
    have hnonneg : 0 ≤ B.max' hB - B.min' hB :=
      sub_nonneg.mpr (B.min'_le (B.max' hB) (B.max'_mem hB))
    simp [R, Int.natAbs_of_nonneg hnonneg]
  have hgap : |d - e| * (R : ℤ) ≤ B.max' hB - B.min' hB := by
    have hdiff : (d - e) * (R : ℤ) =
        (firstDiscreteCoordinate z - e * (R : ℤ)) -
          (firstDiscreteCoordinate z - d * (R : ℤ)) := by ring
    have habs : |(firstDiscreteCoordinate z - e * (R : ℤ)) -
          (firstDiscreteCoordinate z - d * (R : ℤ))| ≤
        B.max' hB - B.min' hB := by
      rw [abs_le]
      constructor <;> omega
    calc
      |d - e| * (R : ℤ) = |(d - e) * (R : ℤ)| := by
        rw [abs_mul, abs_of_nonneg (Int.natCast_nonneg R)]
      _ = |(firstDiscreteCoordinate z - e * (R : ℤ)) -
          (firstDiscreteCoordinate z - d * (R : ℤ))| := by rw [hdiff]
      _ ≤ _ := habs
  have hdeabs : 1 ≤ |d - e| := by
    apply Int.one_le_abs
    omega
  have habsnonneg : 0 ≤ |d - e| := abs_nonneg _
  have hRnonneg : 0 ≤ (R : ℤ) := Int.natCast_nonneg R
  nlinarith

theorem discreteCarrier_subset_target
    {F : Finset TranslationalTilings.Plane} {A E : Set TranslationalTilings.Plane}
    (hTile : TranslationalTilings.Tiles F A E) :
    Tiling.RationalPolygonal.discreteCarrier F A ⊆ E := by
  classical
  rintro x ⟨f, hf, a, ha, rfl⟩
  by_contra hnot
  have hc := (TranslationalTilings.tilesAtLevel_iff_representation_count F A E 1).mp
    hTile (f + a)
  have hz : (F.filter fun g => f + a - g ∈ A).card = 0 := by
    simpa [hnot] using hc
  have hm : f ∈ F.filter fun g => f + a - g ∈ A := by
    simp [hf, ha]
  rw [Finset.card_eq_zero.mp hz] at hm
  simp at hm

private theorem centre_eq_of_eq_representations
    {F : Finset TranslationalTilings.Plane}
    {A E : Set TranslationalTilings.Plane}
    (hTile : TranslationalTilings.Tiles F A E)
    {f g a b : TranslationalTilings.Plane}
    (hf : f ∈ F) (ha : a ∈ A) (hg : g ∈ F) (hb : b ∈ A)
    (heq : f + a = g + b) : a = b := by
  classical
  have htarget := discreteCarrier_subset_target hTile ⟨f, hf, a, ha, rfl⟩
  have hc := (TranslationalTilings.tilesAtLevel_iff_representation_count F A E 1).mp
    hTile (f + a)
  have hcard : (F.filter fun q => f + a - q ∈ A).card = 1 := by
    simpa [htarget] using hc
  obtain ⟨q, hq⟩ := Finset.card_eq_one.mp hcard
  have hfm : f ∈ F.filter fun q => f + a - q ∈ A := by simp [hf, ha]
  have hgm : g ∈ F.filter fun q => f + a - q ∈ A := by
    simp only [Finset.mem_filter, hg, true_and]
    rw [heq]
    simpa using hb
  rw [hq] at hfm hgm
  have hfq : f = q := by simpa using hfm
  have hgq : g = q := by simpa using hgm
  have hfg : f = g := hfq.trans hgq.symm
  rw [hfg] at heq
  exact add_left_cancel heq

private theorem plateCarriers_disjoint
    {F : Finset TranslationalTilings.Plane} {A E : Set TranslationalTilings.Plane}
    (hTile : TranslationalTilings.Tiles F A E)
    {P Q : Tiling.RationalPolygonal.QuakePlate F A verticalDiscreteUnit}
    (hPQ : P ≠ Q) :
    Disjoint
      (Tiling.RationalPolygonal.discreteCarrier F
        (Tiling.RationalPolygonal.quakePlateTranslations P))
      (Tiling.RationalPolygonal.discreteCarrier F
        (Tiling.RationalPolygonal.quakePlateTranslations Q)) := by
  rw [Set.disjoint_left]
  rintro x ⟨f, hf, a, haP, hxfa⟩ ⟨g, hg, b, hbQ, hxgb⟩
  have hab : a = b := centre_eq_of_eq_representations hTile hf haP.1 hg hbQ.1
    (hxfa.symm.trans hxgb)
  exact hPQ (haP.2.symm.trans (hab ▸ hbQ.2))

/-- Every plate in a finite vertical band is a complete vertical column. -/
theorem finiteBand_allVerticalColumns_of_nonempty
    {B : Finset ℤ} {F : Finset TranslationalTilings.Plane}
    {A : Set TranslationalTilings.Plane}
    (hF : F.Nonempty)
    (hB : B.Nonempty)
    (hTile : TranslationalTilings.Tiles F A
      (verticalDiscreteCylinder (B : Set ℤ))) :
    (∀ P : Tiling.RationalPolygonal.QuakePlate F A verticalDiscreteUnit,
      IsDiscreteVerticalColumn P) ∧ A = discreteColumnUnion F A := by
  classical
  let f0 := Classical.choose hF
  have hf0 : f0 ∈ F := Classical.choose_spec hF
  obtain ⟨R, hR, hCopies⟩ := exists_bandSpacing B hB
  let A' : Set TranslationalTilings.Plane :=
    ⋃ d : ℤ, TranslationalTilings.translateSet
      ((d * (R : ℤ)) • horizontalDiscreteUnit) A
  let E' : Set TranslationalTilings.Plane :=
    ⋃ d : ℤ, TranslationalTilings.translateSet
      ((d * (R : ℤ)) • horizontalDiscreteUnit)
      (verticalDiscreteCylinder (B : Set ℤ))
  have hperiodized := periodizeFiniteBand_tiles_general hTile hR hCopies
  have hTile' : TranslationalTilings.Tiles F A' E' := hperiodized.1
  have hVert : Tiling.RationalPolygonal.DiscretePeriodicBy E' verticalDiscreteUnit :=
    hperiodized.2.1
  have hScalar : TranslationalTilings.SetScalarPeriodic R E' := hperiodized.2.2
  obtain ⟨plateEquiv, hplate⟩ :=
    periodizeFiniteBand_verticalPlates_general hF hTile hR hCopies
  have hall : ∀ P : Tiling.RationalPolygonal.QuakePlate F A verticalDiscreteUnit,
      IsDiscreteVerticalColumn P := by
    intro P
    by_contra hnon
    let Q := plateEquiv (P, (0 : ℤ))
    have hQnon : ¬ IsDiscreteVerticalColumn Q := by
      exact fun h => hnon ((hplate P 0).2.mp h)
    obtain ⟨L, hL, _hRL, hperiod, _⟩ :=
      exists_discretePlatePeriodicity hF hR hVert hScalar hTile'
    have hQP : Tiling.RationalPolygonal.quakePlateTranslations Q =
        Tiling.RationalPolygonal.quakePlateTranslations P := by
      rw [(hplate P 0).1]
      ext z
      change z - ((0 : ℤ) * (R : ℤ)) • horizontalDiscreteUnit ∈
          Tiling.RationalPolygonal.quakePlateTranslations P ↔ _
      simp
    obtain ⟨t, htP⟩ :
        (Tiling.RationalPolygonal.quakePlateTranslations P).Nonempty := by
      refine P.ind ?_
      intro a
      exact ⟨a, Tiling.RationalPolygonal.mem_quakePlateTranslations_mk a⟩
    let x : TranslationalTilings.Plane := f0 + t
    have hxcarrier : x ∈ Tiling.RationalPolygonal.discreteCarrier F
        (Tiling.RationalPolygonal.quakePlateTranslations Q) := by
      exact ⟨f0, hf0, t, hQP ▸ htP, rfl⟩
    let n : ℕ := Int.natAbs (B.max' hB - firstDiscreteCoordinate x) + 1
    let w : TranslationalTilings.Plane := (n : ℤ) • horizontalDiscreteUnit
    have hxshift : x + (L : ℤ) • w ∈
        Tiling.RationalPolygonal.discreteCarrier F
          (Tiling.RationalPolygonal.quakePlateTranslations Q) :=
      (hperiod Q hQnon x w).2 hxcarrier
    have hxbaseCarrier : x + (L : ℤ) • w ∈
        Tiling.RationalPolygonal.discreteCarrier F A := by
      rcases hxshift with ⟨f, hf, a, ha, heq⟩
      exact ⟨f, hf, a, (hQP ▸ ha).1, heq⟩
    have hxband := discreteCarrier_subset_target hTile hxbaseCarrier
    have hxcoord := (mem_verticalDiscreteCylinder_iff
      (x + (L : ℤ) • w) (B : Set ℤ)).mp hxband
    have hxle := B.le_max' _ hxcoord
    have hdiffnonneg : 0 ≤ |B.max' hB - firstDiscreteCoordinate x| := abs_nonneg _
    have hn : (n : ℤ) = |B.max' hB - firstDiscreteCoordinate x| + 1 := by
      simp [n]
    have hLabs : 1 ≤ (L : ℤ) := by exact_mod_cast hL
    have hcoordEq : firstDiscreteCoordinate (x + (L : ℤ) • w) =
        firstDiscreteCoordinate x + (L : ℤ) * (n : ℤ) := by
      simp [w, firstDiscreteCoordinate]
    have hxle' : firstDiscreteCoordinate x + (L : ℤ) * (n : ℤ) ≤ B.max' hB :=
      hcoordEq ▸ hxle
    have habsbound : B.max' hB - firstDiscreteCoordinate x ≤
        |B.max' hB - firstDiscreteCoordinate x| := le_abs_self _
    nlinarith
  refine ⟨hall, ?_⟩
  calc
    A = ⋃ P : Tiling.RationalPolygonal.QuakePlate F A verticalDiscreteUnit,
        Tiling.RationalPolygonal.quakePlateTranslations P :=
      (iUnion_verticalPlateCentres F A).symm
    _ = discreteColumnUnion F A := by
      simp [discreteColumnUnion, hall]

theorem finiteBand_allVerticalColumns_general
    {B : Finset ℤ} {F : Finset TranslationalTilings.Plane}
    {A : Set TranslationalTilings.Plane}
    (hF : F.Nonempty)
    (hTile : TranslationalTilings.Tiles F A
      (verticalDiscreteCylinder (B : Set ℤ))) :
    (∀ P : Tiling.RationalPolygonal.QuakePlate F A verticalDiscreteUnit,
      IsDiscreteVerticalColumn P) ∧ A = discreteColumnUnion F A := by
  classical
  by_cases hB : B.Nonempty
  · exact finiteBand_allVerticalColumns_of_nonempty hF hB hTile
  · have hA : A = ∅ := by
      ext a
      constructor
      · intro ha
        let f0 := Classical.choose hF
        have hf0 : f0 ∈ F := Classical.choose_spec hF
        have hx : f0 + a ∈ Tiling.RationalPolygonal.discreteCarrier F A :=
          ⟨f0, hf0, a, ha, rfl⟩
        have hxTarget := discreteCarrier_subset_target hTile hx
        exact (hB ⟨firstDiscreteCoordinate (f0 + a),
          (mem_verticalDiscreteCylinder_iff (f0 + a) (B : Set ℤ)).mp hxTarget⟩).elim
      · simp
    constructor
    · intro P
      obtain ⟨a, _ha⟩ := P.nonempty_supp
      have : False := by
        have ha := a.property
        have he := congrArg (fun S : Set TranslationalTilings.Plane => a.val ∈ S) hA
        exact he.mp ha
      exact this.elim
    · rw [hA]
      simp [discreteColumnUnion]

theorem finiteBand_allVerticalColumns
    {B : Finset ℤ} {F : Finset TranslationalTilings.Plane}
    {A : Set TranslationalTilings.Plane}
    (hF : F.Nonempty)
    (_hFB : (F : Set TranslationalTilings.Plane) ⊆
      verticalDiscreteCylinder (B : Set ℤ))
    (hTile : TranslationalTilings.Tiles F A
      (verticalDiscreteCylinder (B : Set ℤ))) :
    (∀ P : Tiling.RationalPolygonal.QuakePlate F A verticalDiscreteUnit,
      IsDiscreteVerticalColumn P) ∧ A = discreteColumnUnion F A :=
  finiteBand_allVerticalColumns_general hF hTile

/-- Projecting complete columns gives an exact finite tiling of the horizontal band base. -/
theorem finiteBand_projectedTiling
    {B : Finset ℤ} {F : Finset TranslationalTilings.Plane}
    {A : Set TranslationalTilings.Plane}
    (hF : F.Nonempty)
    (hFB : (F : Set TranslationalTilings.Plane) ⊆
      verticalDiscreteCylinder (B : Set ℤ))
    (hTile : TranslationalTilings.Tiles F A
      (verticalDiscreteCylinder (B : Set ℤ))) :
    ∃ C : Finset ℤ,
      TranslationalTilings.Tiles
        (F.image firstDiscreteCoordinate) (C : Set ℤ) (B : Set ℤ) := by
  classical
  have hall := (finiteBand_allVerticalColumns hF hFB hTile).1
  let axis : Tiling.RationalPolygonal.QuakePlate F A verticalDiscreteUnit → ℤ :=
    fun P => Classical.choose (hall P)
  have haxis : ∀ P, firstDiscreteCoordinate ''
      Tiling.RationalPolygonal.quakePlateTranslations P = {axis P} :=
    fun P => Classical.choose_spec (hall P)
  let Cset : Set ℤ := Set.range axis
  let f0 := Classical.choose hF
  have hf0 : f0 ∈ F := Classical.choose_spec hF
  have hCfinite : Cset.Finite := by
    apply Set.Finite.subset (B.image fun b => b - firstDiscreteCoordinate f0).finite_toSet
    rintro c ⟨P, rfl⟩
    obtain ⟨t, ht⟩ :
        (Tiling.RationalPolygonal.quakePlateTranslations P).Nonempty := by
      refine P.ind ?_
      intro a
      exact ⟨a, Tiling.RationalPolygonal.mem_quakePlateTranslations_mk a⟩
    have htc : firstDiscreteCoordinate t = axis P := by
      have : firstDiscreteCoordinate t ∈ ({axis P} : Set ℤ) := haxis P ▸ ⟨t, ht, rfl⟩
      simpa using this
    have hcar : f0 + t ∈ Tiling.RationalPolygonal.discreteCarrier F A :=
      ⟨f0, hf0, t, ht.1, rfl⟩
    have hband := discreteCarrier_subset_target hTile hcar
    have hb := (mem_verticalDiscreteCylinder_iff (f0 + t) (B : Set ℤ)).mp hband
    apply Finset.mem_coe.mpr
    refine Finset.mem_image.mpr ⟨firstDiscreteCoordinate (f0 + t), hb, ?_⟩
    simpa [firstDiscreteCoordinate] using htc
  let C : Finset ℤ := hCfinite.toFinset
  refine ⟨C, tiles_of_existsUnique_on_target ?_ ?_⟩
  · intro x hxB
    let z : TranslationalTilings.Plane := ![x, 0]
    have hzB : z ∈ verticalDiscreteCylinder (B : Set ℤ) := by
      apply (mem_verticalDiscreteCylinder_iff z (B : Set ℤ)).mpr
      simpa [z, firstDiscreteCoordinate]
    have hc := (TranslationalTilings.tilesAtLevel_iff_representation_count F A
      (verticalDiscreteCylinder (B : Set ℤ)) 1).mp hTile z
    have hcard : (F.filter fun f => z - f ∈ A).card = 1 := by simpa [hzB] using hc
    obtain ⟨f, hfilter⟩ := Finset.card_eq_one.mp hcard
    have hfA : f ∈ F ∧ z - f ∈ A := by
      have : f ∈ F.filter fun g => z - g ∈ A := by simp [hfilter]
      simpa using this
    have haUnion : z - f ∈ ⋃ P : Tiling.RationalPolygonal.QuakePlate F A
        verticalDiscreteUnit, Tiling.RationalPolygonal.quakePlateTranslations P := by
      rw [iUnion_verticalPlateCentres F A]
      exact hfA.2
    obtain ⟨P, haP⟩ := Set.mem_iUnion.mp haUnion
    have hac : firstDiscreteCoordinate (z - f) = axis P := by
      have : firstDiscreteCoordinate (z - f) ∈ ({axis P} : Set ℤ) :=
        haxis P ▸ ⟨z - f, haP, rfl⟩
      simpa using this
    refine ⟨firstDiscreteCoordinate f, ⟨Finset.mem_image.mpr ⟨f, hfA.1, rfl⟩, ?_⟩, ?_⟩
    · change x - firstDiscreteCoordinate f ∈ (C : Set ℤ)
      have heq : x - firstDiscreteCoordinate f = axis P := by
        simpa [z, firstDiscreteCoordinate] using hac
      rw [heq]
      exact hCfinite.mem_toFinset.mpr ⟨P, rfl⟩
    · intro u hu
      obtain ⟨g, hgF, rfl⟩ := Finset.mem_image.mp hu.1
      have haxisQ : x - firstDiscreteCoordinate g ∈ Cset := by
        exact hCfinite.mem_toFinset.mp hu.2
      obtain ⟨Q, hQeq⟩ := haxisQ
      have hsumP : x ∈ integerSumset
          (firstDiscreteCoordinate '' (F : Set TranslationalTilings.Plane))
          (firstDiscreteCoordinate '' Tiling.RationalPolygonal.quakePlateTranslations P) := by
        refine ⟨firstDiscreteCoordinate f, ⟨f, hfA.1, rfl⟩,
          axis P, ?_, ?_⟩
        · rw [haxis P]
          exact Set.mem_singleton _
        · rw [← hac]
          simp [z, firstDiscreteCoordinate]
      have hsumQ : x ∈ integerSumset
          (firstDiscreteCoordinate '' (F : Set TranslationalTilings.Plane))
          (firstDiscreteCoordinate '' Tiling.RationalPolygonal.quakePlateTranslations Q) := by
        refine ⟨firstDiscreteCoordinate g, ⟨g, hgF, rfl⟩, axis Q, ?_, ?_⟩
        · rw [haxis Q]
          exact Set.mem_singleton _
        · calc
            firstDiscreteCoordinate g + axis Q = axis Q + firstDiscreteCoordinate g :=
              add_comm _ _
            _ = x := (sub_eq_iff_eq_add.mp hQeq.symm).symm
      have hVert : Tiling.RationalPolygonal.DiscretePeriodicBy
          (verticalDiscreteCylinder (B : Set ℤ)) verticalDiscreteUnit := by
        intro q
        rw [mem_verticalDiscreteCylinder_iff, mem_verticalDiscreteCylinder_iff]
        simp [firstDiscreteCoordinate, verticalDiscreteUnit]
      have hzP : z ∈ Tiling.RationalPolygonal.discreteCarrier F
          (Tiling.RationalPolygonal.quakePlateTranslations P) := by
        rw [verticalPlateCarrier_eq_projectionProduct hF hTile hVert P,
          mem_verticalDiscreteCylinder_iff]
        simpa [z, firstDiscreteCoordinate] using hsumP
      have hzQ : z ∈ Tiling.RationalPolygonal.discreteCarrier F
          (Tiling.RationalPolygonal.quakePlateTranslations Q) := by
        rw [verticalPlateCarrier_eq_projectionProduct hF hTile hVert Q,
          mem_verticalDiscreteCylinder_iff]
        simpa [z, firstDiscreteCoordinate] using hsumQ
      have hPQ : P = Q := by
        by_contra hne
        exact (Set.disjoint_left.mp
          (plateCarriers_disjoint hTile hne)) hzP hzQ
      subst Q
      have hfaxis : x - firstDiscreteCoordinate f = axis P := by
        simpa [z, firstDiscreteCoordinate] using hac
      omega
  · intro x hxB u huF huC
    obtain ⟨f, hfF, rfl⟩ := Finset.mem_image.mp huF
    have hcset : x - firstDiscreteCoordinate f ∈ Cset := hCfinite.mem_toFinset.mp huC
    obtain ⟨P, hPeq⟩ := hcset
    let z : TranslationalTilings.Plane := ![x, 0]
    have hsum : x ∈ integerSumset
        (firstDiscreteCoordinate '' (F : Set TranslationalTilings.Plane))
        (firstDiscreteCoordinate '' Tiling.RationalPolygonal.quakePlateTranslations P) := by
      refine ⟨firstDiscreteCoordinate f, ⟨f, hfF, rfl⟩, axis P, ?_, ?_⟩
      · rw [haxis P]
        exact Set.mem_singleton _
      · calc
          firstDiscreteCoordinate f + axis P = axis P + firstDiscreteCoordinate f :=
            add_comm _ _
          _ = x := (sub_eq_iff_eq_add.mp hPeq.symm).symm
    have hVert : Tiling.RationalPolygonal.DiscretePeriodicBy
        (verticalDiscreteCylinder (B : Set ℤ)) verticalDiscreteUnit := by
      intro q
      rw [mem_verticalDiscreteCylinder_iff, mem_verticalDiscreteCylinder_iff]
      simp [firstDiscreteCoordinate, verticalDiscreteUnit]
    have hzcar : z ∈ Tiling.RationalPolygonal.discreteCarrier F
        (Tiling.RationalPolygonal.quakePlateTranslations P) := by
      rw [verticalPlateCarrier_eq_projectionProduct hF hTile hVert P,
        mem_verticalDiscreteCylinder_iff]
      simpa [z, firstDiscreteCoordinate] using hsum
    have hzA : z ∈ Tiling.RationalPolygonal.discreteCarrier F A := by
      rcases hzcar with ⟨g, hg, a, ha, heq⟩
      exact ⟨g, hg, a, ha.1, heq⟩
    have hzband := discreteCarrier_subset_target hTile hzA
    apply hxB
    have := (mem_verticalDiscreteCylinder_iff z (B : Set ℤ)).mp hzband
    simpa [z, firstDiscreteCoordinate] using this

end Tiling.AxisParallel.Discrete
