import Tiling.RationalPolygonal.Basic

set_option linter.style.header false

/-!
# Exact discrete tile carriers

This module is the low-level bridge between the finite-convolution definition of an exact
discrete tiling and its unique pointwise tile representation.  It is shared by the raster and
earthquake layers, so neither foundational rasterization nor the discrete carrier API depends on
the higher weak-periodicity argument.
-/

open Set
open TranslationalTilings

namespace Tiling.RationalPolygonal

universe u

variable {G : Type u} [AddCommGroup G]

/-- The set covered by translating a finite discrete tile along `T`. -/
def discreteCarrier (F : Finset G) (T : Set G) : Set G :=
  {x | ∃ f ∈ F, ∃ t ∈ T, x = f + t}

@[simp]
theorem mem_discreteCarrier_iff {F : Finset G} {T : Set G} {x : G} :
    x ∈ discreteCarrier F T ↔ ∃ f ∈ F, ∃ t ∈ T, x = f + t :=
  Iff.rfl

/-- The convolution of a subfamily of an exact tiling is the indicator of its discrete carrier. -/
theorem tileConv_indicator_eq_indicator_discreteCarrier
    {F : Finset G}
    {A E B : Set G}
    (hTile : Tiles F A E) (hBA : B ⊆ A) :
    tileConv F (setIndicator B) =
      setIndicator
        (discreteCarrier F B) := by
  classical
  funext x
  rw [tileConv_indicator_eq_card]
  by_cases hx : x ∈ discreteCarrier F B
  · have hxCarrier := hx
    obtain ⟨f, hfF, b, hbB, hxfb⟩ := hx
    have hfb : x - f ∈ B := by
      rw [hxfb]
      simpa only [add_sub_cancel_left] using hbB
    have hfilterNonempty :
        (F.filter fun q ↦ x - q ∈ B).Nonempty :=
      ⟨f, Finset.mem_filter.mpr ⟨hfF, hfb⟩⟩
    have hfilterMono :
        F.filter (fun q ↦ x - q ∈ B) ⊆
          F.filter (fun q ↦ x - q ∈ A) := by
      intro q hq
      exact Finset.mem_filter.mpr
        ⟨(Finset.mem_filter.mp hq).1, hBA (Finset.mem_filter.mp hq).2⟩
    have hcardA : (F.filter fun q ↦ x - q ∈ A).card ≤ 1 := by
      have ht := hTile x
      rw [tileConv_indicator_eq_card] at ht
      have ht' : ((F.filter fun q ↦ x - q ∈ A).card : ℤ) =
          setIndicator E x := by
        simpa only [Nat.cast_one, one_mul] using ht
      by_cases hxE : x ∈ E
      · have hindicator : setIndicator E x = 1 := by
          simp [setIndicator, hxE]
        rw [hindicator] at ht'
        omega
      · have hindicator : setIndicator E x = 0 := by
          simp [setIndicator, hxE]
        rw [hindicator] at ht'
        omega
    have hcardB_le : (F.filter fun q ↦ x - q ∈ B).card ≤ 1 :=
      (Finset.card_le_card hfilterMono).trans hcardA
    have hcardB_pos : 0 < (F.filter fun q ↦ x - q ∈ B).card :=
      Finset.card_pos.mpr hfilterNonempty
    have hcardB : (F.filter fun q ↦ x - q ∈ B).card = 1 := by omega
    rw [hcardB]
    simp [setIndicator, hxCarrier]
  · have hfilterEmpty : F.filter (fun q ↦ x - q ∈ B) = ∅ := by
      apply Finset.not_nonempty_iff_eq_empty.mp
      intro hnonempty
      obtain ⟨f, hf⟩ := hnonempty
      apply hx
      have hdata := Finset.mem_filter.mp hf
      exact ⟨f, hdata.1, x - f, hdata.2, by abel⟩
    rw [hfilterEmpty]
    simp [setIndicator, hx]

/-- Exact discrete tiling gives a unique tile element, and hence a unique translation, at every
ambient point. -/
theorem existsUnique_tile_representation {F : Finset G} {T : Set G}
    (hT : TilesUniverse F T) (x : G) :
    ∃! f : G, f ∈ F ∧ x - f ∈ T := by
  classical
  have hcard : (F.filter fun f ↦ x - f ∈ T).card = 1 := by
    have hcount :=
      (tilesAtLevel_iff_representation_count F T Set.univ 1).mp hT x
    simpa using hcount
  obtain ⟨f, hf⟩ := Finset.card_eq_one.mp hcard
  refine ⟨f, ?_, ?_⟩
  · have : f ∈ F.filter fun g ↦ x - g ∈ T := by simp [hf]
    simpa using this
  · intro g hg
    have hgm : g ∈ F.filter fun f ↦ x - f ∈ T := by simpa using hg
    simpa [hf] using hgm

/-- A unique tile-element representation at every point is exactly a level-one tiling of the
ambient group. -/
theorem tilesUniverse_of_existsUnique {F : Finset G} {T : Set G}
    (hrep : ∀ x : G, ∃! f : G, f ∈ F ∧ x - f ∈ T) :
    TilesUniverse F T := by
  classical
  apply (tilesAtLevel_iff_representation_count F T Set.univ 1).mpr
  intro x
  obtain ⟨f, hf, hunique⟩ := hrep x
  have hfilter : (F.filter fun g ↦ x - g ∈ T) = {f} := by
    ext g
    constructor
    · intro hg
      have hg' : g ∈ F ∧ x - g ∈ T := by simpa using hg
      simpa only [Finset.mem_singleton] using hunique g hg'
    · intro hg
      have hgf : g = f := by simpa only [Finset.mem_singleton] using hg
      subst g
      simpa using hf
  rw [hfilter]
  simp

/-- Translate a finite additive tile by subtracting one group element. -/
noncomputable def shiftFinset (q : G) (F : Finset G) : Finset G := by
  classical
  exact F.image fun f ↦ f - q

@[simp]
theorem mem_shiftFinset_iff {q z : G} {F : Finset G} :
    z ∈ shiftFinset q F ↔ z + q ∈ F := by
  classical
  constructor
  · intro hz
    rw [shiftFinset, Finset.mem_image] at hz
    obtain ⟨f, hf, hfz⟩ := hz
    rw [← hfz]
    simpa only [sub_add_cancel] using hf
  · intro hz
    rw [shiftFinset, Finset.mem_image]
    exact ⟨z + q, hz, by simp only [add_sub_cancel_right]⟩

/-- Translating the finite tile does not change whether a fixed translation set tiles the whole
ambient group. -/
theorem tilesUniverse_shiftFinset_iff (q : G) (F : Finset G) (T : Set G) :
    TilesUniverse (shiftFinset q F) T ↔ TilesUniverse F T := by
  constructor
  · intro hshift
    apply tilesUniverse_of_existsUnique
    intro x
    obtain ⟨g, hg, hgunique⟩ :=
      existsUnique_tile_representation hshift (x - q)
    let f := g + q
    refine ⟨f, ?_, ?_⟩
    · constructor
      · exact mem_shiftFinset_iff.mp hg.1
      · dsimp only [f]
        convert hg.2 using 1
        abel
    · intro f' hf'
      have hcandidate : f' - q ∈ shiftFinset q F ∧
          x - q - (f' - q) ∈ T := by
        constructor
        · exact mem_shiftFinset_iff.mpr (by simpa only [sub_add_cancel] using hf'.1)
        · convert hf'.2 using 1
          abel
      have heq := hgunique (f' - q) hcandidate
      dsimp only [f]
      rw [← heq]
      abel
  · intro hF
    apply tilesUniverse_of_existsUnique
    intro x
    obtain ⟨f, hf, hfunique⟩ :=
      existsUnique_tile_representation hF (x + q)
    let g := f - q
    refine ⟨g, ?_, ?_⟩
    · constructor
      · exact mem_shiftFinset_iff.mpr (by simpa only [g, sub_add_cancel] using hf.1)
      · dsimp only [g]
        convert hf.2 using 1
        abel
    · intro g' hg'
      have hcandidate : g' + q ∈ F ∧
          x + q - (g' + q) ∈ T := by
        constructor
        · exact mem_shiftFinset_iff.mp hg'.1
        · convert hg'.2 using 1
          abel
      have heq := hfunique (g' + q) hcandidate
      dsimp only [g]
      rw [← heq]
      abel

/-- Two representations of a point in an exact discrete tiling use the same translation vector. -/
theorem translation_eq_of_eq_representations {F : Finset G} {T : Set G}
    (hT : TilesUniverse F T) {f g t s : G}
    (hf : f ∈ F) (ht : t ∈ T) (hg : g ∈ F) (hs : s ∈ T)
    (heq : f + t = g + s) : t = s := by
  obtain ⟨chosen, hchosen, hunique⟩ := existsUnique_tile_representation hT (f + t)
  have hfrep : f ∈ F ∧ f + t - f ∈ T := by
    refine ⟨hf, ?_⟩
    simpa only [add_sub_cancel_left] using ht
  have hgrep : g ∈ F ∧ f + t - g ∈ T := by
    refine ⟨hg, ?_⟩
    rw [heq]
    simpa only [add_sub_cancel_left] using hs
  have hfg : f = g := (hunique f hfrep).trans (hunique g hgrep).symm
  rw [hfg] at heq
  exact add_left_cancel heq

/-- Discrete membership invariance under one specified period. -/
def DiscretePeriodicBy (A : Set G) (v : G) : Prop :=
  ∀ x, x + v ∈ A ↔ x ∈ A

/-- Integer multiples of a discrete period remain periods. -/
theorem DiscretePeriodicBy.zsmul {A : Set G} {v : G}
    (hA : DiscretePeriodicBy A v) (n : ℤ) :
    DiscretePeriodicBy A (n • v) := by
  have hperiodic : Function.Periodic (fun x ↦ x ∈ A) v :=
    fun x ↦ propext (hA x)
  exact fun x ↦ eq_iff_iff.mp (hperiodic.zsmul n x)

/-- A one-step transfer between tile placements after translating a represented point by `v`. -/
def quakeTransfer (F : Finset G) (T : Set G) (v : G) (t t' : T) : Prop :=
  ∃ f ∈ F, ∃ f' ∈ F, f + (t : G) + v = f' + (t' : G)

end Tiling.RationalPolygonal
