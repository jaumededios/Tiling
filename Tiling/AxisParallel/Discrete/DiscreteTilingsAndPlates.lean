import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Logic.Denumerable
import Tiling.AxisParallel.Discrete.Core

/-!
# Exact discrete tilings and canonical vertical earthquake plates

The public plate type is the existing connected-component type
`Tiling.RationalPolygonal.QuakePlate`.  This module supplies target-relative versions of the
carrier and minimality lemmas, together with exact set identities used downstream.
-/

open Set
open TranslationalTilings
open scoped Pointwise

namespace Tiling.AxisParallel.Discrete

/- The code of a rooted parent tree is chosen recursively so that a parent's code is always
strictly smaller than its child's.  Pairing with the ambient `Encodable` code keeps it injective,
even when a level of the tree is infinite. -/
private noncomputable def rootedCode
    {α : Type*} [Encodable α] [DecidableEq α]
    (root : α) (parent : α → α) (height : α → ℕ)
    (hparent : ∀ x, x ≠ root → height (parent x) < height x)
    (x : α) : ℕ :=
  if hx : x = root then 0
  else Nat.pair (rootedCode root parent height hparent (parent x))
    (Encodable.encode x) + 1
termination_by height x
decreasing_by exact hparent x (by simpa using hx)

private theorem rootedCode_root
    {α : Type*} [Encodable α] [DecidableEq α]
    (root : α) (parent : α → α) (height : α → ℕ)
    (hparent : ∀ x, x ≠ root → height (parent x) < height x) :
    rootedCode root parent height hparent root = 0 := by
  rw [rootedCode]
  simp

private theorem rootedCode_of_ne
    {α : Type*} [Encodable α] [DecidableEq α]
    (root : α) (parent : α → α) (height : α → ℕ)
    (hparent : ∀ x, x ≠ root → height (parent x) < height x)
    {x : α} (hx : x ≠ root) :
    rootedCode root parent height hparent x =
      Nat.pair (rootedCode root parent height hparent (parent x))
        (Encodable.encode x) + 1 := by
  rw [rootedCode]
  simp [hx]

private theorem rootedCode_parent_lt
    {α : Type*} [Encodable α] [DecidableEq α]
    (root : α) (parent : α → α) (height : α → ℕ)
    (hparent : ∀ x, x ≠ root → height (parent x) < height x)
    {x : α} (hx : x ≠ root) :
    rootedCode root parent height hparent (parent x) <
      rootedCode root parent height hparent x := by
  rw [rootedCode_of_ne root parent height hparent hx]
  exact Nat.lt_succ_of_le (Nat.left_le_pair _ _)

private theorem rootedCode_injective
    {α : Type*} [Encodable α] [DecidableEq α]
    (root : α) (parent : α → α) (height : α → ℕ)
    (hparent : ∀ x, x ≠ root → height (parent x) < height x) :
    Function.Injective (rootedCode root parent height hparent) := by
  intro x y hxy
  by_cases hx : x = root
  · subst x
    by_cases hy : y = root
    · exact hy.symm
    · rw [rootedCode_root, rootedCode_of_ne root parent height hparent hy] at hxy
      omega
  · by_cases hy : y = root
    · subst y
      rw [rootedCode_of_ne root parent height hparent hx, rootedCode_root] at hxy
      omega
    · rw [rootedCode_of_ne root parent height hparent hx,
        rootedCode_of_ne root parent height hparent hy] at hxy
      have hp := Nat.pair_eq_pair.mp (Nat.add_right_cancel hxy)
      exact Encodable.encode_injective hp.2

/- Increasing enumeration of the range of `rootedCode` works for infinitely branching trees:
the construction never attempts to finish one graph-distance sphere before visiting the next. -/
private theorem exists_rootedEnumeration
    {α : Type*} [Countable α] [Infinite α]
    (root : α) (parent : α → α) (height : α → ℕ)
    (hparent : ∀ x, x ≠ root → height (parent x) < height x)
    (R : α → α → Prop)
    (hR : ∀ x, x ≠ root → R x (parent x)) :
    ∃ e : ℕ ≃ α, e 0 = root ∧
      ∀ n, 0 < n → ∃ m, m < n ∧ R (e n) (e m) := by
  classical
  let _ : Encodable α := Classical.choice (nonempty_encodable α)
  let code : α → ℕ := rootedCode root parent height hparent
  have hcode : Function.Injective code :=
    rootedCode_injective root parent height hparent
  have hcodeRoot : code root = 0 := rootedCode_root root parent height hparent
  let s : Set ℕ := Set.range code
  let toRange : α → s := fun x => ⟨code x, ⟨x, rfl⟩⟩
  have htoRange : Function.Injective toRange := by
    intro x y hxy
    apply hcode
    exact congrArg Subtype.val hxy
  let _ : Infinite s := Infinite.of_injective toRange htoRange
  let decodeCode : s → α := fun n => Classical.choose n.2
  have hdecodeCode (n : s) : code (decodeCode n) = n :=
    Classical.choose_spec n.2
  have hdecodeInj : Function.Injective decodeCode := by
    intro m n hmn
    apply Subtype.ext
    rw [← hdecodeCode m, ← hdecodeCode n, hmn]
  have hdecodeSurj : Function.Surjective decodeCode := by
    intro x
    let n : s := ⟨code x, ⟨x, rfl⟩⟩
    refine ⟨n, hcode ?_⟩
    exact hdecodeCode n
  let nthCode : ℕ → s := Nat.Subtype.ofNat s
  have hnthStrict : StrictMono nthCode := by
    apply strictMono_nat_of_lt_succ
    intro n
    exact Nat.Subtype.lt_succ_self (nthCode n)
  have hnthSurj : Function.Surjective nthCode := Nat.Subtype.ofNat_surjective
  let q : ℕ → α := fun n => decodeCode (nthCode n)
  have hqBij : Function.Bijective q :=
    ⟨hdecodeInj.comp hnthStrict.injective, hdecodeSurj.comp hnthSurj⟩
  let e : ℕ ≃ α := Equiv.ofBijective q hqBij
  have heZero : e 0 = root := by
    apply hcode
    change code (decodeCode (nthCode 0)) = code root
    rw [hdecodeCode, hcodeRoot]
    change ((Nat.Subtype.ofNat s 0 : s) : ℕ) = 0
    rw [Nat.Subtype.ofNat]
    apply Nat.le_zero.mp
    exact (show (⊥ : s) ≤ ⟨0, ⟨root, hcodeRoot⟩⟩ from bot_le)
  refine ⟨e, heZero, ?_⟩
  intro n hn
  have hne : e n ≠ root := by
    intro heq
    have : n = 0 := e.injective (heq.trans heZero.symm)
    omega
  have hparentRange : code (parent (e n)) ∈ s := ⟨parent (e n), rfl⟩
  obtain ⟨m, hm⟩ := hnthSurj ⟨code (parent (e n)), hparentRange⟩
  refine ⟨m, ?_, ?_⟩
  · apply hnthStrict.lt_iff_lt.mp
    rw [hm]
    change code (parent (e n)) < ((nthCode n : s) : ℕ)
    rw [← hdecodeCode (nthCode n)]
    exact rootedCode_parent_lt root parent height hparent hne
  · have heparent : e m = parent (e n) := by
      apply hcode
      change code (decodeCode (nthCode m)) =
        code (parent (decodeCode (nthCode n)))
      rw [hdecodeCode, hm]
      rfl
    rw [heparent]
    exact hR (e n) hne

theorem mem_verticalDiscreteFibre_iff
    (z : TranslationalTilings.Plane) (x : ℤ) :
    z ∈ verticalDiscreteFibre x ↔ firstDiscreteCoordinate z = x := by
  simp only [verticalDiscreteFibre, TranslationalTilings.addCoset,
    TranslationalTilings.directionSubgroup, Set.mem_ofPred_eq,
    AddSubgroup.mem_zmultiples_iff]
  constructor
  · rintro ⟨n, hn⟩
    have hcoord := congrFun hn 0
    change n * 0 = z 0 - x * 1 at hcoord
    change z 0 = x
    omega
  · intro hcoord
    change z 0 = x at hcoord
    refine ⟨z 1, ?_⟩
    funext i
    fin_cases i
    · change z 1 * 0 = z 0 - x * 1
      omega
    · change z 1 * 1 = z 1 - x * 0
      ring

theorem mem_verticalDiscreteCongruenceClass_iff
    (z : TranslationalTilings.Plane) (x : ℤ) (L : ℕ) :
    z ∈ verticalDiscreteCongruenceClass x L ↔
      ∃ n : ℤ, firstDiscreteCoordinate z = x + n * (L : ℤ) := by
  simp only [verticalDiscreteCongruenceClass, Set.mem_iUnion,
    mem_verticalDiscreteFibre_iff]

theorem mem_verticalDiscreteCylinder_iff
    (z : TranslationalTilings.Plane) (B : Set ℤ) :
    z ∈ verticalDiscreteCylinder B ↔ firstDiscreteCoordinate z ∈ B := by
  simp only [verticalDiscreteCylinder, Set.mem_iUnion,
    mem_verticalDiscreteFibre_iff]
  constructor
  · rintro ⟨x, hx⟩
    exact hx ▸ x.2
  · intro hz
    exact ⟨⟨firstDiscreteCoordinate z, hz⟩, rfl⟩

private theorem add_mem_target_of_tiles
    {G : Type*} [AddCommGroup G]
    {F : Finset G} {A E : Set G}
    (hTile : TranslationalTilings.Tiles F A E)
    {f a : G} (hf : f ∈ F) (ha : a ∈ A) : f + a ∈ E := by
  classical
  by_contra hnot
  have hcount :=
    (TranslationalTilings.tilesAtLevel_iff_representation_count F A E 1).mp hTile (f + a)
  have hzero : (F.filter fun g ↦ f + a - g ∈ A).card = 0 := by
    simpa [hnot] using hcount
  have hmem : f ∈ F.filter fun g ↦ f + a - g ∈ A := by
    simp only [Finset.mem_filter, hf, true_and]
    simpa only [add_sub_cancel_left] using ha
  rw [Finset.card_eq_zero.mp hzero] at hmem
  simp at hmem

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

private theorem translation_eq_of_eq_representations
    {G : Type*} [AddCommGroup G]
    {F : Finset G} {A E : Set G}
    (hTile : TranslationalTilings.Tiles F A E)
    {f g a b : G} (hf : f ∈ F) (ha : a ∈ A)
    (hg : g ∈ F) (hb : b ∈ A) (heq : f + a = g + b) : a = b := by
  have hx : f + a ∈ E := add_mem_target_of_tiles hTile hf ha
  obtain ⟨chosen, -, hunique⟩ := existsUnique_representation_of_mem hTile hx
  have hfrep : f ∈ F ∧ f + a - f ∈ A := by
    exact ⟨hf, by simpa only [add_sub_cancel_left] using ha⟩
  have hgrep : g ∈ F ∧ f + a - g ∈ A := by
    refine ⟨hg, ?_⟩
    rw [heq]
    simpa only [add_sub_cancel_left] using hb
  have hfg : f = g := (hunique f hfrep).trans (hunique g hgrep).symm
  rw [hfg] at heq
  exact add_left_cancel heq

private theorem connectedComponentMk_eq_of_transfer
    {G : Type*} [AddCommGroup G]
    {F : Finset G} {A : Set G} {v : G} {a b : A}
    (h : Tiling.RationalPolygonal.quakeTransfer F A v a b) :
    (Tiling.RationalPolygonal.quakeGraph F A v).connectedComponentMk a =
      (Tiling.RationalPolygonal.quakeGraph F A v).connectedComponentMk b := by
  by_cases hab : a = b
  · exact congrArg _ hab
  apply SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj
  rw [Tiling.RationalPolygonal.quakeGraph, SimpleGraph.fromRel_adj]
  exact ⟨hab, Or.inl h⟩

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
  · have hfilter : (F.filter fun f ↦ x - f ∈ A) = ∅ := by
      exact Finset.filter_eq_empty_iff.mpr fun f hf ↦ houtside x hx f hf
    rw [if_neg hx, hfilter]
    simp

theorem verticalPlateCarrier_periodic
    {F : Finset TranslationalTilings.Plane}
    {A E : Set TranslationalTilings.Plane}
    (_hF : F.Nonempty)
    (hTile : TranslationalTilings.Tiles F A E)
    (hEVertical : Tiling.RationalPolygonal.DiscretePeriodicBy E verticalDiscreteUnit)
    (P : Tiling.RationalPolygonal.QuakePlate F A verticalDiscreteUnit) :
    Tiling.RationalPolygonal.DiscretePeriodicBy
      (Tiling.RationalPolygonal.discreteCarrier F
        (Tiling.RationalPolygonal.quakePlateTranslations P))
      verticalDiscreteUnit := by
  intro x
  constructor
  · rintro ⟨f, hf, a, haP, hxa⟩
    obtain ⟨haA, hacomp⟩ := haP
    have hxvE : x + verticalDiscreteUnit ∈ E := by
      rw [hxa]
      exact add_mem_target_of_tiles hTile hf haA
    have hxE : x ∈ E := (hEVertical x).mp hxvE
    obtain ⟨f', hf'A, -⟩ := existsUnique_representation_of_mem hTile hxE
    let a' : TranslationalTilings.Plane := x - f'
    have ha'A : a' ∈ A := hf'A.2
    have hrepresentation : x = f' + a' := by
      dsimp only [a']
      abel
    let as : A := ⟨a, haA⟩
    let as' : A := ⟨a', ha'A⟩
    have htransfer : Tiling.RationalPolygonal.quakeTransfer
        F A verticalDiscreteUnit as' as := by
      refine ⟨f', hf'A.1, f, hf, ?_⟩
      rw [← hxa, hrepresentation]
    have hcomp' :
        (Tiling.RationalPolygonal.quakeGraph F A verticalDiscreteUnit).connectedComponentMk as' =
          P := by
      rw [← hacomp]
      exact connectedComponentMk_eq_of_transfer htransfer
    exact ⟨f', hf'A.1, a', ⟨ha'A, hcomp'⟩, hrepresentation⟩
  · rintro ⟨f, hf, a, haP, hxa⟩
    obtain ⟨haA, hacomp⟩ := haP
    have hxE : x ∈ E := by
      rw [hxa]
      exact add_mem_target_of_tiles hTile hf haA
    have hxvE : x + verticalDiscreteUnit ∈ E := (hEVertical x).mpr hxE
    obtain ⟨f', hf'A, -⟩ := existsUnique_representation_of_mem hTile hxvE
    let a' : TranslationalTilings.Plane := x + verticalDiscreteUnit - f'
    have ha'A : a' ∈ A := hf'A.2
    have hrepresentation : x + verticalDiscreteUnit = f' + a' := by
      dsimp only [a']
      abel
    let as : A := ⟨a, haA⟩
    let as' : A := ⟨a', ha'A⟩
    have htransfer : Tiling.RationalPolygonal.quakeTransfer
        F A verticalDiscreteUnit as as' := by
      refine ⟨f, hf, f', hf'A.1, ?_⟩
      rw [← hrepresentation, hxa]
    have hcomp' :
        (Tiling.RationalPolygonal.quakeGraph F A verticalDiscreteUnit).connectedComponentMk as' =
          P := by
      rw [← hacomp]
      exact (connectedComponentMk_eq_of_transfer htransfer).symm
    exact ⟨f', hf'A.1, a', ⟨ha'A, hcomp'⟩, hrepresentation⟩

private theorem verticalPlateCarriers_disjoint
    {F : Finset TranslationalTilings.Plane}
    {A E : Set TranslationalTilings.Plane}
    (hTile : TranslationalTilings.Tiles F A E)
    {P Q : Tiling.RationalPolygonal.QuakePlate F A verticalDiscreteUnit}
    (hPQ : P ≠ Q) :
    Disjoint
      (Tiling.RationalPolygonal.discreteCarrier F
        (Tiling.RationalPolygonal.quakePlateTranslations P))
      (Tiling.RationalPolygonal.discreteCarrier F
        (Tiling.RationalPolygonal.quakePlateTranslations Q)) := by
  rw [Set.disjoint_left]
  intro x hxP hxQ
  obtain ⟨f, hf, a, haP, hfa⟩ := hxP
  obtain ⟨g, hg, b, hbQ, hgb⟩ := hxQ
  obtain ⟨haA, hacomp⟩ := haP
  obtain ⟨hbA, hbcomp⟩ := hbQ
  have hab : a = b := translation_eq_of_eq_representations
    hTile hf haA hg hbA (hfa.symm.trans hgb)
  subst b
  exact hPQ (hacomp.symm.trans hbcomp)

private theorem shifted_representation_mem_plateCarrier
    {F : Finset TranslationalTilings.Plane}
    {A E : Set TranslationalTilings.Plane} {f : TranslationalTilings.Plane}
    (hF : F.Nonempty)
    (hTile : TranslationalTilings.Tiles F A E)
    (hEVertical : Tiling.RationalPolygonal.DiscretePeriodicBy E verticalDiscreteUnit)
    (hf : f ∈ F) (a : A)
    (shift : Tiling.RationalPolygonal.QuakePlate
      F A verticalDiscreteUnit → ℤ) :
    f + (shift ((Tiling.RationalPolygonal.quakeGraph
        F A verticalDiscreteUnit).connectedComponentMk a) • verticalDiscreteUnit +
          (a : TranslationalTilings.Plane)) ∈
      Tiling.RationalPolygonal.discreteCarrier F
        (Tiling.RationalPolygonal.quakePlateTranslations
          ((Tiling.RationalPolygonal.quakeGraph
            F A verticalDiscreteUnit).connectedComponentMk a)) := by
  let P := (Tiling.RationalPolygonal.quakeGraph
    F A verticalDiscreteUnit).connectedComponentMk a
  have hbase : f + (a : TranslationalTilings.Plane) ∈
      Tiling.RationalPolygonal.discreteCarrier F
        (Tiling.RationalPolygonal.quakePlateTranslations P) :=
    ⟨f, hf, a, Tiling.RationalPolygonal.mem_quakePlateTranslations_mk a, rfl⟩
  have hperiod := (verticalPlateCarrier_periodic hF hTile hEVertical P).zsmul (shift P)
  have hshifted := (hperiod (f + (a : TranslationalTilings.Plane))).2 hbase
  convert hshifted using 1
  dsimp only [P]
  abel

private theorem plate_subset_closed_under_adj
    {F : Finset TranslationalTilings.Plane}
    {A E Q : Set TranslationalTilings.Plane}
    (hTile : TranslationalTilings.Tiles F A E) (hQA : Q ⊆ A)
    (hperiod : Tiling.RationalPolygonal.DiscretePeriodicBy
      (Tiling.RationalPolygonal.discreteCarrier F Q) verticalDiscreteUnit)
    {a b : A} (haQ : (a : TranslationalTilings.Plane) ∈ Q)
    (hab : (Tiling.RationalPolygonal.quakeGraph
      F A verticalDiscreteUnit).Adj a b) :
    (b : TranslationalTilings.Plane) ∈ Q := by
  rw [Tiling.RationalPolygonal.quakeGraph, SimpleGraph.fromRel_adj] at hab
  rcases hab.2 with hforward | hbackward
  · obtain ⟨f, hf, g, hg, heq⟩ := hforward
    have hbase : f + (a : TranslationalTilings.Plane) ∈
        Tiling.RationalPolygonal.discreteCarrier F Q :=
      ⟨f, hf, a, haQ, rfl⟩
    have hshift := (hperiod (f + (a : TranslationalTilings.Plane))).2 hbase
    obtain ⟨f', hf', q, hqQ, hrepr⟩ := hshift
    have heq' : g + (b : TranslationalTilings.Plane) = f' + q :=
      heq.symm.trans hrepr
    have hbq := translation_eq_of_eq_representations
      hTile hg b.2 hf' (hQA hqQ) heq'
    rw [hbq]
    exact hqQ
  · obtain ⟨f, hf, g, hg, heq⟩ := hbackward
    have hshift : g + (a : TranslationalTilings.Plane) ∈
        Tiling.RationalPolygonal.discreteCarrier F Q :=
      ⟨g, hg, a, haQ, rfl⟩
    have hbase : f + (b : TranslationalTilings.Plane) ∈
        Tiling.RationalPolygonal.discreteCarrier F Q := by
      apply (hperiod (f + (b : TranslationalTilings.Plane))).mp
      rwa [heq]
    obtain ⟨f', hf', q, hqQ, hrepr⟩ := hbase
    have hbq := translation_eq_of_eq_representations
      hTile hf b.2 hf' (hQA hqQ) hrepr
    rw [hbq]
    exact hqQ

private theorem plate_subset_closed_under_walk
    {F : Finset TranslationalTilings.Plane}
    {A E Q : Set TranslationalTilings.Plane}
    (hTile : TranslationalTilings.Tiles F A E) (hQA : Q ⊆ A)
    (hperiod : Tiling.RationalPolygonal.DiscretePeriodicBy
      (Tiling.RationalPolygonal.discreteCarrier F Q) verticalDiscreteUnit)
    {a b : A}
    (walk : (Tiling.RationalPolygonal.quakeGraph
      F A verticalDiscreteUnit).Walk a b)
    (haQ : (a : TranslationalTilings.Plane) ∈ Q) :
    (b : TranslationalTilings.Plane) ∈ Q := by
  induction walk with
  | nil => exact haQ
  | cons hab walk ih =>
      apply ih
      exact plate_subset_closed_under_adj hTile hQA hperiod haQ hab

theorem verticalPlate_minimal
    {F : Finset TranslationalTilings.Plane}
    {A E Q : Set TranslationalTilings.Plane}
    (_hF : F.Nonempty)
    (hTile : TranslationalTilings.Tiles F A E)
    (_hEVertical : Tiling.RationalPolygonal.DiscretePeriodicBy E verticalDiscreteUnit)
    (P : Tiling.RationalPolygonal.QuakePlate F A verticalDiscreteUnit)
    (hQP : Q ⊆ Tiling.RationalPolygonal.quakePlateTranslations P)
    (hQ : Q.Nonempty)
    (hQVertical : Tiling.RationalPolygonal.DiscretePeriodicBy
      (Tiling.RationalPolygonal.discreteCarrier F Q) verticalDiscreteUnit) :
    Q = Tiling.RationalPolygonal.quakePlateTranslations P := by
  apply Set.Subset.antisymm hQP
  obtain ⟨q, hqQ⟩ := hQ
  obtain ⟨hqA, hqcomp⟩ := hQP hqQ
  intro a haP
  obtain ⟨haA, hacomp⟩ := haP
  let qs : A := ⟨q, hqA⟩
  let as : A := ⟨a, haA⟩
  have hreach : (Tiling.RationalPolygonal.quakeGraph
      F A verticalDiscreteUnit).Reachable qs as := by
    apply SimpleGraph.ConnectedComponent.exact
    exact hqcomp.trans hacomp.symm
  obtain ⟨walk⟩ := hreach
  have hQA : Q ⊆ A := hQP.trans fun _ h ↦ Classical.choose h
  exact plate_subset_closed_under_walk hTile hQA hQVertical walk hqQ

theorem iUnion_verticalPlateCentres
    (F : Finset TranslationalTilings.Plane)
    (A : Set TranslationalTilings.Plane) :
    (⋃ P : Tiling.RationalPolygonal.QuakePlate F A verticalDiscreteUnit,
      Tiling.RationalPolygonal.quakePlateTranslations P) = A :=
  Tiling.RationalPolygonal.iUnion_quakePlateTranslations

theorem verticalPlateCentres_pairwiseDisjoint
    (F : Finset TranslationalTilings.Plane)
    (A : Set TranslationalTilings.Plane) :
    ∀ ⦃P Q : Tiling.RationalPolygonal.QuakePlate F A verticalDiscreteUnit⦄,
      P ≠ Q →
        Disjoint
          (Tiling.RationalPolygonal.quakePlateTranslations P)
          (Tiling.RationalPolygonal.quakePlateTranslations Q) := by
  intro P Q hPQ
  exact Tiling.RationalPolygonal.quakePlateTranslations_pairwiseDisjoint
    (Set.mem_univ P) (Set.mem_univ Q) hPQ

theorem verticalPlateCarrier_eq_projectionProduct
    {F : Finset TranslationalTilings.Plane}
    {A E : Set TranslationalTilings.Plane}
    (hF : F.Nonempty)
    (hTile : TranslationalTilings.Tiles F A E)
    (hEVertical : Tiling.RationalPolygonal.DiscretePeriodicBy E verticalDiscreteUnit)
    (P : Tiling.RationalPolygonal.QuakePlate F A verticalDiscreteUnit) :
    Tiling.RationalPolygonal.discreteCarrier F
        (Tiling.RationalPolygonal.quakePlateTranslations P) =
      verticalDiscreteCylinder
        (integerSumset
          (firstDiscreteCoordinate '' (F : Set TranslationalTilings.Plane))
          (firstDiscreteCoordinate ''
            Tiling.RationalPolygonal.quakePlateTranslations P)) := by
  ext z
  rw [mem_verticalDiscreteCylinder_iff]
  constructor
  · rintro ⟨f, hf, a, haP, rfl⟩
    change firstDiscreteCoordinate (f + a) ∈
      (firstDiscreteCoordinate '' (F : Set TranslationalTilings.Plane)) +
        (firstDiscreteCoordinate ''
          Tiling.RationalPolygonal.quakePlateTranslations P)
    refine ⟨firstDiscreteCoordinate f, ⟨f, hf, rfl⟩,
      firstDiscreteCoordinate a, ⟨a, haP, rfl⟩, ?_⟩
    rfl
  · intro hz
    change firstDiscreteCoordinate z ∈
      (firstDiscreteCoordinate '' (F : Set TranslationalTilings.Plane)) +
        (firstDiscreteCoordinate ''
          Tiling.RationalPolygonal.quakePlateTranslations P) at hz
    obtain ⟨u, ⟨f, hf, rfl⟩, v, ⟨a, haP, rfl⟩, huv⟩ := hz
    have hfirst : firstDiscreteCoordinate (f + a) = firstDiscreteCoordinate z := by
      exact huv
    let n : ℤ := z 1 - f 1 - a 1
    have hpoint : f + a + n • verticalDiscreteUnit = z := by
      funext i
      fin_cases i
      · change f 0 + a 0 + n * 0 = z 0
        change f 0 + a 0 = z 0 at hfirst
        omega
      · change f 1 + a 1 + n * 1 = z 1
        dsimp only [n]
        ring
    have hbase : f + a ∈ Tiling.RationalPolygonal.discreteCarrier F
        (Tiling.RationalPolygonal.quakePlateTranslations P) :=
      ⟨f, hf, a, haP, rfl⟩
    have hshift :=
      ((verticalPlateCarrier_periodic hF hTile hEVertical P).zsmul n (f + a)).2 hbase
    rwa [hpoint] at hshift

theorem discreteCarrier_union
    (F : Finset TranslationalTilings.Plane)
    (C D : Set TranslationalTilings.Plane) :
    Tiling.RationalPolygonal.discreteCarrier F (C ∪ D) =
      Tiling.RationalPolygonal.discreteCarrier F C ∪
        Tiling.RationalPolygonal.discreteCarrier F D := by
  ext x
  simp only [Tiling.RationalPolygonal.mem_discreteCarrier_iff,
    Set.mem_union]
  aesop

theorem discreteCarrier_iUnion
    {I : Type*} (F : Finset TranslationalTilings.Plane)
    (C : I → Set TranslationalTilings.Plane) :
    Tiling.RationalPolygonal.discreteCarrier F (⋃ i, C i) =
      ⋃ i, Tiling.RationalPolygonal.discreteCarrier F (C i) := by
  ext x
  simp only [Tiling.RationalPolygonal.mem_discreteCarrier_iff,
    Set.mem_iUnion]
  aesop

theorem discreteCarrier_sdiff
    {F : Finset TranslationalTilings.Plane}
    {A E C D : Set TranslationalTilings.Plane}
    (hTile : TranslationalTilings.Tiles F A E)
    (hC : C ⊆ A) (hD : D ⊆ A) :
    Tiling.RationalPolygonal.discreteCarrier F (C \ D) =
      Tiling.RationalPolygonal.discreteCarrier F C \
        Tiling.RationalPolygonal.discreteCarrier F D := by
  ext x
  constructor
  · rintro ⟨f, hf, c, ⟨hcC, hcD⟩, rfl⟩
    refine ⟨⟨f, hf, c, hcC, rfl⟩, ?_⟩
    rintro ⟨g, hg, d, hdD, heq⟩
    have hcd : c = d :=
      translation_eq_of_eq_representations hTile hf (hC hcC) hg (hD hdD) heq
    exact hcD (hcd ▸ hdD)
  · rintro ⟨⟨f, hf, c, hcC, rfl⟩, hnotD⟩
    refine ⟨f, hf, c, ⟨hcC, ?_⟩, rfl⟩
    intro hcD
    exact hnotD ⟨f, hf, c, hcD, rfl⟩

theorem periodicOn_iUnion
    {I : Type*} {H : AddSubgroup TranslationalTilings.Plane}
    {S : I → Set TranslationalTilings.Plane}
    (hS : ∀ i, TranslationalTilings.SetPeriodicOn H (S i)) :
    TranslationalTilings.SetPeriodicOn H (⋃ i, S i) := by
  intro h hh x
  simp only [Set.mem_iUnion]
  constructor
  · rintro ⟨i, hxi⟩
    exact ⟨i, (hS i h hh x).mp hxi⟩
  · rintro ⟨i, hxi⟩
    exact ⟨i, (hS i h hh x).mpr hxi⟩

theorem periodicOn_sdiff
    {H : AddSubgroup TranslationalTilings.Plane}
    {E S : Set TranslationalTilings.Plane}
    (hE : TranslationalTilings.SetPeriodicOn H E)
    (hS : TranslationalTilings.SetPeriodicOn H S) :
    TranslationalTilings.SetPeriodicOn H (E \ S) := by
  intro h hh x
  constructor
  · rintro ⟨hxE, hxS⟩
    refine ⟨(hE h hh x).mp hxE, ?_⟩
    intro hx
    exact hxS ((hS h hh x).mpr hx)
  · rintro ⟨hxE, hxS⟩
    refine ⟨(hE h hh x).mpr hxE, ?_⟩
    intro hx
    exact hxS ((hS h hh x).mp hx)

theorem tilesOn_quakeShiftedTranslations
    {F : Finset TranslationalTilings.Plane}
    {A E : Set TranslationalTilings.Plane}
    (hF : F.Nonempty)
    (hTile : TranslationalTilings.Tiles F A E)
    (hEVertical : Tiling.RationalPolygonal.DiscretePeriodicBy E verticalDiscreteUnit)
    (shift : Tiling.RationalPolygonal.QuakePlate
      F A verticalDiscreteUnit → ℤ) :
    TranslationalTilings.Tiles F
      (Tiling.RationalPolygonal.quakeShiftedTranslations shift) E := by
  apply tiles_of_existsUnique_on_target
  · intro x hxE
    obtain ⟨f₀, hf₀, -⟩ := existsUnique_representation_of_mem hTile hxE
    let a₀ : A := ⟨x - f₀, hf₀.2⟩
    let P₀ : Tiling.RationalPolygonal.QuakePlate F A verticalDiscreteUnit :=
      (Tiling.RationalPolygonal.quakeGraph
        F A verticalDiscreteUnit).connectedComponentMk a₀
    have hxP₀ : x ∈ Tiling.RationalPolygonal.discreteCarrier F
        (Tiling.RationalPolygonal.quakePlateTranslations P₀) := by
      refine ⟨f₀, hf₀.1, a₀,
        Tiling.RationalPolygonal.mem_quakePlateTranslations_mk a₀, ?_⟩
      dsimp only [a₀]
      abel
    have hperiod₀ :=
      (verticalPlateCarrier_periodic hF hTile hEVertical P₀).zsmul (-(shift P₀))
    have hback : x + (-(shift P₀)) • verticalDiscreteUnit ∈
        Tiling.RationalPolygonal.discreteCarrier F
          (Tiling.RationalPolygonal.quakePlateTranslations P₀) :=
      (hperiod₀ x).2 hxP₀
    obtain ⟨f, hf, a, haP₀, hrep⟩ := hback
    obtain ⟨haA, hacomp⟩ := haP₀
    let as : A := ⟨a, haA⟩
    have hnewTranslation : shift P₀ • verticalDiscreteUnit + a ∈
        Tiling.RationalPolygonal.quakeShiftedTranslations shift := by
      refine ⟨as, ?_⟩
      simp only [as, hacomp]
    have hxrep : x - f = shift P₀ • verticalDiscreteUnit + a := by
      have hx : x = f + a + shift P₀ • verticalDiscreteUnit := by
        rw [← hrep]
        simp only [neg_smul]
        abel
      rw [hx]
      abel
    refine ⟨f, ⟨hf, hxrep ▸ hnewTranslation⟩, ?_⟩
    intro g hg
    obtain ⟨s, hsnew⟩ := hg.2
    let Q : Tiling.RationalPolygonal.QuakePlate F A verticalDiscreteUnit :=
      (Tiling.RationalPolygonal.quakeGraph
        F A verticalDiscreteUnit).connectedComponentMk s
    have hxQ : x ∈ Tiling.RationalPolygonal.discreteCarrier F
        (Tiling.RationalPolygonal.quakePlateTranslations Q) := by
      have hcarrier := shifted_representation_mem_plateCarrier
        hF hTile hEVertical hg.1 s shift
      have hxeq : x = g +
          (shift ((Tiling.RationalPolygonal.quakeGraph
            F A verticalDiscreteUnit).connectedComponentMk s) • verticalDiscreteUnit +
              (s : TranslationalTilings.Plane)) := by
        calc
          x = g + (x - g) := by abel
          _ = g + (shift ((Tiling.RationalPolygonal.quakeGraph
              F A verticalDiscreteUnit).connectedComponentMk s) • verticalDiscreteUnit +
                (s : TranslationalTilings.Plane)) := by rw [← hsnew]
      rwa [← hxeq] at hcarrier
    have hQP : Q = P₀ := by
      by_contra hne
      exact (Set.disjoint_left.mp (verticalPlateCarriers_disjoint hTile hne)) hxQ hxP₀
    have hsameShift : shift Q = shift P₀ := congrArg shift hQP
    have hgOriginal : g + (s : TranslationalTilings.Plane) = f + a := by
      have hxg : x = g + (shift Q • verticalDiscreteUnit +
          (s : TranslationalTilings.Plane)) := by
        calc
          x = g + (x - g) := by abel
          _ = g + (shift Q • verticalDiscreteUnit +
              (s : TranslationalTilings.Plane)) := by rw [← hsnew]
      rw [hsameShift] at hxg
      have hxf : x = f + (shift P₀ • verticalDiscreteUnit + a) := by
        calc
          x = f + (x - f) := by abel
          _ = f + (shift P₀ • verticalDiscreteUnit + a) := by rw [hxrep]
      rw [hxg] at hxf
      apply add_left_cancel (a := shift P₀ • verticalDiscreteUnit)
      simpa only [add_assoc, add_left_comm, add_comm] using hxf
    have hsa : (s : TranslationalTilings.Plane) = a :=
      translation_eq_of_eq_representations
        hTile hg.1 s.2 hf haA hgOriginal
    have hgf : g = f := by
      rw [hsa] at hgOriginal
      exact add_right_cancel hgOriginal
    exact hgf
  · intro x hxE f hf hxshift
    obtain ⟨a, hnew⟩ := hxshift
    have hcarrier := shifted_representation_mem_plateCarrier
      hF hTile hEVertical hf a shift
    have hxeq : x = f +
        (shift ((Tiling.RationalPolygonal.quakeGraph
          F A verticalDiscreteUnit).connectedComponentMk a) • verticalDiscreteUnit +
            (a : TranslationalTilings.Plane)) := by
      calc
        x = f + (x - f) := by abel
        _ = f + (shift ((Tiling.RationalPolygonal.quakeGraph
            F A verticalDiscreteUnit).connectedComponentMk a) • verticalDiscreteUnit +
              (a : TranslationalTilings.Plane)) := by rw [← hnew]
    rw [← hxeq] at hcarrier
    obtain ⟨g, hg, b, hbP, hgb⟩ := hcarrier
    exact hxE (hgb ▸ add_mem_target_of_tiles hTile hg (Classical.choose hbP))

theorem exists_verticalPlateEnumeration
    {F : Finset TranslationalTilings.Plane}
    {A E : Set TranslationalTilings.Plane}
    (hF : F.Nonempty)
    (hTile : TranslationalTilings.Tiles F A E)
    (hEVertical : Tiling.RationalPolygonal.DiscretePeriodicBy E verticalDiscreteUnit)
    (P : Tiling.RationalPolygonal.QuakePlate F A verticalDiscreteUnit)
    (a₀ : Tiling.RationalPolygonal.quakePlateTranslations P) :
    ∃ (r : ℕ ≃ {x // x ∈ Tiling.RationalPolygonal.discreteCarrier F
        (Tiling.RationalPolygonal.quakePlateTranslations P)})
      (tilePoint centre : ℕ → TranslationalTilings.Plane),
      (∀ n, tilePoint n ∈ F) ∧
      (∀ n, centre n ∈ Tiling.RationalPolygonal.quakePlateTranslations P) ∧
      (∀ n, (r n : TranslationalTilings.Plane) = tilePoint n + centre n) ∧
      centre 0 = a₀ ∧
      ∀ n, 0 < n → ∃ m, m < n ∧ ∃ g ∈ F,
        firstDiscreteCoordinate (r n : TranslationalTilings.Plane) =
          firstDiscreteCoordinate (g + centre m) := by
  classical
  obtain ⟨f₀, hf₀⟩ := hF
  let Tile := {f // f ∈ F}
  let Centre :=
    {a // a ∈ Tiling.RationalPolygonal.quakePlateTranslations P}
  let Carrier :=
    {x // x ∈ Tiling.RationalPolygonal.discreteCarrier F
      (Tiling.RationalPolygonal.quakePlateTranslations P)}
  let X := Tile × Centre
  let fRoot : Tile := ⟨f₀, hf₀⟩
  let aRoot : Centre := ⟨a₀, a₀.2⟩
  let root : X := (fRoot, aRoot)
  let repMap : X → Carrier := fun x =>
    ⟨(x.1 : TranslationalTilings.Plane) +
        (x.2 : TranslationalTilings.Plane),
      ⟨x.1, x.1.2, x.2, x.2.2, rfl⟩⟩
  have hrepInj : Function.Injective repMap := by
    intro x y hxy
    have hadd :
        (x.1 : TranslationalTilings.Plane) +
            (x.2 : TranslationalTilings.Plane) =
          (y.1 : TranslationalTilings.Plane) +
            (y.2 : TranslationalTilings.Plane) :=
      congrArg Subtype.val hxy
    have hcentre : (x.2 : TranslationalTilings.Plane) = y.2 :=
      translation_eq_of_eq_representations hTile
        x.1.2 x.2.2.1 y.1.2 y.2.2.1 hadd
    have htile : (x.1 : TranslationalTilings.Plane) = y.1 := by
      rw [hcentre] at hadd
      exact add_right_cancel hadd
    exact Prod.ext (Subtype.ext htile) (Subtype.ext hcentre)
  have hrepSurj : Function.Surjective repMap := by
    intro z
    obtain ⟨f, hf, a, ha, hza⟩ := z.2
    refine ⟨(⟨f, hf⟩, ⟨a, ha⟩), ?_⟩
    exact Subtype.ext hza.symm
  let repEquiv : X ≃ Carrier :=
    Equiv.ofBijective repMap ⟨hrepInj, hrepSurj⟩
  /- Vertical periodicity supplies the infinitude needed for an `ℕ`-enumeration, even when the
  centre component itself is presented only as a subtype. -/
  let base : Carrier := repMap root
  let verticalLine : ℤ → Carrier := fun n =>
    ⟨(base : TranslationalTilings.Plane) + n • verticalDiscreteUnit,
      ((verticalPlateCarrier_periodic ⟨f₀, hf₀⟩ hTile hEVertical P).zsmul n base).2
        base.2⟩
  have hlineInj : Function.Injective verticalLine := by
    intro m n hmn
    have hcoord :=
      congrArg (fun z : Carrier => (z : TranslationalTilings.Plane) 1) hmn
    change ((base : TranslationalTilings.Plane) + m • verticalDiscreteUnit) 1 =
      ((base : TranslationalTilings.Plane) + n • verticalDiscreteUnit) 1 at hcoord
    simpa [verticalDiscreteUnit] using hcoord
  let _ : Infinite Carrier := Infinite.of_injective verticalLine hlineInj
  let _ : Infinite X := Infinite.of_injective repEquiv.symm repEquiv.symm.injective
  let graph := Tiling.RationalPolygonal.quakeGraph F A verticalDiscreteUnit
  let toVertex : Centre → A := fun a => ⟨a, a.2.1⟩
  have htoVertex : Function.Injective toVertex := by
    intro a b hab
    apply Subtype.ext
    exact congrArg (fun z : A => (z : TranslationalTilings.Plane)) hab
  let rootVertex : A := toVertex aRoot
  have hreachable (a : Centre) : graph.Reachable rootVertex (toVertex a) := by
    apply SimpleGraph.ConnectedComponent.exact
    change (Tiling.RationalPolygonal.quakeGraph F A verticalDiscreteUnit).connectedComponentMk
        (toVertex aRoot) =
      (Tiling.RationalPolygonal.quakeGraph F A verticalDiscreteUnit).connectedComponentMk
        (toVertex a)
    exact aRoot.2.2.trans a.2.2.symm
  have hcentrePred (a : Centre) (ha : a ≠ aRoot) :
      ∃ b : Centre, graph.Adj (toVertex b) (toVertex a) ∧
        graph.dist rootVertex (toVertex b) < graph.dist rootVertex (toVertex a) := by
    have hvne : toVertex aRoot ≠ toVertex a := fun h => ha (htoVertex h).symm
    obtain ⟨p, hp⟩ := (hreachable a).exists_walk_length_eq_dist
    have hpPos : 0 < p.length := by
      rw [hp]
      exact (hreachable a).pos_dist_of_ne hvne
    have hpNotNil : ¬p.Nil := SimpleGraph.Walk.not_nil_iff_lt_length.mpr hpPos
    have hbcomp :
        (Tiling.RationalPolygonal.quakeGraph F A verticalDiscreteUnit).connectedComponentMk
            p.penultimate = P :=
      (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj
        (p.adj_penultimate hpNotNil)).trans a.2.2
    let b : Centre := ⟨p.penultimate, ⟨p.penultimate.2, hbcomp⟩⟩
    refine ⟨b, ?_, ?_⟩
    · simpa [graph, toVertex, b] using p.adj_penultimate hpNotNil
    · have hle :=
        (Tiling.RationalPolygonal.quakeGraph F A verticalDiscreteUnit).dist_le p.dropLast
      have hlength := p.length_dropLast_add_one hpNotNil
      change graph.dist rootVertex p.penultimate ≤ p.dropLast.length at hle
      change graph.dist rootVertex p.penultimate < graph.dist rootVertex (toVertex a)
      omega
  have hprojectionWitness (a b : Centre)
      (hab : graph.Adj (toVertex b) (toVertex a)) :
      ∃ f : Tile, ∃ g : Tile,
        firstDiscreteCoordinate ((f : TranslationalTilings.Plane) + a) =
          firstDiscreteCoordinate ((g : TranslationalTilings.Plane) + b) := by
    change (Tiling.RationalPolygonal.quakeGraph F A verticalDiscreteUnit).Adj
      (toVertex b) (toVertex a) at hab
    rw [Tiling.RationalPolygonal.quakeGraph, SimpleGraph.fromRel_adj] at hab
    rcases hab.2 with htransfer | htransfer
    · obtain ⟨g, hg, f, hf, heq⟩ := htransfer
      refine ⟨⟨f, hf⟩, ⟨g, hg⟩, ?_⟩
      have hcoord := congrFun heq 0
      change g 0 + b.1 0 + 0 = f 0 + a.1 0 at hcoord
      simpa [firstDiscreteCoordinate, add_comm] using hcoord.symm
    · obtain ⟨f, hf, g, hg, heq⟩ := htransfer
      refine ⟨⟨f, hf⟩, ⟨g, hg⟩, ?_⟩
      have hcoord := congrFun heq 0
      change f 0 + a.1 0 + 0 = g 0 + b.1 0 at hcoord
      simpa [firstDiscreteCoordinate] using hcoord
  have hstep (a : Centre) (ha : a ≠ aRoot) :
      ∃ w : Centre × Tile × Tile,
        graph.Adj (toVertex w.1) (toVertex a) ∧
        graph.dist rootVertex (toVertex w.1) < graph.dist rootVertex (toVertex a) ∧
        firstDiscreteCoordinate ((w.2.1 : TranslationalTilings.Plane) + a) =
          firstDiscreteCoordinate ((w.2.2 : TranslationalTilings.Plane) + w.1) := by
    obtain ⟨b, hab, hdist⟩ := hcentrePred a ha
    obtain ⟨f, g, hcoord⟩ := hprojectionWitness a b hab
    exact ⟨(b, f, g), hab, hdist, hcoord⟩
  let step (a : Centre) (ha : a ≠ aRoot) : Centre × Tile × Tile :=
    Classical.choose (hstep a ha)
  have hstepSpec (a : Centre) (ha : a ≠ aRoot) :
      graph.Adj (toVertex (step a ha).1) (toVertex a) ∧
      graph.dist rootVertex (toVertex (step a ha).1) <
        graph.dist rootVertex (toVertex a) ∧
      firstDiscreteCoordinate
          (((step a ha).2.1 : TranslationalTilings.Plane) + a) =
        firstDiscreteCoordinate
          (((step a ha).2.2 : TranslationalTilings.Plane) + (step a ha).1) :=
    Classical.choose_spec (hstep a ha)
  let centreParent : Centre → Centre := fun a =>
    if ha : a = aRoot then aRoot else (step a ha).1
  let anchor : Centre → Tile := fun a =>
    if ha : a = aRoot then fRoot else (step a ha).2.1
  have hcentreParent_ne (a : Centre) (ha : a ≠ aRoot) :
      centreParent a = (step a ha).1 := by
    simp [centreParent, ha]
  have hanchor_ne (a : Centre) (ha : a ≠ aRoot) :
      anchor a = (step a ha).2.1 := by
    simp [anchor, ha]
  have hanchor_root : anchor aRoot = fRoot := by
    simp [anchor]
  let centreDepth : Centre → ℕ := fun a => graph.dist rootVertex (toVertex a)
  let height : X → ℕ := fun x =>
    2 * centreDepth x.2 + if x.1 = anchor x.2 then 0 else 1
  let parent : X → X := fun x =>
    if x.1 = anchor x.2 then (fRoot, centreParent x.2) else (anchor x.2, x.2)
  have hparentHeight (x : X) (hx : x ≠ root) : height (parent x) < height x := by
    by_cases hfa : x.1 = anchor x.2
    · have hac : x.2 ≠ aRoot := by
        intro hca
        have htile : x.1 = fRoot := by
          rw [hfa, hca, hanchor_root]
        apply hx
        exact Prod.ext htile hca
      have hdist := (hstepSpec x.2 hac).2.1
      rw [← hcentreParent_ne x.2 hac] at hdist
      simp only [parent, hfa, if_pos, height]
      change 2 * centreDepth (centreParent x.2) +
          (if fRoot = anchor (centreParent x.2) then 0 else 1) <
        2 * centreDepth x.2
      change graph.dist rootVertex (toVertex (centreParent x.2)) <
        graph.dist rootVertex (toVertex x.2) at hdist
      dsimp only [centreDepth]
      split_ifs <;> omega
    · simp only [parent, hfa, height]
      simp
  let R : X → X → Prop := fun x y =>
    ∃ g ∈ F,
      firstDiscreteCoordinate (repMap x : TranslationalTilings.Plane) =
        firstDiscreteCoordinate (g + (y.2 : TranslationalTilings.Plane))
  have hparentR (x : X) (hx : x ≠ root) : R x (parent x) := by
    by_cases hfa : x.1 = anchor x.2
    · have hac : x.2 ≠ aRoot := by
        intro hca
        have htile : x.1 = fRoot := by
          rw [hfa, hca, hanchor_root]
        apply hx
        exact Prod.ext htile hca
      have hspec := (hstepSpec x.2 hac).2.2
      rw [← hanchor_ne x.2 hac, ← hcentreParent_ne x.2 hac] at hspec
      refine ⟨(step x.2 hac).2.2, (step x.2 hac).2.2.2, ?_⟩
      change firstDiscreteCoordinate
          ((x.1 : TranslationalTilings.Plane) + (x.2 : TranslationalTilings.Plane)) =
        firstDiscreteCoordinate
          (((step x.2 hac).2.2 : TranslationalTilings.Plane) +
            ((parent x).2 : TranslationalTilings.Plane))
      rw [hfa]
      simpa [parent, hfa] using hspec
    · refine ⟨x.1, x.1.2, ?_⟩
      change firstDiscreteCoordinate
          ((x.1 : TranslationalTilings.Plane) + (x.2 : TranslationalTilings.Plane)) =
        firstDiscreteCoordinate
          ((x.1 : TranslationalTilings.Plane) +
            ((parent x).2 : TranslationalTilings.Plane))
      simp [parent, hfa]
  obtain ⟨enum, henumZero, henumParent⟩ :=
    exists_rootedEnumeration root parent height hparentHeight R hparentR
  let r : ℕ ≃ Carrier := enum.trans repEquiv
  let tilePoint : ℕ → TranslationalTilings.Plane := fun n => enum n |>.1
  let centre : ℕ → TranslationalTilings.Plane := fun n => enum n |>.2
  refine ⟨r, tilePoint, centre, ?_, ?_, ?_, ?_, ?_⟩
  · intro n
    exact (enum n).1.2
  · intro n
    exact (enum n).2.2
  · intro n
    rfl
  · have := congrArg (fun x : X => (x.2 : TranslationalTilings.Plane)) henumZero
    exact this
  · intro n hn
    obtain ⟨m, hmn, g, hg, hcoord⟩ := henumParent n hn
    exact ⟨m, hmn, g, hg, hcoord⟩

end Tiling.AxisParallel.Discrete
