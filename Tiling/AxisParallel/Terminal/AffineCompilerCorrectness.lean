import Tiling.AxisParallel.Terminal.AffineCompiler
import Tiling.AxisParallel.Terminal.ExecutableInputSemantics
import Mathlib.Data.Rat.Lemmas
import Mathlib.Algebra.Order.Field.Basic

/-! Semantic correctness of the executable affine compiler. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
open scoped BigOperators

noncomputable section

namespace Tiling.AxisParallel.Terminal.Executable.AffineCompiler

def evalLinear {C n} (R : Realization C) (s : CoordSort)
    (e : LinearExpr C n) (x : Fin n → Real) : Real :=
  (∑ i, (e.coefficients i : Real) * x i) +
    ∑ i, (e.constant i : Real) * s.axis.coord (R.vertex i)

def Atom.Holds {C n} (R : Realization C) (s : CoordSort)
    (a : Atom C n) (x : Fin n → Real) : Prop :=
  match a.comparison with
  | .weak => evalLinear R s a.expr x ≤ 0
  | .strict => evalLinear R s a.expr x < 0

def SortedAtom.Holds {C h v} (R : Realization C) (x : Fin h → Real)
    (y : Fin v → Real) : SortedAtom C h v → Prop
  | .horizontal a => a.Holds R .horizontal x
  | .vertical a => a.Holds R .vertical y

def Clause.Holds {C h v} (R : Realization C) (c : Clause C h v)
    (x : Fin h → Real) (y : Fin v → Real) : Prop := ∀ a ∈ c, a.Holds R x y

def DNF.Holds {C h v} (R : Realization C) (p : DNF C h v)
    (x : Fin h → Real) (y : Fin v → Real) : Prop := ∃ c ∈ p, c.Holds R x y

private def variablePart {C : RegionCode} {n : Nat} (e : LinearExpr C n)
    (x : Fin n → Real) : Real :=
  ∑ i, (e.coefficients i : Real) * x i

private theorem variablePart_cons {C : RegionCode} {n : Nat} (e : LinearExpr C (n + 1))
    (t : Real) (x : Fin n → Real) :
    variablePart e (Fin.cons t x) =
      (e.head : Real) * t + variablePart e.tail x := by
  simp only [variablePart, Fin.sum_univ_succ, LinearExpr.head, LinearExpr.tail,
    Fin.cons_zero, Fin.cons_succ]

private theorem evalLinear_zero {C : RegionCode} {n : Nat} (R : Realization C)
    (s : CoordSort) (x : Fin n → Real) :
    evalLinear R s (LinearExpr.zero C n) x = 0 := by
  simp [evalLinear, LinearExpr.zero]

private theorem evalLinear_add {C : RegionCode} {n : Nat} (R : Realization C)
    (s : CoordSort) (a b : LinearExpr C n) (x : Fin n → Real) :
    evalLinear R s (a.add b) x = evalLinear R s a x + evalLinear R s b x := by
  simp only [evalLinear, LinearExpr.add, Rat.cast_add, add_mul, Finset.sum_add_distrib]
  ring

private theorem evalLinear_neg {C : RegionCode} {n : Nat} (R : Realization C)
    (s : CoordSort) (a : LinearExpr C n) (x : Fin n → Real) :
    evalLinear R s a.neg x = -evalLinear R s a x := by
  simp only [evalLinear, LinearExpr.neg, Rat.cast_neg, neg_mul, Finset.sum_neg_distrib]
  ring

private theorem evalLinear_sub {C : RegionCode} {n : Nat} (R : Realization C)
    (s : CoordSort) (a b : LinearExpr C n) (x : Fin n → Real) :
    evalLinear R s (a.sub b) x = evalLinear R s a x - evalLinear R s b x := by
  rw [LinearExpr.sub, evalLinear_add, evalLinear_neg]
  ring

private theorem evalLinear_scale {C : RegionCode} {n : Nat} (R : Realization C)
    (s : CoordSort) (q : Rat) (a : LinearExpr C n) (x : Fin n → Real) :
    evalLinear R s (a.scale q) x = (q : Real) * evalLinear R s a x := by
  simp only [evalLinear, LinearExpr.scale, Rat.cast_mul, mul_assoc]
  rw [← Finset.mul_sum, ← Finset.mul_sum]
  ring

private theorem evalLinear_cons {C : RegionCode} {n : Nat} (R : Realization C)
    (s : CoordSort) (e : LinearExpr C (n + 1)) (t : Real) (x : Fin n → Real) :
    evalLinear R s e (Fin.cons t x) =
      (e.head : Real) * t + evalLinear R s e.tail x := by
  change variablePart e (Fin.cons t x) + _ = _
  rw [variablePart_cons]
  unfold evalLinear variablePart
  simp only [LinearExpr.tail]
  ring

private theorem evalLinear_ofAffine {C : RegionCode} {n : Nat} (R : Realization C)
    (s : CoordSort) (a : AffineExpr C n) (x : Fin n → Real) :
    evalLinear R s (LinearExpr.ofAffine a) x = evalAffine R s a x := by
  rfl

private theorem dnfOr_holds {C : RegionCode} {h v : Nat} (R : Realization C)
    (p q : DNF C h v) (x : Fin h → Real) (y : Fin v → Real) :
    (dnfOr p q).Holds R x y ↔ p.Holds R x y ∨ q.Holds R x y := by
  simp only [DNF.Holds, dnfOr, List.mem_append]
  aesop

private theorem dnfAnd_holds {C : RegionCode} {h v : Nat} (R : Realization C)
    (p q : DNF C h v) (x : Fin h → Real) (y : Fin v → Real) :
    (dnfAnd p q).Holds R x y ↔ p.Holds R x y ∧ q.Holds R x y := by
  simp only [DNF.Holds, Clause.Holds, dnfAnd, List.mem_flatMap, List.mem_map]
  aesop

private theorem atom_negate_holds {C : RegionCode} {n : Nat} (R : Realization C)
    (s : CoordSort) (a : Atom C n) (x : Fin n → Real) :
    a.negate.Holds R s x ↔ ¬a.Holds R s x := by
  rcases a with ⟨comparison, expr⟩
  cases comparison <;> simp [Atom.negate, Atom.Holds, evalLinear_neg]

private theorem sortedAtom_negate_holds {C : RegionCode} {h v : Nat} (R : Realization C)
    (a : SortedAtom C h v) (x : Fin h → Real) (y : Fin v → Real) :
    a.negate.Holds R x y ↔ ¬a.Holds R x y := by
  cases a <;> exact atom_negate_holds _ _ _ _

private theorem negateClause_holds {C : RegionCode} {h v : Nat} (R : Realization C)
    (c : Clause C h v) (x : Fin h → Real) (y : Fin v → Real) :
    (negateClause c).Holds R x y ↔ ¬c.Holds R x y := by
  simp only [DNF.Holds, Clause.Holds, negateClause, List.mem_map]
  constructor
  · rintro ⟨_, ⟨a, ha, rfl⟩, h⟩ hc
    exact (sortedAtom_negate_holds R a x y).mp (h _ (by simp)) (hc a ha)
  · intro hc
    simp only [not_forall] at hc
    obtain ⟨a, ha, hna⟩ := hc
    refine ⟨[a.negate], ⟨a, ha, rfl⟩, ?_⟩
    intro b hb
    simp only [List.mem_singleton] at hb
    subst b
    exact (sortedAtom_negate_holds R a x y).mpr hna

private theorem negateDNF_foldl_holds {C : RegionCode} {h v : Nat} (R : Realization C)
    (p acc : DNF C h v) (x : Fin h → Real) (y : Fin v → Real) :
    (p.foldl (fun current c => dnfAnd current (negateClause c)) acc).Holds R x y ↔
      acc.Holds R x y ∧ ∀ c ∈ p, ¬c.Holds R x y := by
  induction p generalizing acc with
  | nil => simp
  | cons c p ih =>
      rw [List.foldl_cons, ih, dnfAnd_holds, negateClause_holds]
      simp only [List.mem_cons, forall_eq_or_imp]
      tauto

private theorem horizontalZeroTail_mem {C : RegionCode} {n v : Nat}
    (c : Clause C (n + 1) v) (b : SortedAtom C n v) :
    b ∈ c.filterMap horizontalZeroTail ↔
      (∃ q, SortedAtom.horizontal q ∈ c ∧ q.expr.head = 0 ∧
        b = .horizontal ⟨q.comparison, q.expr.tail⟩) ∨
      (∃ q, SortedAtom.vertical q ∈ c ∧ b = .vertical q) := by
  rw [List.mem_filterMap]
  constructor
  · rintro ⟨a, ha, hab⟩
    cases a with
    | horizontal q =>
        simp only [horizontalZeroTail] at hab
        split at hab
        · exact Or.inl ⟨q, ha, by assumption, (Option.some.inj hab).symm⟩
        · contradiction
    | vertical q =>
        right
        exact ⟨q, ha, by simpa [horizontalZeroTail] using hab.symm⟩
  · rintro (⟨q, hq, hzero, rfl⟩ | ⟨q, hq, rfl⟩)
    · exact ⟨.horizontal q, hq, by simp [horizontalZeroTail, hzero]⟩
    · exact ⟨.vertical q, hq, by simp [horizontalZeroTail]⟩

private theorem positiveHorizontal_mem {C : RegionCode} {n v : Nat}
    (c : Clause C (n + 1) v) (q : Atom C (n + 1)) :
    q ∈ c.filterMap positiveHorizontal ↔
      SortedAtom.horizontal q ∈ c ∧ 0 < q.expr.head := by
  rw [List.mem_filterMap]
  constructor
  · rintro ⟨a, ha, h⟩
    cases a with
    | horizontal a =>
        simp only [positiveHorizontal] at h
        split at h <;> simp_all
    | vertical a => simp [positiveHorizontal] at h
  · rintro ⟨hq, hpos⟩
    exact ⟨.horizontal q, hq, by simp [positiveHorizontal, hpos]⟩

private theorem negativeHorizontal_mem {C : RegionCode} {n v : Nat}
    (c : Clause C (n + 1) v) (q : Atom C (n + 1)) :
    q ∈ c.filterMap negativeHorizontal ↔
      SortedAtom.horizontal q ∈ c ∧ q.expr.head < 0 := by
  rw [List.mem_filterMap]
  constructor
  · rintro ⟨a, ha, h⟩
    cases a with
    | horizontal a =>
        simp only [negativeHorizontal] at h
        split at h <;> simp_all
    | vertical a => simp [negativeHorizontal] at h
  · rintro ⟨hq, hneg⟩
    exact ⟨.horizontal q, hq, by simp [negativeHorizontal, hneg]⟩

private theorem horizontal_partition_exhaustive {C : RegionCode} {n v : Nat}
    (a : SortedAtom C (n + 1) v) :
    (∃ b, horizontalZeroTail a = some b) ∨
      (∃ q, positiveHorizontal a = some q) ∨
      (∃ q, negativeHorizontal a = some q) := by
  cases a with
  | vertical q => exact Or.inl ⟨.vertical q, rfl⟩
  | horizontal q =>
      rcases lt_trichotomy q.expr.head 0 with hneg | hzero | hpos
      · exact Or.inr (Or.inr ⟨q, by simp [negativeHorizontal, hneg]⟩)
      · exact Or.inl ⟨.horizontal ⟨q.comparison, q.expr.tail⟩,
          by simp [horizontalZeroTail, hzero]⟩
      · exact Or.inr (Or.inl ⟨q, by simp [positiveHorizontal, hpos]⟩)

private theorem verticalZeroTail_mem {C : RegionCode} {h n : Nat}
    (c : Clause C h (n + 1)) (b : SortedAtom C h n) :
    b ∈ c.filterMap verticalZeroTail ↔
      (∃ q, SortedAtom.vertical q ∈ c ∧ q.expr.head = 0 ∧
        b = .vertical ⟨q.comparison, q.expr.tail⟩) ∨
      (∃ q, SortedAtom.horizontal q ∈ c ∧ b = .horizontal q) := by
  rw [List.mem_filterMap]
  constructor
  · rintro ⟨a, ha, hab⟩
    cases a with
    | vertical q =>
        simp only [verticalZeroTail] at hab
        split at hab
        · exact Or.inl ⟨q, ha, by assumption, (Option.some.inj hab).symm⟩
        · contradiction
    | horizontal q =>
        right
        exact ⟨q, ha, by simpa [verticalZeroTail] using hab.symm⟩
  · rintro (⟨q, hq, hzero, rfl⟩ | ⟨q, hq, rfl⟩)
    · exact ⟨.vertical q, hq, by simp [verticalZeroTail, hzero]⟩
    · exact ⟨.horizontal q, hq, by simp [verticalZeroTail]⟩

private theorem positiveVertical_mem {C : RegionCode} {h n : Nat}
    (c : Clause C h (n + 1)) (q : Atom C (n + 1)) :
    q ∈ c.filterMap positiveVertical ↔
      SortedAtom.vertical q ∈ c ∧ 0 < q.expr.head := by
  rw [List.mem_filterMap]
  constructor
  · rintro ⟨a, ha, hqa⟩
    cases a with
    | vertical a =>
        simp only [positiveVertical] at hqa
        split at hqa <;> simp_all
    | horizontal a => simp [positiveVertical] at hqa
  · rintro ⟨hq, hpos⟩
    exact ⟨.vertical q, hq, by simp [positiveVertical, hpos]⟩

private theorem negativeVertical_mem {C : RegionCode} {h n : Nat}
    (c : Clause C h (n + 1)) (q : Atom C (n + 1)) :
    q ∈ c.filterMap negativeVertical ↔
      SortedAtom.vertical q ∈ c ∧ q.expr.head < 0 := by
  rw [List.mem_filterMap]
  constructor
  · rintro ⟨a, ha, hqa⟩
    cases a with
    | vertical a =>
        simp only [negativeVertical] at hqa
        split at hqa <;> simp_all
    | horizontal a => simp [negativeVertical] at hqa
  · rintro ⟨hq, hneg⟩
    exact ⟨.vertical q, hq, by simp [negativeVertical, hneg]⟩

private theorem vertical_partition_exhaustive {C : RegionCode} {h n : Nat}
    (a : SortedAtom C h (n + 1)) :
    (∃ b, verticalZeroTail a = some b) ∨
      (∃ q, positiveVertical a = some q) ∨
      (∃ q, negativeVertical a = some q) := by
  cases a with
  | horizontal q => exact Or.inl ⟨.horizontal q, rfl⟩
  | vertical q =>
      rcases lt_trichotomy q.expr.head 0 with hneg | hzero | hpos
      · exact Or.inr (Or.inr ⟨q, by simp [negativeVertical, hneg]⟩)
      · exact Or.inl ⟨.vertical ⟨q.comparison, q.expr.tail⟩,
          by simp [verticalZeroTail, hzero]⟩
      · exact Or.inr (Or.inl ⟨q, by simp [positiveVertical, hpos]⟩)

private def atomEndpoint {C : RegionCode} {n : Nat} (R : Realization C) (s : CoordSort)
    (a : Atom C (n + 1)) (x : Fin n → Real) : Real :=
  -evalLinear R s a.expr.tail x / (a.expr.head : Real)

private def UpperSatisfied {C : RegionCode} {n : Nat} (R : Realization C) (s : CoordSort)
    (a : Atom C (n + 1)) (x : Fin n → Real) (t : Real) : Prop :=
  match a.comparison with
  | .weak => t ≤ atomEndpoint R s a x
  | .strict => t < atomEndpoint R s a x

private def LowerSatisfied {C : RegionCode} {n : Nat} (R : Realization C) (s : CoordSort)
    (a : Atom C (n + 1)) (x : Fin n → Real) (t : Real) : Prop :=
  match a.comparison with
  | .weak => atomEndpoint R s a x ≤ t
  | .strict => atomEndpoint R s a x < t

private theorem positiveAtom_holds_iff_upper {C : RegionCode} {n : Nat}
    (R : Realization C) (s : CoordSort) (a : Atom C (n + 1))
    (x : Fin n → Real) (t : Real) (hpos : 0 < a.expr.head) :
    a.Holds R s (Fin.cons t x) ↔ UpperSatisfied R s a x t := by
  have hpos' : 0 < (a.expr.head : Real) := by exact_mod_cast hpos
  rcases a with ⟨comparison, expr⟩
  cases comparison <;>
    simp only [Atom.Holds, UpperSatisfied, atomEndpoint, evalLinear_cons]
  · rw [le_div_iff₀ hpos']
    constructor <;> intro h <;> linarith
  · rw [lt_div_iff₀ hpos']
    constructor <;> intro h <;> linarith

private theorem negativeAtom_holds_iff_lower {C : RegionCode} {n : Nat}
    (R : Realization C) (s : CoordSort) (a : Atom C (n + 1))
    (x : Fin n → Real) (t : Real) (hneg : a.expr.head < 0) :
    a.Holds R s (Fin.cons t x) ↔ LowerSatisfied R s a x t := by
  have hneg' : (a.expr.head : Real) < 0 := by exact_mod_cast hneg
  rcases a with ⟨comparison, expr⟩
  cases comparison <;>
    simp only [Atom.Holds, LowerSatisfied, atomEndpoint, evalLinear_cons]
  · rw [div_le_iff_of_neg hneg']
    constructor <;> intro h <;> linarith
  · rw [div_lt_iff_of_neg hneg']
    constructor <;> intro h <;> linarith

private structure EndpointExtrema {C : RegionCode} {n : Nat} (R : Realization C)
    (s : CoordSort) (uppers lowers : List (Atom C (n + 1)))
    (x : Fin n → Real) where
  upper : Atom C (n + 1)
  upper_mem : upper ∈ uppers
  upper_min : ∀ u ∈ uppers, atomEndpoint R s upper x ≤ atomEndpoint R s u x
  lower : Atom C (n + 1)
  lower_mem : lower ∈ lowers
  lower_max : ∀ l ∈ lowers, atomEndpoint R s l x ≤ atomEndpoint R s lower x

private theorem exists_list_min {α : Type*} (f : α → Real) (l : List α) (hl : l ≠ []) :
    ∃ a ∈ l, ∀ b ∈ l, f a ≤ f b := by
  induction l with
  | nil => contradiction
  | cons a l ih =>
      by_cases hnil : l = []
      · subst l
        exact ⟨a, by simp, by simp⟩
      · obtain ⟨b, hb, hmin⟩ := ih hnil
        by_cases hab : f a ≤ f b
        · exact ⟨a, by simp, fun c hc => by
            rcases List.mem_cons.mp hc with rfl | hc
            · exact le_rfl
            · exact hab.trans (hmin c hc)⟩
        · exact ⟨b, by simp [hb], fun c hc => by
            rcases List.mem_cons.mp hc with rfl | hc
            · exact le_of_not_ge hab
            · exact hmin c hc⟩

private theorem exists_list_max {α : Type*} (f : α → Real) (l : List α) (hl : l ≠ []) :
    ∃ a ∈ l, ∀ b ∈ l, f b ≤ f a := by
  obtain ⟨a, ha, hmin⟩ := exists_list_min (fun z => -f z) l hl
  exact ⟨a, ha, fun b hb => by have := hmin b hb; linarith⟩

private theorem endpointExtrema_exists {C : RegionCode} {n : Nat}
    (R : Realization C) (s : CoordSort) (uppers lowers : List (Atom C (n + 1)))
    (x : Fin n → Real) (hu : uppers ≠ []) (hl : lowers ≠ []) :
    Nonempty (EndpointExtrema R s uppers lowers x) := by
  obtain ⟨u, hu_mem, hu_min⟩ := exists_list_min (fun a => atomEndpoint R s a x) uppers hu
  obtain ⟨l, hl_mem, hl_max⟩ := exists_list_max (fun a => atomEndpoint R s a x) lowers hl
  exact ⟨⟨u, hu_mem, hu_min, l, hl_mem, hl_max⟩⟩

private theorem upperBounds_oneSided_feasible {C : RegionCode} {n : Nat}
    (R : Realization C) (s : CoordSort) (uppers : List (Atom C (n + 1)))
    (x : Fin n → Real) (_hpos : ∀ u ∈ uppers, 0 < u.expr.head) :
    ∃ t : Real, ∀ u ∈ uppers, UpperSatisfied R s u x t := by
  by_cases hempty : uppers = []
  · exact ⟨0, by simp [hempty]⟩
  · obtain ⟨u₀, hu₀, hmin⟩ :=
      exists_list_min (fun u => atomEndpoint R s u x) uppers hempty
    refine ⟨atomEndpoint R s u₀ x - 1, ?_⟩
    intro u hu
    have hle := hmin u hu
    cases hcomp : u.comparison <;> simp [UpperSatisfied, hcomp] <;> linarith

private theorem lowerBounds_oneSided_feasible {C : RegionCode} {n : Nat}
    (R : Realization C) (s : CoordSort) (lowers : List (Atom C (n + 1)))
    (x : Fin n → Real) (_hneg : ∀ l ∈ lowers, l.expr.head < 0) :
    ∃ t : Real, ∀ l ∈ lowers, LowerSatisfied R s l x t := by
  by_cases hempty : lowers = []
  · exact ⟨0, by simp [hempty]⟩
  · obtain ⟨l₀, hl₀, hmax⟩ :=
      exists_list_max (fun l => atomEndpoint R s l x) lowers hempty
    refine ⟨atomEndpoint R s l₀ x + 1, ?_⟩
    intro l hl
    have hle := hmax l hl
    cases hcomp : l.comparison <;> simp [LowerSatisfied, hcomp] <;> linarith

private theorem combineBounds_eval {C : RegionCode} {n : Nat} (R : Realization C)
    (s : CoordSort) (u l : Atom C (n + 1)) (x : Fin n → Real) :
    evalLinear R s (combineBounds u l).expr x =
      (u.expr.head : Real) * evalLinear R s l.expr.tail x -
        (l.expr.head : Real) * evalLinear R s u.expr.tail x := by
  simp only [combineBounds, evalLinear_sub, evalLinear_scale]

private theorem equalExtrema_areWeak {C : RegionCode} {n : Nat}
    (R : Realization C) (s : CoordSort) (u l : Atom C (n + 1))
    (x : Fin n → Real) (hu : 0 < u.expr.head) (hl : l.expr.head < 0)
    (hcomb : (combineBounds u l).Holds R s x)
    (heq : atomEndpoint R s l x = atomEndpoint R s u x) :
    u.comparison = .weak ∧ l.comparison = .weak := by
  have hu' : (u.expr.head : Real) ≠ 0 := by exact_mod_cast (ne_of_gt hu)
  have hl' : (l.expr.head : Real) ≠ 0 := by exact_mod_cast (ne_of_lt hl)
  have heval : evalLinear R s (combineBounds u l).expr x = 0 := by
    rw [combineBounds_eval]
    unfold atomEndpoint at heq
    field_simp [hu', hl'] at heq
    nlinarith
  rcases u with ⟨uc, ue⟩
  rcases l with ⟨lc, le⟩
  cases uc <;> cases lc
  · exact ⟨rfl, rfl⟩
  · exfalso
    have hev := heval
    simp only [combineBounds] at hev
    simp only [combineBounds, Atom.Holds] at hcomb
    simp at hcomb
    linarith
  · exfalso
    have hev := heval
    simp only [combineBounds] at hev
    simp only [combineBounds, Atom.Holds] at hcomb
    simp at hcomb
    linarith
  · exfalso
    have hev := heval
    simp only [combineBounds] at hev
    simp only [combineBounds, Atom.Holds] at hcomb
    simp at hcomb
    linarith

private theorem combineBounds_endpoint_le {C : RegionCode} {n : Nat}
    (R : Realization C) (s : CoordSort) (u l : Atom C (n + 1))
    (x : Fin n → Real) (hu : 0 < u.expr.head) (hl : l.expr.head < 0)
    (hcomb : (combineBounds u l).Holds R s x) :
    atomEndpoint R s l x ≤ atomEndpoint R s u x := by
  have hu' : 0 < (u.expr.head : Real) := by exact_mod_cast hu
  have hl' : (l.expr.head : Real) < 0 := by exact_mod_cast hl
  have heval : evalLinear R s (combineBounds u l).expr x ≤ 0 := by
    rcases u with ⟨uc, ue⟩
    rcases l with ⟨lc, le⟩
    cases uc <;> cases lc <;>
      simp only [combineBounds, Atom.Holds] at hcomb ⊢ <;>
      simp at hcomb ⊢ <;> linarith
  rw [combineBounds_eval] at heval
  unfold atomEndpoint
  rw [show -evalLinear R s l.expr.tail x / (l.expr.head : Real) =
    evalLinear R s l.expr.tail x / -(l.expr.head : Real) by ring]
  rw [div_le_div_iff₀ (neg_pos.mpr hl') hu']
  nlinarith

private theorem finiteBounds_feasible {C : RegionCode} {n : Nat}
    (R : Realization C) (s : CoordSort) (uppers lowers : List (Atom C (n + 1)))
    (x : Fin n → Real) (hpos : ∀ u ∈ uppers, 0 < u.expr.head)
    (hneg : ∀ l ∈ lowers, l.expr.head < 0)
    (hpair : ∀ u ∈ uppers, ∀ l ∈ lowers, (combineBounds u l).Holds R s x) :
    ∃ t : Real,
      (∀ u ∈ uppers, u.Holds R s (Fin.cons t x)) ∧
      (∀ l ∈ lowers, l.Holds R s (Fin.cons t x)) := by
  by_cases huempty : uppers = []
  · obtain ⟨t, ht⟩ := lowerBounds_oneSided_feasible R s lowers x hneg
    refine ⟨t, by simp [huempty], ?_⟩
    intro l hl
    exact (negativeAtom_holds_iff_lower R s l x t (hneg l hl)).mpr (ht l hl)
  by_cases hlempty : lowers = []
  · obtain ⟨t, ht⟩ := upperBounds_oneSided_feasible R s uppers x hpos
    refine ⟨t, ?_, by simp [hlempty]⟩
    intro u hu
    exact (positiveAtom_holds_iff_upper R s u x t (hpos u hu)).mpr (ht u hu)
  obtain ⟨E⟩ := endpointExtrema_exists R s uppers lowers x huempty hlempty
  let U := atomEndpoint R s E.upper x
  let L := atomEndpoint R s E.lower x
  have hLU : L ≤ U := combineBounds_endpoint_le R s E.upper E.lower x
    (hpos E.upper E.upper_mem) (hneg E.lower E.lower_mem)
    (hpair E.upper E.upper_mem E.lower E.lower_mem)
  by_cases hstrict : L < U
  · refine ⟨(L + U) / 2, ?_, ?_⟩
    · intro u hu
      apply (positiveAtom_holds_iff_upper R s u x _ (hpos u hu)).mpr
      have hUu : U ≤ atomEndpoint R s u x := E.upper_min u hu
      cases hcomp : u.comparison <;> simp [UpperSatisfied, hcomp] <;> linarith
    · intro l hl
      apply (negativeAtom_holds_iff_lower R s l x _ (hneg l hl)).mpr
      have hlL : atomEndpoint R s l x ≤ L := E.lower_max l hl
      cases hcomp : l.comparison <;> simp [LowerSatisfied, hcomp] <;> linarith
  · have hEq : L = U := le_antisymm hLU (le_of_not_gt hstrict)
    refine ⟨L, ?_, ?_⟩
    · intro u hu
      apply (positiveAtom_holds_iff_upper R s u x L (hpos u hu)).mpr
      have hUu : U ≤ atomEndpoint R s u x := E.upper_min u hu
      by_cases he : atomEndpoint R s u x = U
      · have hw := equalExtrema_areWeak R s u E.lower x (hpos u hu)
          (hneg E.lower E.lower_mem) (hpair u hu E.lower E.lower_mem)
          (by rw [he, ← hEq])
        simp [UpperSatisfied, hw.1, he, hEq]
      · have hlt : U < atomEndpoint R s u x := lt_of_le_of_ne hUu (Ne.symm he)
        cases hcomp : u.comparison <;> simp [UpperSatisfied, hcomp] <;> linarith
    · intro l hl
      apply (negativeAtom_holds_iff_lower R s l x L (hneg l hl)).mpr
      have hlL : atomEndpoint R s l x ≤ L := E.lower_max l hl
      by_cases he : atomEndpoint R s l x = L
      · have hw := equalExtrema_areWeak R s E.upper l x
          (hpos E.upper E.upper_mem) (hneg l hl) (hpair E.upper E.upper_mem l hl)
          (by rw [he, hEq])
        simp [LowerSatisfied, hw.2, he]
      · have hlt : atomEndpoint R s l x < L := lt_of_le_of_ne hlL he
        cases hcomp : l.comparison <;> simp [LowerSatisfied, hcomp] <;> linarith

private theorem combineBounds_holds_of_holds {C : RegionCode} {n : Nat}
    (R : Realization C) (s : CoordSort) (u l : Atom C (n + 1))
    (x : Fin n → Real) (t : Real) (hu : 0 < u.expr.head) (hl : l.expr.head < 0)
    (hU : u.Holds R s (Fin.cons t x)) (hL : l.Holds R s (Fin.cons t x)) :
    (combineBounds u l).Holds R s x := by
  have hu' : 0 < (u.expr.head : Real) := by exact_mod_cast hu
  have hl' : (l.expr.head : Real) < 0 := by exact_mod_cast hl
  rcases u with ⟨uc, ue⟩
  rcases l with ⟨lc, le⟩
  cases uc <;> cases lc
  · simp only [Atom.Holds, evalLinear_cons] at hU hL
    simp only [combineBounds, Atom.Holds, evalLinear_sub, evalLinear_scale]
    simp
    have h1 := mul_nonpos_of_nonneg_of_nonpos (le_of_lt hu') hL
    have h2 := mul_nonpos_of_nonneg_of_nonpos (le_of_lt (neg_pos.mpr hl')) hU
    nlinarith
  · simp only [Atom.Holds, evalLinear_cons] at hU hL
    simp only [combineBounds, Atom.Holds, evalLinear_sub, evalLinear_scale]
    simp
    have h1 := mul_neg_of_pos_of_neg hu' hL
    have h2 := mul_nonpos_of_nonneg_of_nonpos (le_of_lt (neg_pos.mpr hl')) hU
    nlinarith
  · simp only [Atom.Holds, evalLinear_cons] at hU hL
    simp only [combineBounds, Atom.Holds, evalLinear_sub, evalLinear_scale]
    simp
    have h1 := mul_nonpos_of_nonneg_of_nonpos (le_of_lt hu') hL
    have h2 := mul_neg_of_pos_of_neg (neg_pos.mpr hl') hU
    nlinarith
  · simp only [Atom.Holds, evalLinear_cons] at hU hL
    simp only [combineBounds, Atom.Holds, evalLinear_sub, evalLinear_scale]
    simp
    have h1 := mul_neg_of_pos_of_neg hu' hL
    have h2 := mul_neg_of_pos_of_neg (neg_pos.mpr hl') hU
    nlinarith

private theorem eliminateHorizontalClause_correct {C : RegionCode} {n v : Nat}
    (R : Realization C) (c : Clause C (n + 1) v) (x : Fin n → Real)
    (y : Fin v → Real) :
    (eliminateHorizontalClause c).Holds R x y ↔
      ∃ t : Real, c.Holds R (Fin.cons t x) y := by
  let fixed := c.filterMap horizontalZeroTail
  let uppers := c.filterMap positiveHorizontal
  let lowers := c.filterMap negativeHorizontal
  change Clause.Holds R (fixed ++ uppers.flatMap (fun u => lowers.map fun l =>
      SortedAtom.horizontal (combineBounds u l))) x y ↔ _
  constructor
  · intro hout
    have hpos : ∀ u ∈ uppers, 0 < u.expr.head := by
      intro u hu
      exact (positiveHorizontal_mem c u).mp hu |>.2
    have hneg : ∀ l ∈ lowers, l.expr.head < 0 := by
      intro l hl
      exact (negativeHorizontal_mem c l).mp hl |>.2
    have hpairs : ∀ u ∈ uppers, ∀ l ∈ lowers,
        (combineBounds u l).Holds R .horizontal x := by
      intro u hu l hl
      exact hout (.horizontal (combineBounds u l))
        (List.mem_append.mpr (Or.inr (List.mem_flatMap.mpr
          ⟨u, hu, List.mem_map.mpr ⟨l, hl, rfl⟩⟩)))
    obtain ⟨t, hupper, hlower⟩ :=
      finiteBounds_feasible R .horizontal uppers lowers x hpos hneg hpairs
    refine ⟨t, ?_⟩
    intro a ha
    rcases horizontal_partition_exhaustive a with ⟨b, hb⟩ | ⟨q, hq⟩ | ⟨q, hq⟩
    · have hbmem : b ∈ fixed := List.mem_filterMap.mpr ⟨a, ha, hb⟩
      have hbholds := hout b (List.mem_append.mpr (Or.inl hbmem))
      cases a with
      | horizontal a =>
          simp only [horizontalZeroTail] at hb
          split at hb
          · have hab := Option.some.inj hb
            subst b
            simp only [SortedAtom.Holds, Atom.Holds] at hbholds ⊢
            rw [evalLinear_cons]
            rename_i hzero
            simp only [hzero, Rat.cast_zero, zero_mul, zero_add]
            exact hbholds
          · contradiction
      | vertical a =>
          have hab := Option.some.inj hb
          subst b
          exact hbholds
    · have hqmem : q ∈ uppers := List.mem_filterMap.mpr ⟨a, ha, hq⟩
      cases a with
      | horizontal a =>
          simp only [positiveHorizontal] at hq
          split at hq
          · have haq := Option.some.inj hq
            subst q
            exact hupper a hqmem
          · contradiction
      | vertical a => simp [positiveHorizontal] at hq
    · have hqmem : q ∈ lowers := List.mem_filterMap.mpr ⟨a, ha, hq⟩
      cases a with
      | horizontal a =>
          simp only [negativeHorizontal] at hq
          split at hq
          · have haq := Option.some.inj hq
            subst q
            exact hlower a hqmem
          · contradiction
      | vertical a => simp [negativeHorizontal] at hq
  · rintro ⟨t, hin⟩
    intro b hb
    rcases List.mem_append.mp hb with hb | hb
    · rw [horizontalZeroTail_mem] at hb
      rcases hb with ⟨q, hq, hzero, rfl⟩ | ⟨q, hq, rfl⟩
      · have h := hin (.horizontal q) hq
        simp only [SortedAtom.Holds, Atom.Holds] at h ⊢
        rw [evalLinear_cons] at h
        simp only [hzero, Rat.cast_zero, zero_mul, zero_add] at h
        exact h
      · exact hin (.vertical q) hq
    · obtain ⟨u, hu, hmap⟩ := List.mem_flatMap.mp hb
      obtain ⟨l, hl, heq⟩ := List.mem_map.mp hmap
      subst b
      have hupos := (positiveHorizontal_mem c u).mp hu
      have hlneg := (negativeHorizontal_mem c l).mp hl
      exact combineBounds_holds_of_holds R .horizontal u l x t hupos.2 hlneg.2
        (hin (.horizontal u) hupos.1) (hin (.horizontal l) hlneg.1)

private theorem eliminateVerticalClause_correct {C : RegionCode} {h n : Nat}
    (R : Realization C) (c : Clause C h (n + 1)) (x : Fin h → Real)
    (y : Fin n → Real) :
    (eliminateVerticalClause c).Holds R x y ↔
      ∃ t : Real, c.Holds R x (Fin.cons t y) := by
  let fixed := c.filterMap verticalZeroTail
  let uppers := c.filterMap positiveVertical
  let lowers := c.filterMap negativeVertical
  change Clause.Holds R (fixed ++ uppers.flatMap (fun u => lowers.map fun l =>
      SortedAtom.vertical (combineBounds u l))) x y ↔ _
  constructor
  · intro hout
    have hpos : ∀ u ∈ uppers, 0 < u.expr.head := by
      intro u hu
      exact (positiveVertical_mem c u).mp hu |>.2
    have hneg : ∀ l ∈ lowers, l.expr.head < 0 := by
      intro l hl
      exact (negativeVertical_mem c l).mp hl |>.2
    have hpairs : ∀ u ∈ uppers, ∀ l ∈ lowers,
        (combineBounds u l).Holds R .vertical y := by
      intro u hu l hl
      exact hout (.vertical (combineBounds u l))
        (List.mem_append.mpr (Or.inr (List.mem_flatMap.mpr
          ⟨u, hu, List.mem_map.mpr ⟨l, hl, rfl⟩⟩)))
    obtain ⟨t, hupper, hlower⟩ :=
      finiteBounds_feasible R .vertical uppers lowers y hpos hneg hpairs
    refine ⟨t, ?_⟩
    intro a ha
    rcases vertical_partition_exhaustive a with ⟨b, hb⟩ | ⟨q, hq⟩ | ⟨q, hq⟩
    · have hbmem : b ∈ fixed := List.mem_filterMap.mpr ⟨a, ha, hb⟩
      have hbholds := hout b (List.mem_append.mpr (Or.inl hbmem))
      cases a with
      | vertical a =>
          simp only [verticalZeroTail] at hb
          split at hb
          · have hab := Option.some.inj hb
            subst b
            simp only [SortedAtom.Holds, Atom.Holds] at hbholds ⊢
            rw [evalLinear_cons]
            rename_i hzero
            simp only [hzero, Rat.cast_zero, zero_mul, zero_add]
            exact hbholds
          · contradiction
      | horizontal a =>
          have hab := Option.some.inj hb
          subst b
          exact hbholds
    · have hqmem : q ∈ uppers := List.mem_filterMap.mpr ⟨a, ha, hq⟩
      cases a with
      | vertical a =>
          simp only [positiveVertical] at hq
          split at hq
          · have haq := Option.some.inj hq
            subst q
            exact hupper a hqmem
          · contradiction
      | horizontal a => simp [positiveVertical] at hq
    · have hqmem : q ∈ lowers := List.mem_filterMap.mpr ⟨a, ha, hq⟩
      cases a with
      | vertical a =>
          simp only [negativeVertical] at hq
          split at hq
          · have haq := Option.some.inj hq
            subst q
            exact hlower a hqmem
          · contradiction
      | horizontal a => simp [negativeVertical] at hq
  · rintro ⟨t, hin⟩
    intro b hb
    rcases List.mem_append.mp hb with hb | hb
    · rw [verticalZeroTail_mem] at hb
      rcases hb with ⟨q, hq, hzero, rfl⟩ | ⟨q, hq, rfl⟩
      · have hqholds := hin (.vertical q) hq
        simp only [SortedAtom.Holds, Atom.Holds] at hqholds ⊢
        rw [evalLinear_cons] at hqholds
        simp only [hzero, Rat.cast_zero, zero_mul, zero_add] at hqholds
        exact hqholds
      · exact hin (.horizontal q) hq
    · obtain ⟨u, hu, hmap⟩ := List.mem_flatMap.mp hb
      obtain ⟨l, hl, heq⟩ := List.mem_map.mp hmap
      subst b
      have hupos := (positiveVertical_mem c u).mp hu
      have hlneg := (negativeVertical_mem c l).mp hl
      exact combineBounds_holds_of_holds R .vertical u l y t hupos.2 hlneg.2
        (hin (.vertical u) hupos.1) (hin (.vertical l) hlneg.1)

private theorem denominatorProduct_pos {n : Nat} (q : Fin n → Rat) :
    0 < ∏ i, (q i).den := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Fin.prod_univ_succ]
      exact Nat.mul_pos (Rat.den_pos _) (ih (fun i => q i.succ))

private theorem denominator_dvd_product {n : Nat} (q : Fin n → Rat) (i : Fin n) :
    (q i).den ∣ ∏ j, (q j).den := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
      rw [Fin.prod_univ_succ]
      refine Fin.cases ?_ (fun j => ?_) i
      · exact dvd_mul_right _ _
      · exact dvd_mul_of_dvd_right (ih (fun k => q k.succ) j) _

private theorem scaledRat_eq_intCast (q : Rat) (D : Nat) (hdiv : q.den ∣ D) :
    ∃ z : Int, ((D : Nat) : Rat) * q = (z : Rat) := by
  obtain ⟨k, rfl⟩ := hdiv
  refine ⟨(k : Int) * q.num, ?_⟩
  push_cast
  calc
    (q.den : Rat) * (k : Rat) * q = (k : Rat) * ((q.den : Rat) * q) := by ring
    _ = (k : Rat) * (q.num : Rat) := by rw [Rat.den_mul_eq_num]

private theorem scaledRat_den_eq_one (q : Rat) (D : Nat) (_hD : 0 < D)
    (hdiv : q.den ∣ D) : (((D : Nat) : Rat) * q).den = 1 := by
  obtain ⟨z, hz⟩ := scaledRat_eq_intCast q D hdiv
  rw [hz, Rat.den_intCast]

private theorem scaledRat_num_cast_rat (q : Rat) (D : Nat) (hD : 0 < D)
    (hdiv : q.den ∣ D) :
    ((((D : Nat) : Rat) * q).num : Rat) = ((D : Nat) : Rat) * q := by
  rw [← Rat.den_eq_one_iff]
  exact scaledRat_den_eq_one q D hD hdiv

private theorem scaledRat_num_cast_real (q : Rat) (D : Nat) (hD : 0 < D)
    (hdiv : q.den ∣ D) :
    ((((D : Nat) : Rat) * q).num : Real) = (D : Real) * (q : Real) := by
  exact_mod_cast scaledRat_num_cast_rat q D hD hdiv

private theorem commonDenominator_dvd {C : RegionCode} (e : LinearExpr C 0)
    (i : Fin C.vertexCount) : (e.constant i).den ∣ commonDenominator e := by
  exact denominator_dvd_product e.constant i

theorem commonDenominator_pos {C : RegionCode} (e : LinearExpr C 0) :
    0 < commonDenominator e := by
  exact denominatorProduct_pos e.constant

theorem clearInput_correct {C : RegionCode} (R : Realization C) (s : CoordSort)
    (e : LinearExpr C 0) :
    evalCoeff R s (clearInput e) =
      commonDenominator e * evalLinear R s e Fin.elim0 := by
  simp only [evalCoeff, clearInput, evalLinear, Finset.univ_eq_empty,
    Finset.sum_empty, zero_add]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [scaledRat_num_cast_real (e.constant i) (commonDenominator e)
    (commonDenominator_pos e) (commonDenominator_dvd e i)]
  ring

theorem negateDNF_correct {C : RegionCode} {h v : Nat} (R : Realization C)
    (p : DNF C h v) (x : Fin h → Real) (y : Fin v → Real) :
    (negateDNF p).Holds R x y ↔ ¬p.Holds R x y := by
  rw [negateDNF, negateDNF_foldl_holds]
  simp [DNF.Holds, Clause.Holds, dnfTrue]

theorem eliminateHorizontal_correct {C : RegionCode} {n v : Nat} (R : Realization C)
    (p : DNF C (n + 1) v) (x : Fin n → Real) (y : Fin v → Real) :
    (eliminateHorizontal p).Holds R x y ↔
      ∃ t : Real, p.Holds R (Fin.cons t x) y := by
  simp only [DNF.Holds, eliminateHorizontal, List.mem_map]
  constructor
  · rintro ⟨_, ⟨c, hc, rfl⟩, hclause⟩
    obtain ⟨t, ht⟩ := (eliminateHorizontalClause_correct R c x y).mp hclause
    exact ⟨t, c, hc, ht⟩
  · rintro ⟨t, c, hc, hclause⟩
    exact ⟨eliminateHorizontalClause c, ⟨c, hc, rfl⟩,
      (eliminateHorizontalClause_correct R c x y).mpr ⟨t, hclause⟩⟩

theorem eliminateVertical_correct {C : RegionCode} {h n : Nat} (R : Realization C)
    (p : DNF C h (n + 1)) (x : Fin h → Real) (y : Fin n → Real) :
    (eliminateVertical p).Holds R x y ↔
      ∃ t : Real, p.Holds R x (Fin.cons t y) := by
  simp only [DNF.Holds, eliminateVertical, List.mem_map]
  constructor
  · rintro ⟨_, ⟨c, hc, rfl⟩, hclause⟩
    obtain ⟨t, ht⟩ := (eliminateVerticalClause_correct R c x y).mp hclause
    exact ⟨t, c, hc, ht⟩
  · rintro ⟨t, c, hc, hclause⟩
    exact ⟨eliminateVerticalClause c, ⟨c, hc, rfl⟩,
      (eliminateVerticalClause_correct R c x y).mpr ⟨t, hclause⟩⟩

theorem compile_correct {C : RegionCode} {h v : Nat} (R : Realization C)
    (f : Formula C h v) (x : Fin h → Real) (y : Fin v → Real) :
    (compile f).Holds R x y ↔ f.Holds R x y := by
  induction f with
  | truth => simp [compile, DNF.Holds, Clause.Holds, dnfTrue, Formula.Holds]
  | falsity => simp [compile, DNF.Holds, dnfFalse, Formula.Holds]
  | horizontalLe a b =>
      simp [compile, DNF.Holds, Clause.Holds, dnfAtom, SortedAtom.Holds, Atom.Holds,
        Formula.Holds, evalLinear_sub, evalLinear_ofAffine]
  | horizontalLt a b =>
      simp [compile, DNF.Holds, Clause.Holds, dnfAtom, SortedAtom.Holds, Atom.Holds,
        Formula.Holds, evalLinear_sub, evalLinear_ofAffine]
  | verticalLe a b =>
      simp [compile, DNF.Holds, Clause.Holds, dnfAtom, SortedAtom.Holds, Atom.Holds,
        Formula.Holds, evalLinear_sub, evalLinear_ofAffine]
  | verticalLt a b =>
      simp [compile, DNF.Holds, Clause.Holds, dnfAtom, SortedAtom.Holds, Atom.Holds,
        Formula.Holds, evalLinear_sub, evalLinear_ofAffine]
  | conjunction p q ihp ihq =>
      rw [compile, dnfAnd_holds, ihp, ihq]
      rfl
  | disjunction p q ihp ihq =>
      rw [compile, dnfOr_holds, ihp, ihq]
      rfl
  | negation p ih =>
      rw [compile, negateDNF_correct, ih]
      rfl
  | existsHorizontal p ih =>
      rw [compile, eliminateHorizontal_correct]
      constructor
      · rintro ⟨t, ht⟩
        exact ⟨t, (ih _ _).mp ht⟩
      · rintro ⟨t, ht⟩
        exact ⟨t, (ih _ _).mpr ht⟩
  | existsVertical p ih =>
      rw [compile, eliminateVertical_correct]
      constructor
      · rintro ⟨t, ht⟩
        exact ⟨t, (ih _ _).mp ht⟩
      · rintro ⟨t, ht⟩
        exact ⟨t, (ih _ _).mpr ht⟩

private theorem strictReverseQuery_correct {C : RegionCode} (R : Realization C)
    (O : CorrectOracle C R) (s : CoordSort) (e : LinearExpr C 0) :
    (!(O.toOracle.answer ⟨s, Coeff.zero C, clearInput e⟩) = true) ↔
      evalLinear R s e Fin.elim0 < 0 := by
  have horacle := O.correct ⟨s, Coeff.zero C, clearInput e⟩
  have hzero : evalCoeff R s (Coeff.zero C) = 0 := by simp [evalCoeff, Coeff.zero]
  rw [hzero, clearInput_correct] at horacle
  have hD : (0 : Real) < commonDenominator e := by
    exact_mod_cast commonDenominator_pos e
  cases hanswer : O.toOracle.answer ⟨s, Coeff.zero C, clearInput e⟩
  · have hn : ¬0 ≤ (commonDenominator e : Real) * evalLinear R s e Fin.elim0 := by
      simpa only [hanswer, Bool.false_eq_true, false_iff] using horacle
    constructor
    · intro _
      by_contra hnot
      exact hn (mul_nonneg (le_of_lt hD) (le_of_not_gt hnot))
    · intro _
      norm_num [hanswer]
  · have hn : 0 ≤ evalLinear R s e Fin.elim0 := by
      have hm : 0 ≤ (commonDenominator e : Real) * evalLinear R s e Fin.elim0 := by
        simpa only [hanswer, Bool.true_eq, true_iff] using horacle
      nlinarith
    constructor
    · intro h
      norm_num [hanswer] at h
    · intro hlt
      exact (not_lt_of_ge hn hlt).elim

private theorem evalClosedAtom_correct {C : RegionCode} (R : Realization C)
    (O : CorrectOracle C R) (s : CoordSort) (a : Atom C 0) :
    evalClosedAtom O.toOracle s a = true ↔ a.Holds R s Fin.elim0 := by
  rcases a with ⟨comparison, expr⟩
  cases comparison
  · simp only [evalClosedAtom, Atom.Holds, closedAtomQuery]
    rw [O.correct, clearInput_correct]
    simp only [evalCoeff, Coeff.zero, Int.cast_zero, zero_mul, Finset.sum_const_zero]
    have hD : (0 : Real) < commonDenominator expr := by
      exact_mod_cast commonDenominator_pos expr
    constructor <;> intro h
    · nlinarith
    · exact mul_nonpos_of_nonneg_of_nonpos (le_of_lt hD) h
  · have horacle := O.correct ⟨s, Coeff.zero C, clearInput expr⟩
    have hzero : evalCoeff R s (Coeff.zero C) = 0 := by simp [evalCoeff, Coeff.zero]
    rw [hzero, clearInput_correct] at horacle
    have hD : (0 : Real) < commonDenominator expr := by
      exact_mod_cast commonDenominator_pos expr
    cases hanswer : O.toOracle.answer ⟨s, Coeff.zero C, clearInput expr⟩
    · have hn : ¬0 ≤ (commonDenominator expr : Real) * evalLinear R s expr Fin.elim0 := by
        simpa only [hanswer, Bool.false_eq_true, false_iff] using horacle
      constructor
      · intro _
        by_contra hnot
        exact hn (mul_nonneg (le_of_lt hD) (le_of_not_gt hnot))
      · intro _
        norm_num [evalClosedAtom, Atom.Holds, hanswer]
    · have hn : 0 ≤ evalLinear R s expr Fin.elim0 := by
        have hm : 0 ≤ (commonDenominator expr : Real) * evalLinear R s expr Fin.elim0 := by
          simpa only [hanswer, Bool.true_eq, true_iff] using horacle
        nlinarith
      constructor
      · intro h
        norm_num [evalClosedAtom, Atom.Holds, hanswer] at h
      · intro hlt
        exact (not_lt_of_ge hn hlt).elim

private theorem evalClosedSortedAtom_correct {C : RegionCode} (R : Realization C)
    (O : CorrectOracle C R) (a : SortedAtom C 0 0) :
    evalClosedSortedAtom O.toOracle a = true ↔
      a.Holds R Fin.elim0 Fin.elim0 := by
  cases a with
  | horizontal a => exact evalClosedAtom_correct R O .horizontal a
  | vertical a => exact evalClosedAtom_correct R O .vertical a

private theorem evalClosedClause_correct {C : RegionCode} (R : Realization C)
    (O : CorrectOracle C R) (c : Clause C 0 0) :
    evalClosedClause O.toOracle c = true ↔
      c.Holds R Fin.elim0 Fin.elim0 := by
  simp only [evalClosedClause, List.all_eq_true, Clause.Holds]
  exact forall_congr' fun a => imp_congr_right fun _ => evalClosedSortedAtom_correct R O a

private theorem evalClosedDNF_correct {C : RegionCode} (R : Realization C)
    (O : CorrectOracle C R) (p : DNF C 0 0) :
    evalClosedDNF O.toOracle p = true ↔ p.Holds R Fin.elim0 Fin.elim0 := by
  simp only [evalClosedDNF, List.any_eq_true, DNF.Holds]
  exact exists_congr fun c => and_congr_right fun _ => evalClosedClause_correct R O c

theorem decideFormula_correct {C : RegionCode} (R : Realization C)
    (O : CorrectOracle C R) (f : Formula C 0 0) :
    decideFormula O.toOracle f = true ↔ f.Holds R Fin.elim0 Fin.elim0 := by
  rw [decideFormula, evalClosedDNF_correct, compile_correct]

end Tiling.AxisParallel.Terminal.Executable.AffineCompiler
