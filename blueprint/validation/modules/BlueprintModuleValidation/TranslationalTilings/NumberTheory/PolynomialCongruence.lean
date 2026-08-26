import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Analysis.Fourier.ZMod
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Factorization.Induction
import Mathlib.NumberTheory.GaussSum
import Mathlib.NumberTheory.LegendreSymbol.AddCharacter
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.RingTheory.Polynomial.Content
import TranslationalTilings.NumberTheory.FiniteCyclicPhase

/-!
Validator-only module generated from the blueprint.
It contains exact-type theorem axioms and is outside production trust.

source-sha256 81b1799e2e08cdaa6639df75a16e15fb3c415793ee04f52cc3cdd2def5dd15a3  blueprint/05b-chen-complete-sums.md
-/


set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3

open scoped BigOperators Real

/- blueprint/05b-chen-complete-sums.md:238; Polynomial.modPrime -/
namespace TranslationalTilings
noncomputable def _root_.Polynomial.modPrime (p : ℕ)
    (f : Polynomial ℤ) : Polynomial (ZMod p) :=
  f.map (Int.castRingHom (ZMod p))
end TranslationalTilings

/- blueprint/05b-chen-complete-sums.md:242; Polynomial.rootsModPrime -/
namespace TranslationalTilings
noncomputable def _root_.Polynomial.rootsModPrime (p : ℕ) [Fact p.Prime]
    (f : Polynomial ℤ) : Finset (ZMod p) :=
  Finset.univ.filter (Polynomial.modPrime p f).IsRoot
end TranslationalTilings

/- blueprint/05b-chen-complete-sums.md:246; Polynomial.rootMassModPrime -/
namespace TranslationalTilings
noncomputable def _root_.Polynomial.rootMassModPrime (p : ℕ) [Fact p.Prime]
    (f : Polynomial ℤ) : ℕ :=
  ∑ x ∈ Polynomial.rootsModPrime p f,
    (Polynomial.modPrime p f).rootMultiplicity x
end TranslationalTilings

/- blueprint/05b-chen-complete-sums.md:251; Polynomial.coeffDiv -/
namespace TranslationalTilings
noncomputable def _root_.Polynomial.coeffDiv
    (f : Polynomial ℤ) (m : ℕ) : Polynomial ℤ :=
  f.sum fun n a ↦ Polynomial.monomial n (a / (m : ℤ))
end TranslationalTilings

/- blueprint/05b-chen-complete-sums.md:255; Polynomial.coefficientPadicOrder -/
namespace TranslationalTilings
def _root_.Polynomial.coefficientPadicOrder
    (p : ℕ) (f : Polynomial ℤ) : ℕ :=
  padicValNat p (Polynomial.contentNat f)
end TranslationalTilings

/- blueprint/05b-chen-complete-sums.md:259; Polynomial.normalizeAtPrime -/
namespace TranslationalTilings
noncomputable def _root_.Polynomial.normalizeAtPrime
    (p : ℕ) (f : Polynomial ℤ) : Polynomial ℤ :=
  Polynomial.coeffDiv f (p ^ Polynomial.coefficientPadicOrder p f)
end TranslationalTilings

/- blueprint/05b-chen-complete-sums.md:263; Polynomial.primeScaleTranslate -/
namespace TranslationalTilings
noncomputable def _root_.Polynomial.primeScaleTranslate
    (f : Polynomial ℤ) (p : ℕ) (mu : ℤ) : Polynomial ℤ :=
  f.comp (Polynomial.C (p : ℤ) * Polynomial.X + Polynomial.C mu)
end TranslationalTilings

/- blueprint/05b-chen-complete-sums.md:267; Polynomial.normalizedPrimeScaleTranslate -/
namespace TranslationalTilings
noncomputable def _root_.Polynomial.normalizedPrimeScaleTranslate
    (f : Polynomial ℤ) (p : ℕ) (mu : ℤ) : Polynomial ℤ :=
  Polynomial.normalizeAtPrime p (Polynomial.primeScaleTranslate f p mu)
end TranslationalTilings

/- blueprint/05b-chen-complete-sums.md:271; Polynomial.stationaryTranslate -/
namespace TranslationalTilings
noncomputable def _root_.Polynomial.stationaryTranslate
    (f : Polynomial ℤ) (p : ℕ) (mu : ℤ) : Polynomial ℤ :=
  Polynomial.primeScaleTranslate f p mu - Polynomial.C (f.eval mu)
end TranslationalTilings

/- blueprint/05b-chen-complete-sums.md:275; Polynomial.stationaryOrder -/
namespace TranslationalTilings
noncomputable def _root_.Polynomial.stationaryOrder
    (f : Polynomial ℤ) (p : ℕ) (mu : ℤ) : ℕ :=
  Polynomial.coefficientPadicOrder p (Polynomial.stationaryTranslate f p mu)
end TranslationalTilings

/- blueprint/05b-chen-complete-sums.md:279; Polynomial.stationaryNormalize -/
namespace TranslationalTilings
noncomputable def _root_.Polynomial.stationaryNormalize
    (f : Polynomial ℤ) (p : ℕ) (mu : ℤ) : Polynomial ℤ :=
  Polynomial.normalizeAtPrime p (Polynomial.stationaryTranslate f p mu)
end TranslationalTilings

/- blueprint/05b-chen-complete-sums.md:283; Polynomial.derivativeContentOrder -/
namespace TranslationalTilings
noncomputable def _root_.Polynomial.derivativeContentOrder
    (f : Polynomial ℤ) (p : ℕ) : ℕ :=
  Polynomial.coefficientPadicOrder p f.derivative
end TranslationalTilings

/- blueprint/05b-chen-complete-sums.md:287; Polynomial.normalizedDerivative -/
namespace TranslationalTilings
noncomputable def _root_.Polynomial.normalizedDerivative
    (f : Polynomial ℤ) (p : ℕ) : Polynomial ℤ :=
  Polynomial.normalizeAtPrime p f.derivative
end TranslationalTilings

/- blueprint/05b-chen-complete-sums.md:291; Polynomial.derivativeRoots -/
namespace TranslationalTilings
noncomputable def _root_.Polynomial.derivativeRoots
    (f : Polynomial ℤ) (p : ℕ) [Fact p.Prime] : Finset (ZMod p) :=
  Polynomial.rootsModPrime p f.derivative
end TranslationalTilings

/- blueprint/05b-chen-complete-sums.md:295; Polynomial.derivativeRootMass -/
namespace TranslationalTilings
noncomputable def _root_.Polynomial.derivativeRootMass
    (f : Polynomial ℤ) (p : ℕ) [Fact p.Prime] : ℕ :=
  Polynomial.rootMassModPrime p f.derivative
end TranslationalTilings

/- blueprint/05b-chen-complete-sums.md:299; Polynomial.earlyDerivativeRoots -/
namespace TranslationalTilings
noncomputable def _root_.Polynomial.earlyDerivativeRoots
    (f : Polynomial ℤ) (p L : ℕ) [Fact p.Prime] : Finset (ZMod p) :=
  (Polynomial.derivativeRoots f p).filter fun mu ↦
    Polynomial.stationaryOrder f p mu.val < L
end TranslationalTilings

/- blueprint/05b-chen-complete-sums.md:304; Polynomial.lateDerivativeRoots -/
namespace TranslationalTilings
noncomputable def _root_.Polynomial.lateDerivativeRoots
    (f : Polynomial ℤ) (p L : ℕ) [Fact p.Prime] : Finset (ZMod p) :=
  (Polynomial.derivativeRoots f p).filter fun mu ↦
    L ≤ Polynomial.stationaryOrder f p mu.val
end TranslationalTilings

/- blueprint/05b-chen-complete-sums.md:309; Polynomial.derivativeRootMassOn -/
namespace TranslationalTilings
noncomputable def _root_.Polynomial.derivativeRootMassOn
    (f : Polynomial ℤ) (p : ℕ) [Fact p.Prime]
    (s : Finset (ZMod p)) : ℕ :=
  ∑ mu ∈ s, (Polynomial.modPrime p f.derivative).rootMultiplicity mu
end TranslationalTilings

/- blueprint/05b-chen-complete-sums.md:314; Polynomial.smallPrimeStationaryRoots -/
namespace TranslationalTilings
noncomputable def _root_.Polynomial.smallPrimeStationaryRoots
    (f : Polynomial ℤ) (p : ℕ) [Fact p.Prime] : Finset (ZMod p) :=
  Polynomial.rootsModPrime p (Polynomial.normalizedDerivative f p)
end TranslationalTilings

/- blueprint/05b-chen-complete-sums.md:318; Polynomial.smallPrimeStationaryMass -/
namespace TranslationalTilings
noncomputable def _root_.Polynomial.smallPrimeStationaryMass
    (f : Polynomial ℤ) (p : ℕ) [Fact p.Prime] : ℕ :=
  Polynomial.rootMassModPrime p (Polynomial.normalizedDerivative f p)
end TranslationalTilings

/- blueprint/05b-chen-complete-sums.md:322; Polynomial.StationaryChildInvariant -/
namespace TranslationalTilings
structure _root_.Polynomial.StationaryChildInvariant
    (f : Polynomial ℤ) (p : ℕ) (mu : ℤ) (d : ℕ) : Prop where
  translate_ne_zero : Polynomial.stationaryTranslate f p mu ≠ 0
  natDegree_eq : (Polynomial.stationaryNormalize f p mu).natDegree = d
  coeff_zero : (Polynomial.stationaryNormalize f p mu).coeff 0 = 0
  primitive :
    ¬ p ∣ Polynomial.nonconstantContentNat
      (Polynomial.stationaryNormalize f p mu)
end TranslationalTilings

/- blueprint/05b-chen-complete-sums.md:335; Polynomial.nonconstantContentNat_C_mul -/
namespace TranslationalTilings
axiom _root_.Polynomial.nonconstantContentNat_C_mul
    (u : ℤ) (f : Polynomial ℤ) :
  Polynomial.nonconstantContentNat (Polynomial.C u * f) =
    Int.natAbs u * Polynomial.nonconstantContentNat f
end TranslationalTilings

/- blueprint/05b-chen-complete-sums.md:340; Polynomial.normalizeAtPrime_spec -/
namespace TranslationalTilings
axiom _root_.Polynomial.normalizeAtPrime_spec
    (hp : p.Prime) (f : Polynomial ℤ) (hf : f ≠ 0) :
  f = Polynomial.C
      ((p ^ Polynomial.coefficientPadicOrder p f : ℕ) : ℤ) *
    Polynomial.normalizeAtPrime p f
end TranslationalTilings

/- blueprint/05b-chen-complete-sums.md:346; Polynomial.normalizeAtPrime_primitive -/
namespace TranslationalTilings
axiom _root_.Polynomial.normalizeAtPrime_primitive
    (hp : p.Prime) (f : Polynomial ℤ) (hf : f ≠ 0) :
  ¬ p ∣ Polynomial.contentNat (Polynomial.normalizeAtPrime p f)
end TranslationalTilings

/- blueprint/05b-chen-complete-sums.md:362; Polynomial.ack_lemma_2_2_degree -/
namespace TranslationalTilings
axiom _root_.Polynomial.ack_lemma_2_2_degree
    [Fact p.Prime] (hp : p.Prime) (g : Polynomial ℤ)
    (hg : Polynomial.modPrime p g ≠ 0) (mu : ZMod p)
    (hmu : (Polynomial.modPrime p g).IsRoot mu) :
  (Polynomial.modPrime p
      (Polynomial.normalizedPrimeScaleTranslate g p mu.val)).natDegree ≤
    (Polynomial.modPrime p g).rootMultiplicity mu
end TranslationalTilings

/- blueprint/05b-chen-complete-sums.md:370; Polynomial.ack_lemma_2_2_rootMass -/
namespace TranslationalTilings
axiom _root_.Polynomial.ack_lemma_2_2_rootMass
    [Fact p.Prime] (hp : p.Prime) (g : Polynomial ℤ)
    (hg : Polynomial.modPrime p g ≠ 0) (mu : ZMod p)
    (hmu : (Polynomial.modPrime p g).IsRoot mu) :
  Polynomial.rootMassModPrime p
      (Polynomial.normalizedPrimeScaleTranslate g p mu.val) ≤
    (Polynomial.modPrime p g).rootMultiplicity mu
end TranslationalTilings

/- blueprint/05b-chen-complete-sums.md:397; Polynomial.ack_lemma_2_3 -/
namespace TranslationalTilings
axiom _root_.Polynomial.ack_lemma_2_3
    (hp : p.Prime) (f : Polynomial ℤ)
    (hdegree : f.natDegree ≤ d)
    (hprimitive : ¬ p ∣ Polynomial.nonconstantContentNat f)
    (mu : ℤ) :
  1 ≤ Polynomial.stationaryOrder f p mu ∧
    Polynomial.stationaryOrder f p mu ≤ d
end TranslationalTilings

/- blueprint/05b-chen-complete-sums.md:405; Polynomial.stationaryChildInvariant -/
namespace TranslationalTilings
axiom _root_.Polynomial.stationaryChildInvariant
    (hp : p.Prime) (f : Polynomial ℤ) (hdegree : f.natDegree = d)
    (hd : 0 < d)
    (hprimitive : ¬ p ∣ Polynomial.nonconstantContentNat f)
    (mu : ℤ) :
  Polynomial.StationaryChildInvariant f p mu d
end TranslationalTilings

/- blueprint/05b-chen-complete-sums.md:412; Polynomial.stationaryOrder_two_le_of_isRoot -/
namespace TranslationalTilings
axiom _root_.Polynomial.stationaryOrder_two_le_of_isRoot
    (hp : p.Prime) (f : Polynomial ℤ) (mu : ZMod p)
    (htranslate : Polynomial.stationaryTranslate f p mu.val ≠ 0)
    (hmu : (Polynomial.modPrime p f.derivative).IsRoot mu) :
  2 ≤ Polynomial.stationaryOrder f p mu.val
end TranslationalTilings

/- blueprint/05b-chen-complete-sums.md:446; TranslationalTilings.chen_convexity_bound -/
namespace TranslationalTilings
axiom chen_convexity_bound
    {I : Type*} (s : Finset I) (a : ℝ) (m : I → ℕ)
    (ha : 1 < a) (hm : ∀ i ∈ s, 0 < m i) :
  ∑ i ∈ s, a ^ m i ≤
    max (((∑ i ∈ s, m i : ℕ) : ℝ) * a)
      (a ^ (∑ i ∈ s, m i))
end TranslationalTilings
