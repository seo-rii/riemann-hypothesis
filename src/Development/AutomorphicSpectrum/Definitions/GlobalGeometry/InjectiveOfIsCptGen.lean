module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsCptGen
public import Mathlib.Data.Nat.Prime.Int
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

@[expose] public section

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.CptModel

open AlgebraicGeometry CategoryTheory

section General

variable {X : Scheme.{0}} {Ω : Type} [Field Ω]

def self (ξ : Spec (CommRingCat.of Ω) ⟶ X) : Cpt ξ := ⟨genPt ξ, specializes_refl _⟩

theorem genMap_self (ξ : Spec (CommRingCat.of Ω) ⟶ X) :
    genMap ξ (self ξ) = (Scheme.stalkClosedPointTo ξ).hom := by
  have h : X.presheaf.stalkSpecializes (self ξ).2 = 𝟙 _ := X.presheaf.stalkSpecializes_refl _
  unfold genMap
  rw [h]
  rfl

theorem unitAt_iff (ξ : Spec (CommRingCat.of Ω) ⟶ X) (p : Cpt ξ) (a : Ω) :
    unitAt ξ p a ↔ ∃ s : X.presheaf.stalk p.1, IsUnit s ∧ genMap ξ p s = a := by
  constructor
  · rintro ⟨h0, ⟨s, hs⟩, ⟨t, ht⟩⟩
    refine ⟨s, ?_, hs⟩
    have h1 : genMap ξ p (1 - s * t) = 0 := by
      rw [map_sub, map_mul, map_one, hs, ht, mul_inv_cancel₀ h0, sub_self]
    rcases IsLocalRing.isUnit_or_isUnit_one_sub_self (s * t) with h | h
    · exact isUnit_of_mul_isUnit_left h
    · exact absurd (h1 ▸ h.map (genMap ξ p)) not_isUnit_zero
  · rintro ⟨s, ⟨u, rfl⟩, rfl⟩
    refine ⟨(u.isUnit.map (genMap ξ p)).ne_zero, ⟨_, rfl⟩, ⟨(u⁻¹ : _ˣ), ?_⟩⟩
    exact (map_units_inv (genMap ξ p) u)

theorem regAt_self {ξ : Spec (CommRingCat.of Ω) ⟶ X} (h : IsCptGen ξ) : regAt ξ (self ξ) = ⊤ := by
  rw [regAt, RingHom.range_eq_top, genMap_self]
  exact h.bij.2

end General

section Affine

variable {R K : Type} [CommRing R] [Field K]

abbrev pt (φ : R →+* K) : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of R) :=
  Spec.map (CommRingCat.ofHom φ)

def tS (p : Spec (CommRingCat.of R)) : R →+* (Spec (CommRingCat.of R)).presheaf.stalk p :=
  (StructureSheaf.toStalk R p).hom

theorem genMap_toStalk (φ : R →+* K) (p : Cpt (pt φ)) (r : R) :
    genMap (pt φ) p (tS p.1 r) = φ r := by
  have h1 := Scheme.germ_stalkClosedPointTo_Spec (R := CommRingCat.of R) (S := CommRingCat.of K)
    (CommRingCat.ofHom φ)
  have h2 := (Spec (CommRingCat.of R)).presheaf.germ_stalkSpecializes (U := ⊤) (y := p.1) trivial p.2
  have h3 : (Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ (Spec (CommRingCat.of R)).presheaf.germ ⊤ p.1 trivial ≫
      ((Spec (CommRingCat.of R)).presheaf.stalkSpecializes p.2 ≫ Scheme.stalkClosedPointTo (pt φ)) =
      CommRingCat.ofHom φ := by
    have h4 : (Spec (CommRingCat.of R)).presheaf.germ ⊤ p.1 trivial ≫
      ((Spec (CommRingCat.of R)).presheaf.stalkSpecializes p.2 ≫ Scheme.stalkClosedPointTo (pt φ)) =
        (Scheme.ΓSpecIso (CommRingCat.of R)).hom ≫ CommRingCat.ofHom φ :=
      (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ Scheme.stalkClosedPointTo (pt φ)) h2).trans h1)
    exact (congrArg ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ ·) h4).trans (Iso.inv_hom_id_assoc _ _)
  exact congrArg (fun f => f.hom r) h3

theorem exists_frac (φ : R →+* K) (p : Cpt (pt φ)) (x : (Spec (CommRingCat.of R)).presheaf.stalk p.1) :
    ∃ a s : R, s ∉ p.1.asIdeal ∧
      x * tS p.1 s = tS p.1 a := by
  have key : ∀ (q : PrimeSpectrum R) (y : (Spec.structureSheaf R).presheaf.stalk q), ∃ a s : R, s ∉ q.asIdeal ∧
      y * algebraMap R _ s = algebraMap R _ a := fun q y => by
    obtain ⟨⟨a, s⟩, h⟩ := IsLocalization.surj q.asIdeal.primeCompl y
    exact ⟨a, s, s.2, h⟩
  exact key p.1 x

theorem isUnit_toStalk (p : PrimeSpectrum R) {s : R} (hs : s ∉ p.asIdeal) :
    IsUnit (tS p s) :=
  IsLocalization.map_units (M := p.asIdeal.primeCompl)
    ((Spec.structureSheaf R).presheaf.stalk p) ⟨s, hs⟩

theorem mem_regAt_iff (φ : R →+* K) (p : Cpt (pt φ)) (c : K) :
    c ∈ regAt (pt φ) p ↔ ∃ a s : R, s ∉ p.1.asIdeal ∧ φ s ≠ 0 ∧ c * φ s = φ a := by
  have hne : ∀ s : R, s ∉ p.1.asIdeal → φ s ≠ 0 := fun s hs => by
    rw [← genMap_toStalk φ p]
    exact ((isUnit_toStalk p.1 hs).map (genMap (pt φ) p)).ne_zero
  constructor
  · rintro ⟨x, rfl⟩
    obtain ⟨a, s, hs, h⟩ := exists_frac φ p x
    refine ⟨a, s, hs, hne s hs, ?_⟩
    rw [← genMap_toStalk φ p, ← genMap_toStalk φ p]
    exact (map_mul (genMap (pt φ) p) _ _).symm.trans (congrArg (genMap (pt φ) p) h)
  · rintro ⟨a, s, hs, h0, h⟩
    obtain ⟨v, hv⟩ := (isUnit_toStalk p.1 hs).exists_right_inv
    refine ⟨tS p.1 a * v, ?_⟩
    have e : φ s * genMap (pt φ) p v = 1 := by
      rw [← genMap_toStalk φ p]
      exact (map_mul (genMap (pt φ) p) _ _).symm.trans
        ((congrArg (genMap (pt φ) p) hv).trans (map_one _))
    refine (map_mul (genMap (pt φ) p) _ _).trans ?_
    rw [genMap_toStalk, ← h, mul_assoc, e, mul_one]

theorem genPt_asIdeal (φ : R →+* K) : (genPt (pt φ)).asIdeal = RingHom.ker φ := by
  change Ideal.comap φ (IsLocalRing.maximalIdeal K) = _
  rw [IsLocalRing.maximalIdeal_eq_bot]
  rfl

theorem genMap_injective (φ : R →+* K) (hφ : Function.Injective φ) (p : Cpt (pt φ)) :
    Function.Injective (genMap (pt φ) p) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨a, s, hs, h⟩ := exists_frac φ p x
  have h1 := (map_mul (genMap (pt φ) p) _ _).symm.trans (congrArg (genMap (pt φ) p) h)
  rw [hx, zero_mul, genMap_toStalk] at h1
  have ha : a = 0 := hφ (by rw [← h1, map_zero])
  rw [ha, map_zero] at h
  exact (isUnit_toStalk p.1 hs).mul_left_eq_zero.mp h

theorem isCptGen_fractionRing [IsDomain R] [Algebra R K] [IsFractionRing R K] :
    IsCptGen (pt (algebraMap R K)) := by
  have hi := IsFractionRing.injective R K
  refine ⟨?_, genMap_injective _ hi⟩
  rw [← genMap_self]
  refine ⟨genMap_injective _ hi _, fun c => ?_⟩
  obtain ⟨a, s, hs, rfl⟩ := IsFractionRing.div_surjective (A := R) c
  have h0 : algebraMap R K s ≠ 0 := (map_ne_zero_iff _ hi).2 (nonZeroDivisors.ne_zero hs)
  refine (mem_regAt_iff _ (self _) _).2 ⟨a, s, ?_, h0, div_mul_cancel₀ _ h0⟩
  change s ∉ (genPt (pt (algebraMap R K))).asIdeal
  rw [genPt_asIdeal]
  exact h0

end Affine

section Int

theorem isCptGen_int : IsCptGen (pt (algebraMap ℤ ℚ)) := isCptGen_fractionRing

def two : Cpt (pt (algebraMap ℤ ℚ)) :=
  ⟨(⟨Ideal.span {2}, (Ideal.span_singleton_prime two_ne_zero).2 Int.prime_two⟩ : PrimeSpectrum ℤ),
    (PrimeSpectrum.le_iff_specializes _ _).1 (by
      change (genPt (pt (algebraMap ℤ ℚ))).asIdeal ≤ _
      rw [genPt_asIdeal, (RingHom.injective_iff_ker_eq_bot _).1 (IsFractionRing.injective ℤ ℚ)]
      exact bot_le)⟩

theorem half_notMem : (2 : ℚ)⁻¹ ∉ regAt _ two := by
  rw [mem_regAt_iff]
  rintro ⟨a, s, hs, -, h⟩
  apply hs
  change s ∈ Ideal.span {(2 : ℤ)}
  rw [Ideal.mem_span_singleton]
  refine ⟨a, ?_⟩
  simp only [algebraMap_int_eq, eq_intCast] at h
  have : (s : ℚ) = 2 * a := by rw [← h]; ring
  exact_mod_cast this

theorem not_unitAt_two : ¬ unitAt _ two (2 : ℚ) := fun h => half_notMem h.2.2

theorem unitAt_three : unitAt _ two (3 : ℚ) := by
  have h : ∀ n : ℤ, ¬ (2 : ℤ) ∣ n → n ∉ two.1.asIdeal := fun n hn hm =>
    hn (Ideal.mem_span_singleton.1 hm)
  refine ⟨by norm_num, (mem_regAt_iff _ _ _).2 ⟨3, 1, h 1 (by decide), by simp, by simp⟩,
    (mem_regAt_iff _ _ _).2 ⟨1, 3, h 3 (by decide), by simp, by simp⟩⟩

end Int

end GlobalTheory.CompanionTheory.Ar.CptModel
