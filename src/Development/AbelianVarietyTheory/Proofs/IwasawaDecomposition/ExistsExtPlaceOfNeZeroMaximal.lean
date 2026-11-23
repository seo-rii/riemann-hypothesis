module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingKrullDimIntegers
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ClosedPointGeometricFibresFinite
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsHorizontalPrimeLeOfIsMaximal
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.Valuation.LocalSubring
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
import ReciprocityTheory.AnalyticForms.RegularLocalRings.IntToRatA
import ReciprocityTheory.GaloisValuations.GlobalB

@[expose] public section

set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjVar GlobalTheory.TrueGeo Formalism.BasicNotions
open Pointwise

namespace GlobalTheory.TrueGeo.HorizRing

variable {F : Type} [Field F] [NumberField F]

theorem exists_embed (B : Type) [CommRing B] [IsDomain B] [Algebra (𝓞 F) B] [CharZero B] [Algebra.IsAlgebraic ℤ B] :
    ∃ ψ : B →ₐ[𝓞 F] AlgebraicClosure F, Function.Injective ψ := by
  have hinj : Function.Injective (algebraMap (𝓞 F) B) := by
    rw [RingHom.injective_iff_ker_eq_bot]
    refine Ideal.eq_bot_of_comap_eq_bot (R := ℤ) ?_
    change Ideal.comap (algebraMap ℤ (𝓞 F)) (RingHom.ker (algebraMap (𝓞 F) B)) = ⊥
    rw [RingHom.comap_ker, ← RingHom.injective_iff_ker_eq_bot]
    exact RingHom.injective_int _
  haveI : Algebra.IsAlgebraic (𝓞 F) B :=
    Algebra.IsAlgebraic.extendScalars (R := ℤ) (RingHom.injective_int _)
  haveI : Module.IsTorsionFree (𝓞 F) B := Module.isTorsionFree_iff_algebraMap_injective.2 hinj
  haveI : Module.IsTorsionFree (𝓞 F) (AlgebraicClosure F) := by
    rw [Module.isTorsionFree_iff_algebraMap_injective, IsScalarTower.algebraMap_eq (𝓞 F) F (AlgebraicClosure F)]
    exact (algebraMap F _).injective.comp (IsFractionRing.injective (𝓞 F) F)
  let ψ : B →ₐ[𝓞 F] AlgebraicClosure F := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  refine ⟨ψ, ?_⟩
  rw [injective_iff_map_eq_zero]
  intro x hx
  by_contra h0
  refine Ideal.comap_ne_bot_of_algebraic_mem (R := ℤ) (I := RingHom.ker ψ.toRingHom) h0 hx
    (Algebra.IsAlgebraic.isAlgebraic x) ?_
  change Ideal.comap (algebraMap ℤ B) (RingHom.ker ψ.toRingHom) = ⊥
  rw [RingHom.comap_ker, ← RingHom.injective_iff_ker_eq_bot]
  exact RingHom.injective_int _

theorem comap_ne_bot {R : Type} [CommRing R] [Algebra (𝓞 F) R] [Algebra.FiniteType (𝓞 F) R] (𝔪 : Ideal R)
    [h : 𝔪.IsMaximal] : 𝔪.comap (algebraMap (𝓞 F) R) ≠ ⊥ := by
  intro h0
  letI := Ideal.Quotient.field 𝔪
  haveI := ReciprocityTheory.AnForm.R.IntegerToRational.isJacobsonRing_int
  haveI : IsJacobsonRing (𝓞 F) := isJacobsonRing_of_isIntegral (R := ℤ)
  haveI : Module.Finite (𝓞 F) (R ⧸ 𝔪) := finite_of_finite_type_of_isJacobsonRing _ _
  have hinj : Function.Injective (algebraMap (𝓞 F) (R ⧸ 𝔪)) := by
    rw [RingHom.injective_iff_ker_eq_bot, IsScalarTower.algebraMap_eq (𝓞 F) R (R ⧸ 𝔪), ← RingHom.comap_ker,
      Ideal.Quotient.algebraMap_eq, Ideal.mk_ker, h0]
  exact RingOfIntegers.not_isField F
    ((Algebra.IsIntegral.isField_iff_isField hinj).2 (Field.toIsField _))

theorem exists_valuationSubring {R K : Type} [CommRing R] [Field K] (ψ : R →+* K) (𝔪 : Ideal R) [h : 𝔪.IsMaximal]
    (hk : RingHom.ker ψ ≤ 𝔪) : ∃ A : ValuationSubring K, (∀ x, ψ x ∈ A) ∧ ∀ x, A.valuation (ψ x) < 1 ↔ x ∈ 𝔪 := by
  have hs := ψ.rangeRestrict_surjective
  have hc : (𝔪.map ψ.rangeRestrict).comap ψ.rangeRestrict = 𝔪 := by
    rw [Ideal.comap_map_of_surjective _ hs, sup_eq_left, ← RingHom.ker_eq_comap_bot, RingHom.ker_rangeRestrict]
    exact hk
  have hne : 𝔪.map ψ.rangeRestrict ≠ ⊤ := fun ht => h.ne_top (by rw [← hc, ht, Ideal.comap_top])
  obtain ⟨A, hA, hI⟩ := Ideal.image_subset_nonunits_valuationSubring (A := ψ.range) _ hne
  have hm : ∀ x, ψ x ∈ A := fun x => hA ⟨x, rfl⟩
  refine ⟨A, hm, ?_⟩
  let φ : R →+* A := ψ.codRestrict A hm
  have hle : 𝔪 ≤ (IsLocalRing.maximalIdeal A).comap φ := fun x hx => by
    rw [Ideal.mem_comap, ValuationSubring.valuation_lt_one_iff]
    exact hI ⟨_, Ideal.mem_map_of_mem _ hx, rfl⟩
  have he := h.eq_of_le (Ideal.comap_ne_top φ (IsLocalRing.maximalIdeal.isMaximal A).ne_top) hle
  intro x
  rw [he, Ideal.mem_comap, ValuationSubring.valuation_lt_one_iff]
  rfl

theorem main : ∀ (F : Type) [Field F] [NumberField F] (R : Type) [CommRing R] [IsDomain R] [Algebra (𝓞 F) R] [Algebra.FiniteType (𝓞 F) R] [CharZero R] (𝔪 : Ideal R), 𝔪.IsMaximal → ∀ g : R, g ≠ 0 → ∃ (v : HeightOneSpectrum (𝓞 F)) (e : Ext v) (φ : R →+* e.O), (∀ a : 𝓞 F, ((φ (algebraMap (𝓞 F) R a) : e.O) : AlgebraicClosure F) = algebraMap F (AlgebraicClosure F) (algebraMap (𝓞 F) F a)) ∧ (IsLocalRing.maximalIdeal e.O).comap φ = 𝔪 ∧ φ g ≠ 0 := by
  intro F _ _ R _ _ _ _ _ 𝔪 h𝔪 g hg
  haveI : Algebra.FiniteType ℤ R := Algebra.FiniteType.trans (S := 𝓞 F) inferInstance inferInstance
  obtain ⟨q, hq, hqm, hgq, hc, ha⟩ := GlobalTheory.exists_horizontal_prime_le_of_isMaximal R 𝔪 h𝔪 g hg
  obtain ⟨ψ₀, hψ₀⟩ := @exists_embed F _ _ (R ⧸ q) _ _ _ hc (by convert ha <;> first | rfl | exact Subsingleton.elim _ _)
  let ψ : R →ₐ[𝓞 F] AlgebraicClosure F := ψ₀.comp (Ideal.Quotient.mkₐ (𝓞 F) q)
  have hker : ∀ x, ψ x = 0 ↔ x ∈ q := fun x => by
    rw [← Ideal.Quotient.eq_zero_iff_mem, ← map_eq_zero_iff ψ₀ hψ₀]
    rfl
  have hψ (a : 𝓞 F) : ψ (algebraMap (𝓞 F) R a) = algebraMap F (AlgebraicClosure F) (algebraMap (𝓞 F) F a) := by
    rw [ψ.commutes, ← IsScalarTower.algebraMap_apply]
  obtain ⟨A, hA, hAm⟩ := exists_valuationSubring ψ.toRingHom 𝔪 (fun x hx => hqm ((hker x).1 hx))
  let v : HeightOneSpectrum (𝓞 F) := ⟨𝔪.comap (algebraMap (𝓞 F) R), inferInstance, comap_ne_bot 𝔪⟩
  obtain ⟨e⟩ := (ExtConj.main F).1 v
  have hov (x : 𝓞 F) : A.valuation (algebraMap F (AlgebraicClosure F) (x : F)) < 1 ↔ x ∈ v.asIdeal := by
    have := hAm (algebraMap (𝓞 F) R x)
    rwa [show ψ.toRingHom (algebraMap (𝓞 F) R x) = _ from hψ x] at this
  obtain ⟨σ, hσ⟩ := ReciprocityTheory.Gal.exists_smul_eq_of_over hov (ExtConj.lies_over e)
  have hm (x : R) : σ (ψ x) ∈ e.O := by
    rw [← hσ]
    exact ValuationSubring.smul_mem_pointwise_smul σ _ A (hA x)
  let φ : R →+* e.O := (σ.toRingEquiv.toRingHom.comp ψ.toRingHom).codRestrict e.O hm
  have hφ (x : R) : (φ x : AlgebraicClosure F) = σ (ψ x) := rfl
  refine ⟨v, e, φ, fun a => ?_, ?_, fun h0 => hgq ?_⟩
  · rw [hφ, hψ, σ.commutes]
  · ext x
    rw [Ideal.mem_comap, ValuationSubring.valuation_lt_one_iff, hφ, ← hAm]
    have := ReciprocityTheory.Gal.smul_valuation_lt_one_iff σ A (σ (ψ x))
    rw [hσ] at this
    rw [this]
    simp
  · have := hφ g
    rw [h0] at this
    exact (hker g).1 (by simpa using this.symm)

end GlobalTheory.TrueGeo.HorizRing
