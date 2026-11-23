module

public import Mathlib.Basic.NNReal.Defs
public import Mathlib.RingTheory.Ideal.Height
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.Valuation.Integers
public import Development.WeilBound.CoreStatements.HodgeTatePoints.DvrOfHeightOne
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
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.LatNormGrLatNeZeroOfSpan
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
public import Mathlib.RingTheory.Flat.TorsionFree

@[expose] public section

open Module NumberField GlobalTheory.CompanionTheory.Ar.HT TensorProduct

namespace PositivityTheory.HtPt.Gc

theorem test_descend : ∀ (A K : Type) [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsIntegrallyClosed A] [Field K] [Algebra A K] [IsFractionRing A K] (C : Type) [Field C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] (hv : v.Integers O) [Algebra A O] (𝔮 : Ideal A) (M : Type) [AddCommGroup M] [Module A M] (L : Submodule A M) (x : M), 𝔮.IsPrime → 𝔮.height = 1 → Function.Injective (algebraMap A O) → (∀ a, a ∈ 𝔮 ↔ v (algebraMap O C (algebraMap A O a)) < 1) → (1 : O) ⊗ₜ[A] x ∈ Submodule.span O ((fun y : M => (1 : O) ⊗ₜ[A] y) '' (L : Set M)) → ∃ s : A, s ∉ 𝔮 ∧ s • x ∈ L := by
  intro A K _ _ _ _ _ _ _ C _ v O _ _ hv _ q M _ _ L x hq h1 hinj hcen hx
  haveI : IsDomain O := hv.hom_inj.isDomain
  haveI : ValuationRing O := ValuationRing.of_integers _ hv
  haveI := dvr_of_height_one q h1
  have hu : ∀ s : q.primeCompl, IsUnit (algebraMap A O s) := fun s => by
    rw [hv.isUnit_iff_valuation_eq_one]
    exact le_antisymm (hv.map_le_one _) (not_lt.1 fun h => s.2 ((hcen s).2 h))
  let R := Localization.AtPrime q
  letI : Algebra R O := (IsLocalization.lift (M := q.primeCompl) hu).toAlgebra
  have hcomp : ∀ a : A, algebraMap R O (algebraMap A R a) = algebraMap A O a := fun a =>
    IsLocalization.lift_eq hu a
  haveI : IsScalarTower A R O := IsScalarTower.of_algebraMap_eq fun a => (hcomp a).symm
  have hinjR : Function.Injective (algebraMap R O) := by
    rw [injective_iff_map_eq_zero]
    intro r hr
    obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective q.primeCompl r
    have h2 : algebraMap A O a = 0 := by
      rw [← hcomp, ← IsLocalization.mk'_spec R a s, map_mul]
      simp only at hr
      rw [hr, zero_mul]
    have : a = 0 := hinj (by simpa using h2)
    simp [this]
  haveI : IsLocalHom (algebraMap R O) := ⟨fun r hr => by
    obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective q.primeCompl r
    simp only at hr ⊢
    rw [IsLocalization.AtPrime.isUnit_mk'_iff R q]
    have h2 : IsUnit (algebraMap A O a) := by
      rw [← hcomp, ← IsLocalization.mk'_spec R a s, map_mul, hcomp]
      exact hr.mul (hu s)
    rw [hv.isUnit_iff_valuation_eq_one] at h2
    intro ha
    exact ((hcen a).1 ha).ne h2⟩
  haveI : FaithfulSMul R O := (faithfulSMul_iff_algebraMap_injective R O).2 hinjR
  haveI : Module.Flat R O := by
    rw [IsDedekindDomain.flat_iff_torsion_eq_bot, ← Submodule.isTorsionFree_iff_torsion_eq_bot]
    infer_instance
  haveI : Module.FaithfullyFlat R O := Module.FaithfullyFlat.of_flat_of_isLocalHom
  have h0 : (1 : O) ⊗ₜ[A] (L.mkQ x) = 0 := by
    have : Submodule.span O ((fun y : M => (1 : O) ⊗ₜ[A] y) '' (L : Set M)) ≤
        LinearMap.ker (L.mkQ.baseChange O) := by
      rw [Submodule.span_le]
      rintro _ ⟨y, hy, rfl⟩
      simp [(Submodule.Quotient.mk_eq_zero L).2 hy]
    simpa using this hx
  have h2 : (1 : O) ⊗ₜ[R] ((1 : R) ⊗ₜ[A] (L.mkQ x)) = 0 := by
    apply (AlgebraTensorModule.cancelBaseChange A R O O (M ⧸ L)).injective
    simpa using h0
  rw [Module.FaithfullyFlat.one_tmul_eq_zero_iff] at h2
  obtain ⟨s, hs⟩ := (IsLocalizedModule.eq_zero_iff q.primeCompl
    (TensorProduct.mk A R (M ⧸ L) 1)).1 h2
  refine ⟨s, s.2, ?_⟩
  rw [← Submodule.Quotient.mk_eq_zero, Submodule.Quotient.mk_smul]
  exact hs

end PositivityTheory.HtPt.Gc
