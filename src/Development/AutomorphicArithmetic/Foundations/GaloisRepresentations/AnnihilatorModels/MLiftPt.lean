module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.OrdReadOf
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES
open GlobalTheory.IwLevel (InSub IsIsogDeg)
open GlobalTheory.AbDual (evc IsAdditive swap)
attribute [local instance] Ideal.Quotient.field
open UpperTheory.Gal.crystallineComparison UpperTheory.Gal.crystallineComparison.Mod

theorem UpperTheory.Gal.crystallineComparison.Mod.liftPt_of :
    LiftPt := by
  intro V _ _ _ _ B _ _ _ _ χ hχ
  classical
  let m : Ideal B := RingHom.ker χ
  haveI : m.IsPrime := RingHom.ker_isPrime χ
  obtain ⟨q, hqmin, hqm⟩ := Ideal.exists_minimalPrimes_le (I := (⊥ : Ideal B)) (J := m) bot_le
  haveI : q.IsPrime := hqmin.1.1
  have hnzd : ∀ v : V, v ≠ 0 → algebraMap V B v ∈ nonZeroDivisors B := by
    intro v hv
    rw [mem_nonZeroDivisors_iff]
    refine ⟨fun x hx => ?_, fun x hx => ?_⟩
    · rw [← Algebra.smul_def] at hx
      exact (smul_eq_zero.mp hx).resolve_left hv
    · rw [← Algebra.commutes, ← Algebra.smul_def] at hx
      exact (smul_eq_zero.mp hx).resolve_left hv
  have hinj : Function.Injective (algebraMap V (B ⧸ q)) := by
    rw [injective_iff_map_eq_zero]
    intro v hv
    by_contra hv0
    rw [← Ideal.Quotient.mk_algebraMap, Ideal.Quotient.eq_zero_iff_mem] at hv
    exact Set.disjoint_left.mp (Ideal.disjoint_nonZeroDivisors_of_mem_minimalPrimes hqmin) hv (hnzd v hv0)
  have hK : Function.Injective (algebraMap V (FractionRing V)) := IsFractionRing.injective V (FractionRing V)
  haveI : Module.IsTorsionFree V (B ⧸ q) := by
    refine Module.IsTorsionFree.of_smul_eq_zero fun r x h => ?_
    rw [Algebra.smul_def, mul_eq_zero] at h
    exact h.imp_left fun h => hinj (by rw [h, map_zero])
  haveI : Module.IsTorsionFree V (FractionRing V) := by
    refine Module.IsTorsionFree.of_smul_eq_zero fun r x h => ?_
    rw [Algebra.smul_def, mul_eq_zero] at h
    exact h.imp_left fun h => hK (by rw [h, map_zero])
  haveI : Algebra.IsIntegral V (B ⧸ q) := inferInstance
  haveI : Algebra.IsAlgebraic V (B ⧸ q) := Algebra.IsIntegral.isAlgebraic
  let φ : (B ⧸ q) →ₐ[V] FractionRing V := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  have hker : RingHom.ker (φ : (B ⧸ q) →+* FractionRing V) = ⊥ := by
    apply Ideal.eq_bot_of_comap_eq_bot (R := V)
    ext v
    simp only [Ideal.mem_comap, RingHom.mem_ker, Ideal.mem_bot, RingHom.coe_coe, AlgHom.commutes]
    exact map_eq_zero_iff _ hK
  have hφinj : Function.Injective φ := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    have : x ∈ RingHom.ker (φ : (B ⧸ q) →+* FractionRing V) := hx
    rwa [hker] at this
  let ψ : B →ₐ[V] FractionRing V := φ.comp (Ideal.Quotient.mkₐ V q)
  have hψ : ∀ b, ψ b ∈ (⊥ : Subalgebra V (FractionRing V)) := by
    intro b
    rw [Algebra.mem_bot]
    obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.mp
      ((Algebra.IsIntegral.isIntegral (R := V) (Ideal.Quotient.mkₐ V q b)).map φ)
    exact ⟨y, hy⟩
  let e := Algebra.botEquivOfInjective hK
  let z : B →ₐ[V] V := e.toAlgHom.comp (ψ.codRestrict ⊥ hψ)
  have hz : ∀ b, algebraMap V (FractionRing V) (z b) = ψ b := by
    intro b
    have h1 := e.symm_apply_apply (ψ.codRestrict ⊥ hψ b)
    have h2 := e.symm.commutes (z b)
    have h3 : (algebraMap V V) (z b) = e (ψ.codRestrict ⊥ hψ b) := rfl
    rw [h3, h1] at h2
    have h4 := congrArg (fun s : (⊥ : Subalgebra V (FractionRing V)) => (s : FractionRing V)) h2
    simpa using h4.symm
  refine ⟨z, ?_⟩
  ext b
  have hc : b - algebraMap V B (z b) ∈ q := by
    have h0 : z (b - algebraMap V B (z b)) = 0 := by
      rw [map_sub, AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply, sub_self]
    have h1 : ψ (b - algebraMap V B (z b)) = 0 := by
      rw [← hz, h0, map_zero]
    have h2 : Ideal.Quotient.mkₐ V q (b - algebraMap V B (z b)) = 0 :=
      hφinj (by rw [map_zero]; exact h1)
    rwa [Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem] at h2
  have hm : χ (b - algebraMap V B (z b)) = 0 := hqm hc
  rw [map_sub, sub_eq_zero] at hm
  rw [hm, ← RingHom.comp_apply, hχ]
  rfl
