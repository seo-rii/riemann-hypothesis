module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.OrbitVanishingLocal
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
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.GradedModulesLength.ToDegInjective
import Formalism.SharpRestriction.ValuationFrobeniusEpsilon.LeastPrimeTwists.QuotientShiftIrreducible.NoetherianQuotientCalc.EulerVanishingBelowDimension
public import Mathlib.RingTheory.DedekindDomain.Basic

@[expose] public section

open IsLocalRing Filter Formalism.MainNotions.V.Pf.V2.Calc UpperTheory.V.Alg UpperTheory.V.Alg.M

private theorem prime_maximal_or_kernel (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (K : Type) [Field K] [Algebra O K] [IsAlgClosed K] [FaithfulSMul O K]
    (B : Type) [CommRing B] [Algebra O B] [IsLocalRing B] (P : Ideal B) [hP : P.IsPrime]
    [Module.Finite O (B ⧸ P)] :
    P = maximalIdeal B ∨ ((∀ c : O, c ≠ 0 → algebraMap O B c ∉ P) ∧ ∃ σ : B →ₐ[O] K, RingHom.ker σ = P) := by
  classical
  haveI : Algebra.IsIntegral O (B ⧸ P) := Algebra.IsIntegral.of_finite O (B ⧸ P)
  have hcomap : ∀ a : O, algebraMap O (B ⧸ P) a = 0 ↔ algebraMap O B a ∈ P := by
    intro a
    rw [IsScalarTower.algebraMap_apply O B (B ⧸ P), Ideal.Quotient.algebraMap_eq, Ideal.Quotient.eq_zero_iff_mem]
  by_cases hc : ∃ c : O, c ≠ 0 ∧ algebraMap O B c ∈ P
  · obtain ⟨c, hc0, hcP⟩ := hc
    left
    apply IsLocalRing.eq_maximalIdeal
    have hQ : (P.comap (algebraMap O B)).IsMaximal := by
      apply Ideal.IsPrime.isMaximal (Ideal.comap_isPrime _ _)
      intro h
      have hmem : c ∈ P.comap (algebraMap O B) := hcP
      rw [h] at hmem
      exact hc0 ((Submodule.mem_bot O).1 hmem)
    have hbot : (⊥ : Ideal (B ⧸ P)).comap (algebraMap O (B ⧸ P)) = P.comap (algebraMap O B) := by
      ext a
      rw [Ideal.mem_comap, Ideal.mem_bot, Ideal.mem_comap, hcomap]
    haveI : (⊥ : Ideal (B ⧸ P)).IsPrime := Ideal.isPrime_bot
    have hmax := Ideal.isMaximal_of_isIntegral_of_isMaximal_under (R := O) (⊥ : Ideal (B ⧸ P)) (by
      change ((⊥ : Ideal (B ⧸ P)).comap (algebraMap O (B ⧸ P))).IsMaximal
      rw [hbot]
      exact hQ)
    rw [Ideal.Quotient.maximal_ideal_iff_isField_quotient]
    exact Ring.isField_iff_maximal_bot.2 hmax
  · push_neg at hc
    right
    refine ⟨hc, ?_⟩
    have hinj : Function.Injective (algebraMap O (B ⧸ P)) := by
      rw [injective_iff_map_eq_zero]
      intro a ha
      by_contra h0
      exact hc a h0 ((hcomap a).1 ha)
    haveI : Module.IsTorsionFree O (B ⧸ P) := Module.isTorsionFree_iff_algebraMap_injective.2 hinj
    haveI : Module.IsTorsionFree O K :=
      Module.isTorsionFree_iff_algebraMap_injective.2 (FaithfulSMul.algebraMap_injective O K)
    haveI : Algebra.IsAlgebraic O (B ⧸ P) := Algebra.IsIntegral.isAlgebraic
    let τ : (B ⧸ P) →ₐ[O] K := (by
      refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
      solve_by_elim* (maxDepth := 2) only [*,
        @_root_.DivisionSemiring.to_moduleIsTorsionFree,
        @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
    refine ⟨τ.comp (Ideal.Quotient.mkₐ O P), ?_⟩
    have hτ : RingHom.ker (τ : (B ⧸ P) →+* K) = ⊥ := by
      apply Ideal.eq_bot_of_comap_eq_bot (R := O)
      ext a
      rw [Ideal.mem_comap, RingHom.mem_ker, Ideal.mem_bot]
      change τ (algebraMap O (B ⧸ P) a) = 0 ↔ a = 0
      rw [AlgHom.commutes]
      constructor
      · intro h
        exact FaithfulSMul.algebraMap_injective O K (h.trans (map_zero _).symm)
      · intro h
        rw [h, map_zero]
    have hτi : Function.Injective τ := (RingHom.injective_iff_ker_eq_bot (τ : (B ⧸ P) →+* K)).2 hτ
    ext b
    rw [RingHom.mem_ker]
    change τ (Ideal.Quotient.mk P b) = 0 ↔ b ∈ P
    rw [map_eq_zero_iff τ hτi, Ideal.Quotient.eq_zero_iff_mem]

theorem UpperTheory.V.Alg.M.emb_holds :
    ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (maximalIdeal O) O] [CharZero O]
      (K : Type) [Field K] [Algebra O K] [IsAlgClosed K] [FaithfulSMul O K]
      (A : Type) [CommRing A] [Algebra O A] (𝒜 : ℤ → Submodule O A) [GradedAlgebra 𝒜] [IsCO O (𝒜 0)] (x : A →ₐ[O] O) (I : Ideal A), M2 𝒜 I →
    ∀ P : Ideal (𝒜 0), P.IsPrime → (∀ b : 𝒜 0, (b : A) ∈ I → b ∈ P) →
      (P = maximalIdeal (𝒜 0) ∨ ((∀ c : O, c ≠ 0 → algebraMap O (𝒜 0) c ∉ P) ∧ ∃ σ : 𝒜 0 →ₐ[O] K, RingHom.ker σ = P)) := by
  intro O _ _ _ _ _ K _ _ _ _ A _ _ 𝒜 _ _ x I hM P hP hIP
  let φ : 𝒜 0 →ₗ[O] A ⧸ I := (Ideal.Quotient.mkₐ O I).toLinearMap ∘ₗ (𝒜 0).subtype
  have hr : (LinearMap.range φ).FG := by
    have : LinearMap.range φ = (𝒜 0).map (Ideal.Quotient.mkₐ O I).toLinearMap := by
      rw [LinearMap.range_comp, Submodule.range_subtype]
    rw [this]; exact hM
  haveI : Module.Finite O (LinearMap.range φ) := Module.Finite.iff_fg.2 hr
  haveI : Module.Finite O (𝒜 0 ⧸ LinearMap.ker φ) := Module.Finite.equiv φ.quotKerEquivRange.symm
  let ψ : 𝒜 0 →ₗ[O] (𝒜 0 ⧸ P) := (Ideal.Quotient.mkₐ O P).toLinearMap
  have hk : LinearMap.ker φ ≤ LinearMap.ker ψ := fun b hb =>
    Ideal.Quotient.eq_zero_iff_mem.2 (hIP b (Ideal.Quotient.eq_zero_iff_mem.1 hb))
  haveI : Module.Finite O (𝒜 0 ⧸ P) := by
    refine Module.Finite.of_surjective ((LinearMap.ker φ).liftQ ψ hk) fun y => ?_
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective y
    exact ⟨Submodule.Quotient.mk b, rfl⟩
  exact prime_maximal_or_kernel O K (𝒜 0) P
