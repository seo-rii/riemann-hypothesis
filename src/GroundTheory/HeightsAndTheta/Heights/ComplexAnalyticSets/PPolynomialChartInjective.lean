module

public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StPolynomialChartInjective
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PNormalCurveRegularPoint
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Analytic.Polynomial
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial Topology

noncomputable section

theorem PolynomialChartInjective.full : PolynomialChartInjective.Statement := by
  classical
  intro σ _ k t f w hk hlin
  set g : Fin (k + 1) → MvPolynomial σ ℂ := Fin.cons t f with hg
  set F : (σ → ℂ) → Fin (k + 1) → ℂ := fun z j ↦ eval z (g j) with hF
  set L : (σ → ℂ) →L[ℂ] (Fin (k + 1) → ℂ) :=
    ContinuousLinearMap.pi fun j ↦ fderiv ℂ (fun z : σ → ℂ ↦ eval z (g j)) w with hL
  have hFL : HasStrictFDerivAt F L w := hasStrictFDerivAt_pi.2 fun j ↦
    (AnalyticOnNhd.eval_mvPolynomial (𝕜 := ℂ) (g j) w trivial).hasStrictFDerivAt
  set r : Fin (k + 1) → σ → ℂ :=
    Fin.cons (fun i ↦ eval w (pderiv i t)) (fun j i ↦ eval w (pderiv i (f j))) with hr
  have hrow : ∀ j i, fderiv ℂ (fun z : σ → ℂ ↦ eval z (g j)) w (Pi.single i 1) = r j i := by
    intro j i
    rw [NormalCurveRegularPoint.fderiv_eval_single]
    refine Fin.cases ?_ (fun j ↦ ?_) j <;> simp [g, r]
  have hspan : Submodule.span ℂ (Set.range r) = ⊤ :=
    hlin.span_eq_top_of_card_eq_finrank' (by simp [Module.finrank_fintype_fun_eq_card, hk])
  have hinj : Function.Injective L := by
    rw [injective_iff_map_eq_zero]
    intro v hv
    let ψ : (σ → ℂ) →ₗ[ℂ] ℂ :=
      { toFun := fun u ↦ ∑ i, u i * v i
        map_add' := fun a b ↦ by simp [add_mul, Finset.sum_add_distrib]
        map_smul' := fun c a ↦ by simp [Finset.mul_sum, mul_assoc] }
    have hker : Submodule.span ℂ (Set.range r) ≤ LinearMap.ker ψ := by
      rw [Submodule.span_le]
      rintro _ ⟨j, rfl⟩
      have h0 := congrFun hv j
      simp only [hL, ContinuousLinearMap.pi_apply, Pi.zero_apply] at h0

      rw [pi_eq_sum_univ' v, map_sum] at h0
      simp only [map_smul, smul_eq_mul, hrow] at h0
      simpa [ψ, mul_comm] using h0
    rw [hspan] at hker
    funext i
    have := hker (Submodule.mem_top (x := Pi.single i 1))
    simpa [ψ, Pi.single_apply] using this
  let e : (σ → ℂ) ≃L[ℂ] (Fin (k + 1) → ℂ) :=
    (LinearMap.linearEquivOfInjective L.toLinearMap hinj
      (by simp [Module.finrank_fintype_fun_eq_card, hk])).toContinuousLinearEquiv
  have hFe : HasStrictFDerivAt F (e : (σ → ℂ) →L[ℂ] (Fin (k + 1) → ℂ)) w := by
    convert hFL using 1
    ext v : 1
    rfl
  refine ⟨_, hFe.eventually_left_inverse, fun x hx y hy hxy ↦ ?_⟩
  have hFxy : F x = F y := by
    funext j
    refine Fin.cases ?_ (fun j ↦ ?_) j
    · simpa [F, g] using hxy
    · simp only [F, g, Fin.cons_succ, hx.2 j, hy.2 j]
  rw [← hx.1, ← hy.1, hFxy]

end

end GroundTheory.Heights₂.Heights
