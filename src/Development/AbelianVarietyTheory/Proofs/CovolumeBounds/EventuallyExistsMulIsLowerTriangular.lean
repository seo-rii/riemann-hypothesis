module

public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.SumFinsuppAntidiagProdPowDivMultiFactorial
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsWeightedHomogeneousOfMemOrbitSpan
public import Mathlib.Analysis.Complex.Basic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
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
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open MvPolynomial Matrix Topology Filter
open GlobalTheory.MvPoly

namespace GlobalTheory.Harm

section Adjoint

variable {σ τ : Type*} [Fintype σ] [Fintype τ]

theorem pderiv_algHom_of_linear {R : Type*} [CommRing R]
    (G : MvPolynomial τ R →ₐ[R] MvPolynomial σ R) (M : σ → τ → R)
    (hG : ∀ j, G (X j) = ∑ i, M i j • X i) (i : σ) (Q : MvPolynomial τ R) :
    pderiv i (G Q) = ∑ j, M i j • G (pderiv j Q) := by
  classical
  induction Q using MvPolynomial.induction_on with
  | C r => simp [algHom_C]
  | add P Q hP hQ => simp [hP, hQ, Finset.sum_add_distrib]
  | mul_X P k hP =>
    have h1 : pderiv i (G (X k)) = C (M i k) := by
      simp [hG, pderiv_X, Pi.single_apply, smul_eq_C_mul]
    have h2 : ∑ j, M i j • G (P * pderiv j (X k)) = G P * C (M i k) := by
      rw [Finset.sum_eq_single k]
      · simp [smul_eq_C_mul, mul_comm]
      · intro j _ hj
        simp [pderiv_X, Pi.single_apply, hj.symm]
      · simp
    rw [map_mul, Derivation.leibniz, hP, h1, smul_eq_mul, smul_eq_mul, ← h2, Finset.mul_sum,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Derivation.leibniz, map_add (f := _), smul_add, smul_eq_mul, smul_eq_mul, map_mul G (X k),
      mul_smul_comm]


omit [Fintype τ] in
theorem constantCoeff_algHom_of_linear {R : Type*} [CommRing R]
    (G : MvPolynomial τ R →ₐ[R] MvPolynomial σ R) (M : σ → τ → R)
    (hG : ∀ j, G (X j) = ∑ i, M i j • X i) (Q : MvPolynomial τ R) :
    constantCoeff (G Q) = constantCoeff Q := by
  induction Q using MvPolynomial.induction_on with
  | C r => simp [algHom_C]
  | add P Q hP hQ => simp [hP, hQ]
  | mul_X P k hP => simp [hG, smul_eq_C_mul]

theorem fockInner_algHom_of_linear (F : MvPolynomial σ ℂ →ₐ[ℂ] MvPolynomial τ ℂ)
    (G : MvPolynomial τ ℂ →ₐ[ℂ] MvPolynomial σ ℂ) (M : σ → τ → ℂ)
    (hF : ∀ i, F (X i) = ∑ j, M i j • X j) (hG : ∀ j, G (X j) = ∑ i, star (M i j) • X i)
    (P : MvPolynomial σ ℂ) (Q : MvPolynomial τ ℂ) : fockInner (F P) Q = fockInner P (G Q) := by
  induction P using MvPolynomial.induction_on generalizing Q with
  | C r =>
    have := constantCoeff_algHom_of_linear G _ hG Q
    rw [constantCoeff_eq] at this
    rw [algHom_C, algebraMap_eq, C_apply, C_apply, fockInner_monomial_left,
      fockInner_monomial_left, this]
    simp [constantCoeff_eq]
  | add P P' hP hP' => rw [map_add (f := _), fockInner_add_left, fockInner_add_left, hP, hP']
  | mul_X P k hP =>

    rw [mul_comm P, fockInner_X_mul_left, pderiv_algHom_of_linear G _ hG, map_mul, hF,
    Finset.sum_mul, ← fockInnerₛₗ_apply, ← fockInnerₛₗ_apply, map_sum, map_sum,
    LinearMap.sum_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [fockInnerₛₗ_apply, fockInnerₛₗ_apply, smul_mul_assoc, fockInner_smul_left,
      fockInner_smul_right, fockInner_X_mul_left, hP]
    simp

variable {T κ : Type*} [Fintype T] [Fintype κ] {p q : ℕ}

theorem fockInner_colSubst (A B : T → Matrix κ κ ℂ) (P Q : Poly ℂ T p q κ) :
    fockInner (colSubst A B P) Q =
      fockInner P (colSubst (fun t => (A t)ᴴ) (fun t => (B t)ᴴ) Q) := by
  classical
  refine fockInner_algHom_of_linear _ _ (fun v w => if v.1 = w.1 ∧ v.2.1 = w.2.1 then
    Sum.elim (fun _ => A v.1 v.2.2 w.2.2) (fun _ => B v.1 w.2.2 v.2.2) v.2.1 else 0) ?_ ?_ P Q
  · rintro ⟨t, a | b, k⟩
    · rw [colSubst_X_xVar, xForm_apply]
      simp [Fintype.sum_prod_type, ite_and, smul_eq_C_mul, apply_ite C]
    · rw [colSubst_X_yVar, yForm_apply]
      simp [Fintype.sum_prod_type, ite_and, smul_eq_C_mul, apply_ite C]
  · rintro ⟨t, a | b, k⟩
    · rw [colSubst_X_xVar, xForm_apply]
      simp [Fintype.sum_prod_type, ite_and, smul_eq_C_mul, apply_ite C, apply_ite star]
    · rw [colSubst_X_yVar, yForm_apply]
      simp [Fintype.sum_prod_type, ite_and, smul_eq_C_mul, apply_ite C, apply_ite star]

theorem fockInner_colAct [DecidableEq κ] (g : T → GL κ ℂ) (P Q : Poly ℂ T p q κ) :
    fockInner (colAct ℂ T p q κ g P) Q = fockInner P (colAct ℂ T p q κ (star g) Q) := by
  rw [colAct_apply, colAct_apply, fockInner_colSubst]
  rfl

theorem exists_fockInner_sub_eq_zero {σ : Type*} (W : Submodule ℂ (MvPolynomial σ ℂ))
    [FiniteDimensional ℂ W] (P : MvPolynomial σ ℂ) :
    ∃ Q ∈ W, ∀ w ∈ W, fockInner (P - Q) w = 0 := by
  let b := Module.finBasis ℂ W
  let L : MvPolynomial σ ℂ →ₗ[ℂ] (Fin (Module.finrank ℂ W) → ℂ) :=
    LinearMap.pi fun i => (fockInnerₛₗ σ ℂ).flip (b i)
  have hL (P) (h : L P = 0) (w) (hw : w ∈ W) : fockInner P w = 0 := by
    have := congrArg W.subtype (b.sum_repr ⟨w, hw⟩)

    rw [map_sum, Submodule.subtype_apply] at this
    change _ = w at this

    rw [← this, ← fockInnerₛₗ_apply, map_sum]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [map_smul, fockInnerₛₗ_apply, fockInner_smul_right]
    exact mul_eq_zero_of_right _ (congrFun h i)
  have hinj : Function.Injective (L ∘ₗ W.subtype) := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    have := hL x hx x x.2
    rw [fockInner_self] at this
    exact Subtype.ext (fockNormSq_eq_zero.mp (RCLike.ofReal_eq_zero.mp this))
  obtain ⟨x, hx⟩ := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (by simp)).mp hinj
    (L P)
  exact ⟨x, x.2, hL _ (by rw [map_sub, ← hx]; simp)⟩

end Adjoint

section Triangular

variable {R : Type*} [CommRing R] {T : Type*} [Fintype T] {p q n : ℕ}

end Triangular

section Density

variable {T κ : Type*} [Fintype κ] {p q n : ℕ}

end Density

end GlobalTheory.Harm
