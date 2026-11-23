module

public import Development.AbelianVarietyTheory.Definitions.Foundations.IsHermND
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsEqZpowMulUnit
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsPrincipalIdealRingOfHenselian
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RelativeLatticeVolumeOfDetValuation
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TupleJacobianRightMulIsometry
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
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
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.HermLat

@[expose] public section

open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.FrameIndex

theorem relIndex_span_matrix : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ ϖ : 𝒪[F], Irreducible ϖ → ∀ {n m : ℕ} (b : Fin m → Fin n → E), LinearIndependent E b → ∀ (A : Matrix (Fin m) (Fin m) E) (c : F), c ≠ 0 → A.det * L.cj A.det = algebraMap F E c → ∀ Q Q' : Submodule L.O (Fin n → E), Q = Submodule.span L.O (Set.range b) → Q' = Submodule.span L.O (Set.range fun j => ∑ i, A i j • b i) → Q'.toAddSubgroup.relIndex Q.toAddSubgroup ≠ 0 ∧ Q.toAddSubgroup.relIndex Q'.toAddSubgroup ≠ 0 ∧ (Q'.toAddSubgroup.relIndex Q.toAddSubgroup : ℝ) = (resQ ϖ : ℝ) ^ (vE L ϖ (algebraMap F E c)) * (Q.toAddSubgroup.relIndex Q'.toAddSubgroup : ℝ) := by
  intro F _ _ _ _ _ E _ _ _ L ϖ hϖ n m b hb A c hc0 hA Q Q' hQ hQ'
  obtain ⟨c2, hc, hN⟩ := TupleJac.exists_int_basis L
  have := L.free
  obtain ⟨u, hu⟩ := (GlobalTheory.UnramVal.vE_valuation L ϖ hϖ).2.2.2 c hc0
  have hAu : IsUnit A.det := by
    have h := (IsUnit.mk0 c hc0).map (algebraMap F E)
    rw [← hA] at h
    exact isUnit_of_mul_isUnit_left h
  have hdet : IsUnit (LinearMap.det (Matrix.toLin' A)) := by
    rw [LinearMap.det_toLin']; exact hAu
  set φ := LinearMap.equivOfIsUnitDet hdet with hφdef
  have hφ : φ.toLinearMap = Matrix.toLin' A := LinearMap.coe_equivOfIsUnitDet hdet
  have hφx : ∀ x, φ x = A.mulVec x := fun x => LinearMap.congr_fun hφ x
  let W0 : AddSubgroup (Fin m → E) := AddSubgroup.pi Set.univ fun _ => L.O.toAddSubgroup
  have hW0 : ∀ x, x ∈ W0 ↔ ∀ i, x i ∈ L.O := fun x => by
    simp only [W0, AddSubgroup.mem_pi, Set.mem_univ, true_imp_iff, Subring.mem_toAddSubgroup]
  have h := LatDet.relVol_map ϖ hϖ (c2.smulTower (Pi.basisFun E (Fin m))) (φ.restrictScalars F)
    (vE L ϖ (algebraMap F E c)) u
    (by
      apply GlobalTheory.UnramOrder.algebraMap_inj L
      rw [← hu, ← hA, ← hN, ← LinearMap.det_toLin', ← hφ, ← LinearMap.det_restrictScalars]
      rfl) W0 (by
      intro x
      simp only [hW0, hc, Module.Basis.smulTower_repr, Pi.basisFun_repr]
      exact ⟨fun h i => h _ _, fun h j i => h (i, j)⟩)
  let e : (Fin m → E) →+ (Fin n → E) := (Fintype.linearCombination E b).toAddMonoidHom
  have he : ∀ x, e x = ∑ i, x i • b i := fun x => Fintype.linearCombination_apply E b x
  have hei : Function.Injective e := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    exact funext (Fintype.linearIndependent_iff.1 hb x ((he x).symm.trans hx))
  have h1 : Q.toAddSubgroup = W0.map e := by
    ext w
    rw [hQ, Submodule.mem_toAddSubgroup, Submodule.mem_span_range_iff_exists_fun,
      AddSubgroup.mem_map]
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨fun i => x i, (hW0 _).2 fun i => (x i).2, he _⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨fun i => ⟨x i, (hW0 _).1 hx i⟩, (he _).symm⟩
  have hsum : ∀ x : Fin m → E, e (φ x) = ∑ j, x j • ∑ i, A i j • b i := by
    intro x
    rw [he, hφx]
    simp only [Matrix.mulVec, dotProduct, Finset.sum_smul, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    simp only [mul_comm]
  have h2 : Q'.toAddSubgroup =
      (W0.map (φ.restrictScalars F).toAddEquiv.toAddMonoidHom).map e := by
    ext w
    rw [hQ', Submodule.mem_toAddSubgroup, Submodule.mem_span_range_iff_exists_fun,
      AddSubgroup.mem_map]
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨_, ⟨fun i => x i, (hW0 _).2 fun i => (x i).2, rfl⟩, hsum _⟩
    · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
      exact ⟨fun i => ⟨x i, (hW0 _).1 hx i⟩, (hsum _).symm⟩
  rw [h1, h2, AddSubgroup.relIndex_map_map_of_injective _ _ hei,
    AddSubgroup.relIndex_map_map_of_injective _ _ hei]
  obtain ⟨n1, n2, h3⟩ := h
  refine ⟨n1, n2, ?_⟩
  unfold relVol at h3
  have hq : (resQ ϖ : ℝ) ≠ 0 := by exact_mod_cast LatDet.resQ_ne_zero hϖ
  rw [div_eq_iff (by exact_mod_cast n1)] at h3
  rw [h3, ← mul_assoc, ← zpow_add₀ hq, add_neg_cancel, zpow_zero, one_mul]

end GlobalTheory.HL.FrameIndex
