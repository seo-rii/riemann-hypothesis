module

public import GroundTheory.LocalFields.LocalFourierChar
public import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import GroundTheory.LocalFields.LocalFourierHaar
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

namespace GroundTheory.LocalField

open ValuativeRel Topology Filter
open scoped WithZero Pointwise

section RatCircle

def ratAddCircleToReal : AddCircle (1 : ℚ) →+ AddCircle (1 : ℝ) :=
  QuotientAddGroup.map _ _ (Rat.castHom ℝ : ℚ →+* ℝ).toAddMonoidHom
    (AddSubgroup.zmultiples_le_of_mem (by
      rw [AddSubgroup.mem_comap]
      simp))

theorem ratAddCircleToReal_coe (q : ℚ) :
    ratAddCircleToReal (q : AddCircle (1 : ℚ)) = ((q : ℝ) : AddCircle (1 : ℝ)) := rfl

theorem ratAddCircleToReal_injective : Function.Injective ratAddCircleToReal := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  induction x using QuotientAddGroup.induction_on with
  | H q =>
    rw [ratAddCircleToReal_coe, AddCircle.coe_eq_zero_iff] at hx
    obtain ⟨n, hn⟩ := hx
    rw [QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_zmultiples_iff]
    refine ⟨n, ?_⟩
    have : ((n : ℚ) : ℝ) = (q : ℝ) := by simpa using hn
    simpa using (Rat.cast_injective this)

def ratCircleChar : AddChar (AddCircle (1 : ℚ)) Circle :=
  (AddCircle.toCircle_addChar (T := 1)).compAddMonoidHom ratAddCircleToReal

theorem ratCircleChar_injective : Function.Injective ratCircleChar :=
  (AddCircle.injective_toCircle one_ne_zero).comp ratAddCircleToReal_injective

theorem ratCircleChar_eq_one_iff {x : AddCircle (1 : ℚ)} : ratCircleChar x = 1 ↔ x = 0 := by
  constructor
  · intro h
    apply ratCircleChar_injective
    rw [h, AddChar.map_zero_eq_one]
  · rintro rfl
    exact AddChar.map_zero_eq_one _

end RatCircle

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

section Existence

theorem exists_mem_valBall_neg_one_notMem_valBall_zero :
    ∃ x : K, x ∈ valBall K (-1) ∧ x ∉ valBall K 0 := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[K]
  have h0 : (ϖ : K) ≠ 0 := fun h => hϖ.ne_zero (Subtype.ext h)
  have hi : (ϖ : K)⁻¹ ≠ 0 := inv_ne_zero h0
  refine ⟨(ϖ : K)⁻¹, ?_, ?_⟩
  · rw [mem_valBall_iff_le_ord hi, ord_inv h0, ord_uniformizer hϖ]
  · rw [mem_valBall_iff_le_ord hi, ord_inv h0, ord_uniformizer hϖ]
    omega

theorem continuous_of_isTrivialOn {χ : AddChar K Circle} {n : ℤ} (h : IsTrivialOn χ n) :
    Continuous χ := by
  have hlc : IsLocallyConstant χ := by
    rw [IsLocallyConstant.iff_exists_open]
    intro x
    refine ⟨{z | z - x ∈ valBall K n},
      (isOpen_valBall n).preimage (continuous_id.sub continuous_const), by simp, fun z hz => ?_⟩
    have e : x + (z - x) = z := by abel
    rw [← e, AddChar.map_add_eq_mul, h _ hz, mul_one]
  exact hlc.continuous

theorem exists_addChar_isTrivialOn_zero_not_isTrivialOn_neg_one :
    ∃ ψ : AddChar K Circle, IsTrivialOn ψ 0 ∧ ¬ IsTrivialOn ψ (-1) := by
  obtain ⟨x, hx1, hx0⟩ := exists_mem_valBall_neg_one_notMem_valBall_zero (K := K)
  let π : K →+ K ⧸ valBall K 0 := QuotientAddGroup.mk' (valBall K 0)
  have hπx : π x ≠ 0 := by
    rwa [Ne, QuotientAddGroup.mk'_apply, QuotientAddGroup.eq_zero_iff]
  obtain ⟨c, hc⟩ := CharacterModule.exists_character_apply_ne_zero_of_ne_zero hπx
  let ψ : AddChar K Circle :=
    ratCircleChar.compAddMonoidHom ((c : K ⧸ valBall K 0 →+ AddCircle (1 : ℚ)).comp π)
  have hψ : ∀ y, ψ y = ratCircleChar (c (π y)) := fun _ => rfl
  refine ⟨ψ, fun y hy => ?_, fun h => ?_⟩
  · have : π y = 0 := by
      rwa [QuotientAddGroup.mk'_apply, QuotientAddGroup.eq_zero_iff]
    rw [hψ, this, map_zero, AddChar.map_zero_eq_one]
  · exact hc (ratCircleChar_eq_one_iff.mp ((hψ x).symm.trans (h x hx1)))

theorem exists_addChar_addCharConductor_eq_zero :
    ∃ ψ : AddChar K Circle, Continuous ψ ∧ ψ ≠ 1 ∧ addCharConductor ψ = 0 := by
  obtain ⟨ψ, h0, h1⟩ := exists_addChar_isTrivialOn_zero_not_isTrivialOn_neg_one (K := K)
  have hc : Continuous ψ := continuous_of_isTrivialOn h0
  have hne : ψ ≠ 1 := by
    rintro rfl
    exact h1 fun _ _ => AddChar.one_apply _
  refine ⟨ψ, hc, hne, le_antisymm ((isTrivialOn_iff hc hne 0).mp h0) ?_⟩
  by_contra hlt
  exact h1 ((isTrivialOn_iff hc hne (-1)).mpr (by omega))

theorem exists_addChar_continuous_ne_one :
    ∃ ψ : AddChar K Circle, Continuous ψ ∧ ψ ≠ 1 := by
  obtain ⟨ψ, hc, hne, -⟩ := exists_addChar_addCharConductor_eq_zero (K := K)
  exact ⟨ψ, hc, hne⟩

end Existence

end GroundTheory.LocalField
