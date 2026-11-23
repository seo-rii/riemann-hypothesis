module

public import Formalism.FilteredPoleLength.ReducedBasisBounds.LengthBaseChangeLocal
public import Mathlib.RingTheory.Flat.Basic
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
public import Mathlib.RingTheory.OrderOfVanishing.Noetherian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import Mathlib.Topology.Sheaves.Init
import Formalism.FilteredPoleLength.LocalDescentLevels.MemSpanBasisFun
public import Mathlib.FieldTheory.Separable
public import Mathlib.RingTheory.OrderOfVanishing.Basic

@[expose] public section

noncomputable section

namespace Formalism.LatticeBaseChangeAlt

open Module TensorProduct

namespace LengthBaseChangeAlt

theorem length_baseChange_eq_mul {O O₁ : Type} [CommRing O] [CommRing O₁] [Algebra O O₁]
    [Module.Flat O O₁] (ε : ℕ∞)
    (hs : ∀ (S : Type) [AddCommGroup S] [Module O S], IsSimpleModule O S →
      Module.length O₁ (TensorProduct O O₁ S) = ε)
    (Q : Type) [AddCommGroup Q] [Module O Q] (h : IsFiniteLength O Q) :
    Module.length O₁ (TensorProduct O O₁ Q) = ε * Module.length O Q := by
  induction h with
  | of_subsingleton =>
    rw [Module.length_eq_zero (R := O), mul_zero, Module.length_eq_zero_iff]
    refine ⟨fun x y => ?_⟩
    rw [← sub_eq_zero]
    generalize x - y = z
    induction z using TensorProduct.induction_on with
    | zero => rfl
    | tmul a b => rw [Subsingleton.elim b 0, TensorProduct.tmul_zero]
    | add u v hu hv => rw [hu, hv, add_zero]
  | of_simple_quotient hN ih =>
    rename_i M _ _ N hS
    have e1 := Module.length_eq_add_of_exact N.subtype N.mkQ N.injective_subtype N.mkQ_surjective
      (LinearMap.exact_subtype_mkQ N)
    have e2 := Module.length_eq_add_of_exact ((N.subtype).baseChange O₁) ((N.mkQ).baseChange O₁)
      (by
        rw [LinearMap.baseChange_eq_ltensor]
        exact Module.Flat.lTensor_preserves_injective_linearMap (M := O₁) _ N.injective_subtype)
      (by
        rw [LinearMap.baseChange_eq_ltensor]
        exact LinearMap.lTensor_surjective O₁ N.mkQ_surjective)
      (by
        rw [LinearMap.baseChange_eq_ltensor, LinearMap.baseChange_eq_ltensor]
        exact Module.Flat.lTensor_exact (M := O₁) (LinearMap.exact_subtype_mkQ N))
    rw [e1, e2, ih, hs _ hS, Module.length_eq_one_iff.mpr hS]
    ring

end LengthBaseChangeAlt

theorem lengthBaseChangeLocal : LengthBaseChangeLocal := by
  intro O O₁ Q _ _ _ _ _ _ _ _ _ ϖ ϖ₁ u ε hϖ hϖ₁ hu hQ
  have hinj : Function.Injective (algebraMap O O₁) := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    by_contra hx0
    obtain ⟨k, v, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hx0 hϖ
    rw [map_mul, map_pow, hu] at hx
    rcases mul_eq_zero.1 hx with h | h
    · exact ((v.isUnit.map (algebraMap O O₁)).ne_zero) h
    · exact (pow_ne_zero _ (mul_ne_zero u.ne_zero (pow_ne_zero _ hϖ₁.ne_zero))) h
  have : Module.IsTorsionFree O O₁ := Module.isTorsionFree_iff_algebraMap_injective.2 hinj
  have : Module.Flat O O₁ := inferInstance
  rw [Module.length_ne_top_iff] at hQ
  refine LengthBaseChangeAlt.length_baseChange_eq_mul (ε : ℕ∞) ?_ Q hQ
  intro S _ _ hS
  obtain ⟨m, hm, ⟨e⟩⟩ := isSimpleModule_iff_quot_maximal.mp hS
  obtain rfl := IsLocalRing.eq_maximalIdeal hm
  rw [(TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl O₁ O₁) e).length_eq,
    ← (Algebra.TensorProduct.quotIdealMapEquivTensorQuot O₁
      (IsLocalRing.maximalIdeal O)).toLinearEquiv.length_eq,
    hϖ.maximalIdeal_eq, Ideal.map_span, Set.image_singleton, hu]
  change Ring.ord O₁ _ = _
  rw [Ring.ord_eq_addVal, IsDiscreteValuationRing.addVal_mul, IsDiscreteValuationRing.addVal_pow,
    IsDiscreteValuationRing.addVal_uniformizer hϖ₁]
  simp

namespace LengthBaseChangeAlt

open BQuot

section Ext

variable {O K K₁ V : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K]
  [Algebra O K] [IsFractionRing O K] [Field K₁] [Algebra K K₁] [FiniteDimensional K K₁]
  [Algebra.IsSeparable K K₁] [Algebra O K₁] [IsScalarTower O K K₁]
  [AddCommGroup V] [Module K V] [Module O V] [IsScalarTower O K V]

end Ext

end LengthBaseChangeAlt


end Formalism.LatticeBaseChangeAlt
