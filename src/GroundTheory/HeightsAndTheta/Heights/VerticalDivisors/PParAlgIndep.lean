module

public import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.IntToFracInjective
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Vertical

open MvPolynomial NumberField IsDedekindDomain

noncomputable section

attribute [local instance] MvPolynomial.algebraMvPolynomial

theorem eval_parYF_comp (K : Type*) [Field K] [NumberField K] (e n : ℕ) :
    (eval₂Hom (kToFrac K e n) (parYF K e n)).comp
        (algebraMap (MvPolynomial (Par e n) (𝓞 K)) (MvPolynomial (Par e n) K)) =
      algebraMap (MvPolynomial (Par e n) (𝓞 K)) (ParFrac K e n) := by
  refine MvPolynomial.ringHom_ext (fun x => ?_) (fun p => ?_)
  · simp only [RingHom.coe_comp, Function.comp_apply, MvPolynomial.algebraMap_def, map_C,
      eval₂Hom_C]
    rw [kToFrac, IsFractionRing.lift_algebraMap, RingHom.comp_apply]
  · simp [parYF]

theorem ParAlgIndep.proof : ParAlgIndep.Statement := by
  intro K _ _ e n
  let _ := (kToFrac K e n).toAlgebra
  rw [algebraicIndependent_iff_injective_aeval]
  change Function.Injective (eval₂Hom (kToFrac K e n) (parYF K e n))
  let M : Submonoid (MvPolynomial (Par e n) (𝓞 K)) := (nonZeroDivisors (𝓞 K)).map C
  rw [injective_iff_map_eq_zero]
  intro z hz
  obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective M z
  have h := IsLocalization.mk'_spec (MvPolynomial (Par e n) K) a s
  have hc := eval_parYF_comp K e n
  have ha : algebraMap (MvPolynomial (Par e n) (𝓞 K)) (ParFrac K e n) a = 0 := by
    rw [← hc, RingHom.comp_apply, ← h, map_mul, hz, zero_mul]
  have ha0 : a = 0 := IsFractionRing.injective _ _ (ha.trans (map_zero _).symm)
  subst ha0
  exact IsLocalization.mk'_zero _

end

end GroundTheory.Heights₂.Heights.Vertical
