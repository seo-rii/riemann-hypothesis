module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsSumMonomialAdd
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BdRPlusIsDomainBdRIsField
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NonemptyLocalPeriodRingsData
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
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotential

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.TensorOneInj

theorem bcris_nontrivial (l : ℕ) [Fact l.Prime] : Nontrivial (Per.Bcris l) := by
  obtain ⟨C⟩ := GlobalTheory.MemLoc.nonempty_core l
  have : Nontrivial (Per.BdR l) := (GlobalTheory.MemLoc.BdRField.bdR_isField l).2.2.1.nontrivial
  exact C.ι.domain_nontrivial

theorem algebraMap_injective (l : ℕ) [Fact l.Prime] :
    Function.Injective (algebraMap ℤ_[l] (Per.Bcris l)) := by
  have := bcris_nontrivial l
  rw [injective_iff_map_eq_zero]
  intro x hx
  by_contra h0
  rw [PadicInt.unitCoeff_spec h0, map_mul, map_pow, map_natCast] at hx
  have hu : IsUnit (algebraMap ℤ_[l] (Per.Bcris l) (PadicInt.unitCoeff h0 : ℤ_[l])) :=
    (PadicInt.unitCoeff h0).isUnit.map _
  exact (hu.mul ((GlobalTheory.MemLoc.isUnit_l_Bcris l).pow _)).ne_zero hx

theorem algebraMap_OB_injective (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [Algebra ℤ_[l] O]
    [Module.Flat ℤ_[l] O] : Function.Injective (algebraMap O (OB l O)) := by
  have h := Module.Flat.lTensor_preserves_injective_linearMap (M := O)
    (Algebra.linearMap ℤ_[l] (Per.Bcris l)) (algebraMap_injective l)
  have e : ⇑(algebraMap O (OB l O)) =
      (LinearMap.lTensor O (Algebra.linearMap ℤ_[l] (Per.Bcris l))) ∘ (TensorProduct.rid ℤ_[l] O).symm := by
    funext o
    simp [Algebra.TensorProduct.algebraMap_apply]
  rw [e]
  exact h.comp (TensorProduct.rid ℤ_[l] O).symm.injective

theorem tensor_one_injective : ∀ (l : ℕ) [Fact l.Prime] (O K : Type) [CommRing O] [Algebra ℤ_[l] O]
    [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [Algebra O K] [IsUnitBall O K]
    [NormedAlgebra ℚ_[l] K] (G : Type) [Group G] [TopologicalSpace G] (T : LocLat G ℚ_[l] K O),
    Function.Injective fun x : ↥T.L.T => (1 : OB l O) ⊗ₜ[O] x := by
  intro l _ O K _ _ _ _ _ _ _ _ G _ _ T
  haveI : Module.Free O ↥T.L.T := T.L.free
  have h := Module.Flat.rTensor_preserves_injective_linearMap (M := ↥T.L.T)
    (Algebra.linearMap O (OB l O)) (algebraMap_OB_injective l O)
  have e : (fun x : ↥T.L.T => (1 : OB l O) ⊗ₜ[O] x) =
      (LinearMap.rTensor (↥T.L.T) (Algebra.linearMap O (OB l O))) ∘ (TensorProduct.lid O ↥T.L.T).symm := by
    funext x
    simp [Algebra.TensorProduct.one_def]
  rw [e]
  exact h.comp (TensorProduct.lid O ↥T.L.T).symm.injective

end GlobalTheory.TensorOneInj
