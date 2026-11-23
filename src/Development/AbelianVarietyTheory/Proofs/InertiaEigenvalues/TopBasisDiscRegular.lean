module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinNormEisensteinLeRadiusStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ClosedDiscCoefficientsTopologicallyFreeStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ClosedDiscToDiscInjectiveOfAdicBasisStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EisensteinDivClosedDiscOfTopBasisStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TopologicalBasisBasicFactsStatement
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
import Mathlib.RingTheory.PowerSeries.NoZeroDivisors
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP

theorem topBasis_disc_regular : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (A : Type) [CommRing A] (s : bk.S →+* A) (ι : Type), TopBasis s bk.J ι → Function.Injective (toDisc l (s X) bk.ρ₀) ∧ toDisc l (s X) bk.ρ₀ (s bk.E) ∈ nonZeroDivisors (Disc l (s X) bk.ρ₀) ∧ (l : A) ∈ nonZeroDivisors A ∧ ∀ F : bk.DS bk.ρ₀ →+* Disc l (s X) bk.ρ₀, IsDiscMap (l := _) (u := _) (ρ := _) s F → Function.Injective F := by
  intro l _ K bk A _ s ι TB
  obtain ⟨h0, h1, -, -⟩ := GlobalTheory.T.breuilKisin_norm_eisenstein_le_radius l K bk A s
  refine ⟨(GlobalTheory.T.closedDisc_toDisc_injective_of_adicBasis l K bk A s ι TB bk.ρ₀ h0 h1).1, ?_, ?_, ?_⟩
  · rw [mem_nonZeroDivisors_iff_right]
    intro y hy
    have hn := (GlobalTheory.T.eisenstein_div_closedDisc_of_topBasis l K bk A s ι TB bk.ρ₀ le_rfl h1).1 y
    rw [mul_comm, hy, norm_zero] at hn
    have hp : (0 : ℝ) < (bk.ρ₀ : ℝ) ^ bk.Ep.natDegree := pow_pos (by exact_mod_cast h0) _
    exact norm_eq_zero.1 ((mul_eq_zero.1 hn.symm).resolve_left hp.ne')
  · have hH : IsHausdorff bk.J bk.S := bk.complete.toIsHausdorff
    have hF := GlobalTheory.T.topologicalBasis_basic_facts bk.S A s bk.J ι TB hH
    have hW : ((l : ℕ) : Wq l bk.a) ≠ 0 := by
      intro h
      have h2 := congrArg (fun w : Wq l bk.a => w.coeff 1) h
      simp only [WittVector.coeff_p_one, WittVector.zero_coeff] at h2
      exact one_ne_zero h2
    have hS : ((l : ℕ) : bk.S) ≠ 0 := by
      intro h
      have h2 := congrArg (PowerSeries.constantCoeff) h
      rw [map_natCast, map_zero] at h2
      exact hW h2
    have := hF.2.2.2.2 _ (mem_nonZeroDivisors_of_ne_zero hS)
    rwa [map_natCast] at this
  · intro F hF
    obtain ⟨_, -, -, -, -, -, -, -, hnorm⟩ := GlobalTheory.T.closedDisc_coefficients_topologicallyFree l K bk A s ι TB bk.ρ₀ h0 h1 F hF
    rw [injective_iff_map_eq_zero]
    intro x hx
    have h := hnorm x
    rw [hx, norm_zero] at h
    exact norm_eq_zero.1 h.symm

end GlobalTheory.BSP
