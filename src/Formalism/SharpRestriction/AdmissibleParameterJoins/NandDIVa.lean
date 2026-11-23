module

public import Mathlib.Algebra.DirectSum.Basic
public import Mathlib.Algebra.Module.Submodule.Lattice
public import Mathlib.Basic.Complex.Basic
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
import Mathlib.RingTheory.SimpleRing.Principal
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
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
public import Mathlib.Algebra.DirectSum.Decomposition

@[expose] public section

noncomputable section

namespace Formalism.MainNotions.J

open Formalism.BasicNotions

theorem injective_of_scalars {ι V W : Type*} [DecidableEq ι] [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] (S : ι → Submodule ℂ V) (hS : DirectSum.IsInternal S)
    (A : V →ₗ[ℂ] W) (B : W →ₗ[ℂ] V)
    (h : ∀ σ, S σ ≠ ⊥ → ∃ lam : ℂ, lam ≠ 0 ∧ ∀ f ∈ S σ, B (A f) = lam • f) :
    Function.Injective A := by
  classical
  have h' : ∀ σ, ∃ lam : ℂ, lam ≠ 0 ∧ ∀ f ∈ S σ, B (A f) = lam • f := by
    intro σ
    by_cases hσ : S σ = ⊥
    · refine ⟨1, one_ne_zero, fun f hf => ?_⟩
      rw [hσ, Submodule.mem_bot] at hf
      simp [hf]
    · exact h σ hσ
  choose c hc0 hc using h'
  let _ := hS.chooseDecomposition
  have key : ∀ v : V, ∀ k, ((DirectSum.decompose S (B (A v)) k : S k) : V) =
      c k • ((DirectSum.decompose S v k : S k) : V) := by
    intro v
    induction v using DirectSum.Decomposition.inductionOn S with
    | zero => intro k; simp
    | @homogeneous i m =>
      intro k
      have hm : B (A (m : V)) ∈ S i := by
        rw [hc i _ m.2]; exact (S i).smul_mem _ m.2
      by_cases hik : i = k
      · subst hik
        rw [DirectSum.decompose_of_mem_same S hm, DirectSum.decompose_of_mem_same S m.2, hc i _ m.2]
      · rw [DirectSum.decompose_of_mem_ne S hm hik, DirectSum.decompose_of_mem_ne S m.2 hik, smul_zero]
    | add a b ha hb =>
      intro k
      simp only [map_add (f := _), DirectSum.decompose_add, DirectSum.add_apply, Submodule.coe_add, smul_add, ha k, hb k]
  rw [injective_iff_map_eq_zero]
  intro v hv
  have hz : DirectSum.decompose S v = 0 := by
    ext k
    have := key v k
    rw [hv, map_zero, DirectSum.decompose_zero] at this
    simp only [DirectSum.zero_apply, ZeroMemClass.coe_zero] at this ⊢
    exact (smul_eq_zero.mp this.symm).resolve_left (hc0 k)
  exact (DirectSum.decompose S).injective (by rw [hz, DirectSum.decompose_zero])

end Formalism.MainNotions.J

end
