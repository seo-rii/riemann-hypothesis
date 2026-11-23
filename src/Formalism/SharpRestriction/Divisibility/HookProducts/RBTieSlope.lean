module

public import Formalism.HarderNarasimhan.Statement
public import Formalism.HarderNarasimhan.HarderNarasimhanProofs.Rerealize
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
import Mathlib.Tactic.Linter.Style
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

open Module

noncomputable section

namespace Formalism.MainNotions.DIV.HookProducts.RBTie

theorem slope_eq_of_norm_eq {R V E F : Type*} [Ring R] [AddCommGroup V] [Module R V]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    (ρ : V →+ E) (ρ₂ : V →+ F) (hn : ∀ x, ‖ρ₂ x‖ = ‖ρ x‖) (N : Submodule R V) :
    Formalism.HN.slope ρ₂ N = Formalism.HN.slope ρ N := by
  classical
  have memL : ∀ y : E, y ∈ Formalism.HN.zl ρ N ↔ ∃ x ∈ N.toAddSubgroup, ρ x = y := by
    intro y
    show y ∈ (N.toAddSubgroup.map ρ) ↔ _
    exact AddSubgroup.mem_map
  have memM : ∀ y : F, y ∈ Formalism.HN.zl ρ₂ N ↔ ∃ x ∈ N.toAddSubgroup, ρ₂ x = y := by
    intro y
    show y ∈ (N.toAddSubgroup.map ρ₂) ↔ _
    exact AddSubgroup.mem_map
  let pre : Formalism.HN.zl ρ N → V := fun y => Classical.choose ((memL y).1 y.2)
  have pre_mem : ∀ y, pre y ∈ N.toAddSubgroup := fun y =>
    (Classical.choose_spec ((memL y).1 y.2)).1
  have pre_eq : ∀ y, ρ (pre y) = y := fun y => (Classical.choose_spec ((memL y).1 y.2)).2
  let f0 : Formalism.HN.zl ρ N →+ Formalism.HN.zl ρ₂ N :=
    AddMonoidHom.mk' (fun y => ⟨ρ₂ (pre y), (memM _).2 ⟨pre y, pre_mem y, rfl⟩⟩) (by
      intro y z
      apply Subtype.ext
      show ρ₂ (pre (y + z)) = ρ₂ (pre y) + ρ₂ (pre z)
      rw [← map_add (f := _)]
      apply Formalism.HN.Rerealization.eq_of_eq ρ ρ₂ hn
      rw [map_add (f := _), pre_eq, pre_eq, pre_eq]
      rfl)
  have f0_apply : ∀ y, ((f0 y : Formalism.HN.zl ρ₂ N) : F) = ρ₂ (pre y) := fun y => rfl
  have f0_norm : ∀ y, ‖((f0 y : Formalism.HN.zl ρ₂ N) : F)‖ = ‖(y : E)‖ := by
    intro y
    rw [f0_apply, hn, pre_eq]
  have hinj : Function.Injective f0 := by
    rw [injective_iff_map_eq_zero]
    intro y hy
    have h0 : ‖(y : E)‖ = 0 := by
      rw [← f0_norm, hy]
      simp
    exact Subtype.ext (norm_eq_zero.1 h0)
  have hsurj : Function.Surjective f0 := by
    rintro ⟨z, hz⟩
    obtain ⟨x, hx, rfl⟩ := (memM z).1 hz
    refine ⟨⟨ρ x, (memL _).2 ⟨x, hx, rfl⟩⟩, Subtype.ext ?_⟩
    rw [f0_apply]
    exact Formalism.HN.Rerealization.eq_of_eq ρ ρ₂ hn (pre_eq _)
  let e : Formalism.HN.zl ρ N ≃+ Formalism.HN.zl ρ₂ N := AddEquiv.ofBijective f0 ⟨hinj, hsurj⟩
  have e_norm : ∀ y, ‖e y‖ = ‖y‖ := fun y => f0_norm y
  have e_symm_norm : ∀ z, ‖e.symm z‖ = ‖z‖ := by
    intro z
    rw [← e_norm (e.symm z), e.apply_symm_apply]
  have iso : Isometry e := AddMonoidHomClass.isometry_of_norm e e_norm
  have iso_symm : Isometry e.symm := AddMonoidHomClass.isometry_of_norm e.symm e_symm_norm
  have hiff : DiscreteTopology (Formalism.HN.zl ρ N) ↔ DiscreteTopology (Formalism.HN.zl ρ₂ N) := by
    constructor
    · intro h
      exact iso_symm.isEmbedding.discreteTopology
    · intro h
      exact iso.isEmbedding.discreteTopology
  have hrk : Formalism.F.rk (Formalism.HN.zl ρ₂ N) = Formalism.F.rk (Formalism.HN.zl ρ N) := by
    unfold Formalism.F.rk
    exact e.toIntLinearEquiv.finrank_eq.symm
  have hcov : Formalism.F.covol (Formalism.HN.zl ρ₂ N) = Formalism.F.covol (Formalism.HN.zl ρ N) := by
    by_cases h : DiscreteTopology (Formalism.HN.zl ρ N)
    · exact (Formalism.HN.Rerealization.covol_rk_eq ρ ρ₂ hn N.toAddSubgroup h (hiff.1 h)).1
    · have h' : ¬ DiscreteTopology (Formalism.HN.zl ρ₂ N) := fun h' => h (hiff.2 h')
      unfold Formalism.F.covol
      rw [dite_eq_right h, dite_eq_right h']
  unfold Formalism.HN.slope Formalism.F.slope Formalism.F.deg
  rw [hcov, hrk]

end Formalism.MainNotions.DIV.HookProducts.RBTie
