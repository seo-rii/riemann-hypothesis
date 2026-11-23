module

public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Algebra.Module.StablyFree.Basic
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
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
public import Mathlib.Algebra.Module.Projective
public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Defs

@[expose] public section

open Matrix

namespace GlobalTheory

namespace LatticeIndicator

theorem exists_injective_comp_eq_of_surjective {k V W : Type*} [Field k] [AddCommGroup V]
    [Module k V] [FiniteDimensional k V] [AddCommGroup W] [Module k W] (f g : V →ₗ[k] W)
    (hf : Function.Surjective f) (hg : Function.Surjective g) :
    ∃ e : V →ₗ[k] V, Function.Injective e ∧ g ∘ₗ e = f := by
  obtain ⟨s, hs⟩ := g.exists_rightInverse_of_surjective (LinearMap.range_eq_top.2 hg)
  have hrk : Module.finrank k (LinearMap.ker f) = Module.finrank k (LinearMap.ker g) := by
    have h1 := f.finrank_range_add_finrank_ker
    have h2 := g.finrank_range_add_finrank_ker
    rw [LinearMap.range_eq_top.2 hf] at h1
    rw [LinearMap.range_eq_top.2 hg] at h2
    omega
  let θ := LinearEquiv.ofFinrankEq _ _ hrk
  obtain ⟨p, hp⟩ := (LinearMap.ker f).subtype.exists_leftInverse_of_injective
    (Submodule.ker_subtype _)
  have hgs : ∀ w, g (s w) = w := fun w => LinearMap.congr_fun hs w
  have key : ∀ v, g (s (f v) + (θ (p v) : V)) = f v := fun v => by
    rw [map_add (f := _), hgs, (θ (p v)).2, add_zero]
  refine ⟨s ∘ₗ f + (LinearMap.ker g).subtype ∘ₗ θ.toLinearMap ∘ₗ p, ?_, LinearMap.ext key⟩
  rw [injective_iff_map_eq_zero]
  intro v hv
  have hv' : s (f v) + (θ (p v) : V) = 0 := hv
  have hfv : f v = 0 := by rw [← key v, hv', map_zero]
  rw [hfv, map_zero, zero_add] at hv'
  have h1 : p v = 0 := θ.map_eq_zero_iff.1 (Subtype.ext hv')
  have h2 : p v = ⟨v, hfv⟩ := LinearMap.congr_fun hp ⟨v, hfv⟩
  rw [h2] at h1
  exact congrArg Subtype.val h1

theorem exists_matrix_of_span_eq_top_field {k W n : Type*} [Field k] [AddCommGroup W] [Module k W]
    [Fintype n] [DecidableEq n] (a b : n → W) (ha : Submodule.span k (Set.range a) = ⊤)
    (hb : Submodule.span k (Set.range b) = ⊤) :
    ∃ g : Matrix n n k, g.det ≠ 0 ∧ ∀ j, a j = ∑ i, g i j • b i := by
  obtain ⟨e, he, hge⟩ := exists_injective_comp_eq_of_surjective
    (Fintype.linearCombination k a) (Fintype.linearCombination k b)
    (by rw [← LinearMap.range_eq_top, Fintype.range_linearCombination, ha])
    (by rw [← LinearMap.range_eq_top, Fintype.range_linearCombination, hb])
  refine ⟨LinearMap.toMatrix' e, ?_, fun j => ?_⟩
  · rw [LinearMap.det_toMatrix']
    exact ((LinearMap.isUnit_iff_isUnit_det e).1
      ((LinearMap.isUnit_iff_ker_eq_bot e).2 (LinearMap.ker_eq_bot.2 he))).ne_zero
  · have := LinearMap.congr_fun hge (Pi.single j 1)
    rw [Fintype.linearCombination_apply_single, one_smul] at this
    rw [← this]
    simp [Fintype.linearCombination_apply, LinearMap.toMatrix'_apply]

end LatticeIndicator

open LatticeIndicator

section Main

variable {O K m n R : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (IsLocalRing.ResidueField O)] [Field K] [Algebra O K] [IsFractionRing O K]
  [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n] [CommRing R]

end Main

end GlobalTheory
