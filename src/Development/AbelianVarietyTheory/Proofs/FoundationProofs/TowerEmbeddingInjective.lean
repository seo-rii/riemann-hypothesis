module

public import Development.AbelianVarietyTheory.Definitions.Foundations.NotCoboundaryConstantOne
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsBasisOnZetaPowMulQPow
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsDiscreteValuationRingCyclotomicTowerLevel
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Foundations.CosetTrace

@[expose] public section

open GlobalTheory.AlmostEt GlobalTheory.K5
open scoped NNReal

noncomputable section

namespace GlobalTheory.K5.EmbInj

theorem emb_injective : ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], IsClo p Ω →
    ∀ (T : Tower p Ω) (n : ℕ), 1 ≤ n → ∀ ι : On p n →ₐ[O0 p] Ω, IsEmb T n ι →
      Function.Injective ι := by
  intro p _ Ω _ _ hc T n hn ι _
  obtain ⟨hdom, -, -⟩ := GlobalTheory.K5.OnDVR.isDVR_On p n hn
  obtain ⟨b, -⟩ := GlobalTheory.K5.OnFree.on_free p n
  haveI : Module.Finite (O0 p) (On p n) := Module.Finite.of_basis b
  haveI : Algebra.IsIntegral (O0 p) (On p n) := Algebra.IsIntegral.of_finite _ _
  rw [injective_iff_map_eq_zero]
  have hker : RingHom.ker (ι : On p n →+* Ω) = ⊥ := by
    apply Ideal.eq_bot_of_comap_eq_bot (R := O0 p)
    rw [eq_bot_iff]
    intro a ha
    rw [Ideal.mem_comap, RingHom.mem_ker] at ha
    have : algebraMap (O0 p) Ω a = 0 := by
      rw [← ι.commutes a]; exact ha
    rw [Ideal.mem_bot]
    exact hc.inj (this.trans (map_zero _).symm)
  intro x hx
  have : x ∈ RingHom.ker (ι : On p n →+* Ω) := hx
  rwa [hker, Ideal.mem_bot] at this

end GlobalTheory.K5.EmbInj
