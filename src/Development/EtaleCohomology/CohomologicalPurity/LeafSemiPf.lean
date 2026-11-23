module

public import Development.EtaleCohomology.CohomologicalPurity.LeafIndExc
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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

@[expose] public section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.CohomologicalPurity

theorem LeafSemi_of : LeafSemi := by
  intro hA9 hG
  intro q _ X Z S p ι _ d e _ _ hq U hU N i
  obtain ⟨gys, rs, hgys⟩ := hG d
  let P : SP d := ⟨X, Z, S, p, ι, e, U, inferInstance, inferInstance, inferInstance, hU⟩
  have hqX : IsUnit (q : Γ(P.X, ⊤)) := by
    simpa using hq.map p.appTop.hom
  have hex := (hgys q P hqX).1
  have hsub : ∀ m j : ℤ, m < 0 → Subsingleton (Ht q (sch.obj Z) m j) :=
    fun m j hm => (hA9 (ZMod q) (tw q j)).1 _ m hm
  obtain ⟨j, rfl⟩ : ∃ j, i = j + d := ⟨i - d, by ring⟩
  constructor
  · intro hN
    refine ⟨?_, ?_⟩
    · obtain ⟨m, rfl⟩ : ∃ m, N = m + 2 * d := ⟨N - 2 * d, by ring⟩
      have hm : m < 0 := by omega
      have := hsub m j hm
      rw [injective_iff_map_eq_zero]
      intro a ha
      obtain ⟨b, rfl⟩ := ((hex m j).2.2 a).1 ha
      rw [Subsingleton.elim b 0, map_zero]
    · obtain ⟨m, rfl⟩ : ∃ m, N = m + 2 * d - 1 := ⟨N - 2 * d + 1, by ring⟩
      have hm : m < 0 := by omega
      have := hsub m j hm
      intro u
      exact ((hex m j).1 u).1 (Subsingleton.elim _ _)
  · intro hN
    obtain ⟨m, rfl⟩ : ∃ m, N = m + 2 * d := ⟨N - 2 * d, by ring⟩
    have hm : m < 0 := by omega
    have := hsub m j hm
    rw [injective_iff_map_eq_zero]
    intro a ha
    obtain ⟨b, rfl⟩ := ((hex m j).2.2 a).1 ha
    rw [Subsingleton.elim b 0, map_zero]

end LateralTheory.CohomologicalPurity
