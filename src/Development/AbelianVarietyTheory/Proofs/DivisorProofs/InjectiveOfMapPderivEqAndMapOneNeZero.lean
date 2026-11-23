module

public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.Basic.Complex.Basic
public import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
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

@[expose] public section

namespace GlobalTheory.FockAlg


open MvPolynomial in
theorem injective_of_pderiv {V : Type} [AddCommGroup V] [Module ℂ V] {ι : Type}
    (Φ₀ : MvPolynomial ι ℂ →ₗ[ℂ] V) (d : ι → Module.End ℂ V)
    (hd : ∀ (i : ι) (p : MvPolynomial ι ℂ), Φ₀ (MvPolynomial.pderiv i p) = d i (Φ₀ p))
    (h1 : Φ₀ 1 ≠ 0) : Function.Injective Φ₀ := by
  classical
  have hC : ∀ p : MvPolynomial ι ℂ, Φ₀ p = 0 → (∀ m ∈ p.support, m = 0) → p = 0 := by
    intro p hp hs
    have e : p = (p.coeff 0) • (1 : MvPolynomial ι ℂ) := by
      ext m
      by_cases hm : m = 0
      · subst hm; simp
      · have : p.coeff m = 0 := by
          by_contra h
          exact hm (hs m (mem_support_iff.2 h))
        rw [this, MvPolynomial.coeff_smul, coeff_one, if_neg (Ne.symm hm), smul_zero]
    rw [e, map_smul, smul_eq_zero] at hp
    rcases hp with hp | hp
    · rw [e, hp, zero_smul]
    · exact absurd hp h1
  have key : ∀ n : ℕ, ∀ p : MvPolynomial ι ℂ, (∀ m ∈ p.support, m.degree ≤ n) →
      Φ₀ p = 0 → p = 0 := by
    intro n
    induction n with
    | zero =>
      intro p hs hp
      exact hC p hp (fun m hm => (Finsupp.degree_eq_zero_iff m).1 (Nat.le_zero.1 (hs m hm)))
    | succ n ih =>
      intro p hs hp
      have hz : ∀ i, pderiv i p = 0 := by
        intro i
        apply ih
        · intro m hm
          rw [mem_support_iff, coeff_pderiv] at hm
          have h2 := hs _ (mem_support_iff.2 (left_ne_zero_of_mul hm))
          rw [map_add (f := _), Finsupp.degree_single] at h2
          omega
        · rw [hd, hp, map_zero]
      apply hC p hp
      intro m hm
      by_contra hm0
      obtain ⟨i, hi⟩ : ∃ i, m i ≠ 0 := by
        by_contra h
        push Not at h
        exact hm0 (Finsupp.ext h)
      have hle : Finsupp.single i 1 ≤ m := by
        rw [Finsupp.single_le_iff]; omega
      have hc := congrArg (fun q : MvPolynomial ι ℂ => q.coeff (m - Finsupp.single i 1)) (hz i)
      rw [coeff_pderiv, tsub_add_cancel_of_le hle, AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply, mul_eq_zero] at hc
      rcases hc with hc | hc
      · exact (mem_support_iff.1 hm) hc
      · exact (Nat.cast_add_one_ne_zero _) hc
  rw [injective_iff_map_eq_zero]
  intro p hp
  exact key (p.support.sup fun m => m.degree) p
    (fun m hm => Finset.le_sup (f := fun m : ι →₀ ℕ => m.degree) hm) hp

end GlobalTheory.FockAlg
