module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.BaseOver
public import Mathlib.LinearAlgebra.Matrix.BilinearForm
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
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
import Mathlib.Tactic.TypeStar
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

open Function

namespace GlobalTheory

section General

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

theorem pow_succ_dvd_bilin_of_const_on_cosets (h2 : IsUnit (2 : R)) (r : R)
    (B : LinearMap.BilinForm R M) (hB : ∀ x y, B x y = B y x) (T : Set M)
    (hT : ∀ x, ∃ t ∈ T, ∃ a, x = t + r • a) (c : R) (hc : ∀ t ∈ T, B t t = c) (i : ℕ)
    (hi : ∀ x y, r ^ i ∣ B x y) (x y : M) : r ^ (i + 1) ∣ B x y := by
  have h1 : ∀ z, r ^ (i + 1) ∣ B z z - c := by
    intro z
    obtain ⟨t, ht, a, rfl⟩ := hT z
    have : B (t + r • a) (t + r • a) - c = (B t a + B a t + r * B a a) * r := by
      simp only [map_add (f := _), map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
        ← hc t ht]
      ring
    rw [this, pow_succ]
    exact mul_dvd_mul_right (((hi _ _).add (hi _ _)).add ((hi _ _).mul_left _)) r
  have h0 : r ^ (i + 1) ∣ c := by simpa using h1 0
  have h3 : ∀ z, r ^ (i + 1) ∣ B z z := fun z => by simpa using (h1 z).add h0
  have h4 : 2 * B x y = B (x + y) (x + y) - B x x - B y y := by
    simp only [map_add (f := _), LinearMap.add_apply, hB y x]
    ring
  exact h2.dvd_mul_left.1 (h4 ▸ ((h3 _).sub (h3 _)).sub (h3 _))

theorem bilin_eq_zero_of_const_on_cosets (h2 : IsUnit (2 : R)) {r : R} (hr : IsNilpotent r)
    (B : LinearMap.BilinForm R M) (hB : ∀ x y, B x y = B y x) (T : Set M)
    (hT : ∀ x, ∃ t ∈ T, ∃ a, x = t + r • a) (c : R) (hc : ∀ t ∈ T, B t t = c) : B = 0 := by
  have h : ∀ (i : ℕ) (x y : M), r ^ i ∣ B x y := by
    intro i
    induction i with
    | zero => simp
    | succ i ih => exact pow_succ_dvd_bilin_of_const_on_cosets h2 r B hB T hT c hc i ih
  obtain ⟨k, hk⟩ := hr
  ext x y
  simpa [hk] using h k x y

theorem end_eq_zero_of_quad_const_on_cosets (h2 : IsUnit (2 : R)) {r : R} (hr : IsNilpotent r)
    (ω : LinearMap.BilinForm R M) (hω : Injective ω) (S : M →ₗ[R] M)
    (hS : ∀ x y, ω (S x) y = ω (S y) x) (u : Rˣ) (q : M → R)
    (hq : ∀ x, 2 * q x = u * ω (S x) x) (T : Set M)
    (hT : ∀ x, ∃ t ∈ T, ∃ a, x = t + r • a) (c : R) (hc : ∀ t ∈ T, q t = c) : S = 0 := by
  have h : (ω ∘ₗ S : LinearMap.BilinForm R M) = 0 := by
    refine bilin_eq_zero_of_const_on_cosets h2 hr (ω ∘ₗ S) hS T hT (↑u⁻¹ * (2 * c)) fun t ht => ?_
    rw [← hc t ht, hq, Units.inv_mul_cancel_left]
    rfl
  ext x
  exact hω ((LinearMap.congr_fun h x).trans (by simp))

end General

section ZMod

variable {n k : ℕ}

theorem isUnit_two_zmod_pow (hn : Odd n) (k : ℕ) : IsUnit (2 : ZMod (n ^ k)) := by
  have h : Nat.Coprime 2 (n ^ k) := (Nat.coprime_two_left.2 hn).pow_right k
  simpa using (ZMod.isUnit_iff_coprime 2 (n ^ k)).2 h

theorem exists_eq_nsmul_of_nsmul_eq_zero_zmod (hn : n ≠ 0) (hk : 2 ≤ k) (x : ZMod (n ^ k))
    (hx : n • x = 0) : ∃ a, x = n • a := by
  obtain ⟨z, rfl⟩ := ZMod.intCast_surjective x
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le' hk
  have h1 : (((n : ℤ) * z : ℤ) : ZMod (n ^ (j + 2))) = 0 := by
    rw [← hx]; simp
  obtain ⟨w, hw⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 h1
  have h2 : z = n * ((n : ℤ) ^ j * w) := by
    apply mul_left_cancel₀ (Int.natCast_ne_zero.2 hn)
    rw [hw]; push_cast; ring
  exact ⟨(((n : ℤ) ^ j * w : ℤ) : ZMod (n ^ (j + 2))), by rw [h2]; simp⟩

end ZMod

section LevelForm

open ReciprocityTheory.ChartRestriction.G.Out

theorem injective_toBilin'_stdSymp {R : Type*} [CommRing R] (g : ℕ) :
    Injective (Matrix.toBilin' (Matrix.of fun i j => ((stdSymp g i j : ℤ) : R))) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  funext i
  have key : ∀ j, ∑ l, x l * ((stdSymp g l j : ℤ) : R) = 0 := fun j => by
    have := LinearMap.congr_fun hx (Pi.single j 1)
    simpa [Matrix.toBilin'_apply, Pi.single_apply] using this
  by_cases hi : (i : ℕ) < g
  · have h := key ⟨i + g, by omega⟩
    rw [Finset.sum_eq_single i] at h
    · simpa [stdSymp, hi] using h
    · intro l _ hl
      have h1 : (l : ℕ) ≠ i := fun h => hl (Fin.ext h)
      have : stdSymp g l ⟨i + g, by omega⟩ = 0 := by
        unfold stdSymp
        rw [if_neg (by simp only; omega), if_neg (by simp only; omega)]
      simp [this]
    · simp
  · have hi2 := i.2
    have h := key ⟨i - g, by omega⟩
    rw [Finset.sum_eq_single i] at h
    · have : stdSymp g i ⟨i - g, by omega⟩ = -1 := by
        unfold stdSymp
        rw [if_neg (by simp only; omega), if_pos (by simp only; omega)]
      simpa [this] using h
    · intro l _ hl
      have h1 : (l : ℕ) ≠ i := fun h => hl (Fin.ext h)
      have : stdSymp g l ⟨i - g, by omega⟩ = 0 := by
        unfold stdSymp
        rw [if_neg (by simp only; omega), if_neg (by simp only; omega)]
      simp [this]
    · simp

end LevelForm

end GlobalTheory
