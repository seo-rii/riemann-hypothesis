module

public import Formalism.HermitianLattices.StatementMaj
public import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
public import Formalism.LocalRingCardinality.Lemmas
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Formalism.LocalToGlobal.Divisibility.CoefMod
public import Formalism.LocalToGlobal.Divisibility.GoodPartHermitianSpec
public import Formalism.LocalToGlobal.Divisibility.RowLat
import Formalism.LocalToGlobal.IndefiniteForms.IndefSide
import Formalism.QuotientMetricDivisors.Statement

@[expose] public section

noncomputable section

open Module NumberField IsDedekindDomain Formalism.DivisionValues Formalism.L2.DIV Formalism.L2.Indef Formalism.BasicNotions
open scoped Matrix InnerProductSpace ComplexOrder

namespace GlobalTheory.Mem.RowSides

section Semi

variable {K : Type} [Field K] {σ : K →+* ℂ} {U V W : Type} [AddCommGroup U] [Module K U] [AddCommGroup W] [Module ℂ W]

theorem semi_injective_of_basis {ι : Type} [Fintype ι] (b : Basis ι K U) (g : U →ₛₗ[σ] W)
    (h : LinearIndependent ℂ fun i => g (b i)) : Function.Injective g := by
  rw [injective_iff_map_eq_zero]
  intro x hx

  rw [← b.sum_repr x, map_sum] at hx
  simp only [map_smulₛₗ] at hx
  have := Fintype.linearIndependent_iff.1 h (fun i => σ (b.repr x i)) hx
  refine b.repr.injective (Finsupp.ext fun i => σ.injective ?_)
  simpa using this i

end Semi

section Polar

variable {K : Type} [Field K] [NumberField K] [StarRing K]

theorem majAt_expand {V ι : Type} [AddCommGroup V] [Module K V] [Fintype ι] [DecidableEq ι] (b : Basis ι K V)
    (X : InfinitePlace K → Matrix ι ι ℂ) (v : InfinitePlace K) (a : K) (x y : V) :
    Formalism.HermitianLatticesTheory.normAt b X v (x + a • y) ^ 2 = Formalism.HermitianLatticesTheory.normAt b X v x ^ 2 + Formalism.HermitianLatticesTheory.normAt b X v (a • y) ^ 2 +
      2 * (v.embedding a * Formalism.HermitianLatticesTheory.majAt b X v x y).re := by
  have hs : Formalism.HermitianLatticesTheory.fcoord b X v (a • y) = v.embedding a • Formalism.HermitianLatticesTheory.fcoord b X v y := by
    have : Formalism.HermitianLatticesTheory.vecAt b v (a • y) = v.embedding a • Formalism.HermitianLatticesTheory.vecAt b v y := by
      funext i; simp [Formalism.HermitianLatticesTheory.vecAt]
    rw [Formalism.HermitianLatticesTheory.fcoord, this, Matrix.mulVec_smul]; rfl
  simp only [normAt_sq_eq_majAt, Formalism.HermitianLatticesTheory.majAt, Formalism.HermitianLatticesTheory.fcoord_add, hs, Finset.mul_sum, Complex.re_sum,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, star_add, star_mul', Complex.star_def, Complex.mul_re, Complex.add_re,
    Complex.add_im, Complex.mul_im, Complex.conj_re, Complex.conj_im]
  ring

theorem majAt_eq_of_normAt [_root_.NumberField.IsTotallyComplex K] {V ι W κ : Type} [AddCommGroup V] [Module K V] [Fintype ι] [DecidableEq ι]
    [AddCommGroup W] [Module K W] [Fintype κ] [DecidableEq κ] (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
    (b' : Basis κ K W) (X' : InfinitePlace K → Matrix κ κ ℂ) (v : InfinitePlace K) (e : V →ₗ[K] W)
    (h : ∀ x, Formalism.HermitianLatticesTheory.normAt b' X' v (e x) ^ 2 = Formalism.HermitianLatticesTheory.normAt b X v x ^ 2) (x y : V) :
    Formalism.HermitianLatticesTheory.majAt b' X' v (e x) (e y) = Formalism.HermitianLatticesTheory.majAt b X v x y := by
  have key : ∀ a : K, (v.embedding a * Formalism.HermitianLatticesTheory.majAt b' X' v (e x) (e y)).re =
      (v.embedding a * Formalism.HermitianLatticesTheory.majAt b X v x y).re := fun a => by
    have h1 := majAt_expand b X v a x y
    have h2 := majAt_expand b' X' v a (e x) (e y)
    rw [← map_smul, ← map_add (f := _), h, h, h] at h2
    linarith
  obtain ⟨a, ha⟩ : ∃ a : K, (v.embedding a).im ≠ 0 := by
    by_contra hn
    push Not at hn
    have hc := IsTotallyComplex.isComplex v
    rw [InfinitePlace.isComplex_iff] at hc
    apply hc
    rw [ComplexEmbedding.isReal_iff]
    ext x
    rw [ComplexEmbedding.conjugate_coe_eq]
    exact Complex.conj_eq_iff_im.2 (hn x)
  have h1 := key 1
  have h2 := key a
  simp only [map_one, one_mul] at h1
  simp only [Complex.mul_re, h1] at h2
  refine Complex.ext h1 (mul_left_cancel₀ ha ?_)
  linarith

end Polar

section Block

variable {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] [Fintype G] {Pl0 : Type}
  (B : BlockDat K G Pl0) (ℓ : Lvl K G)

variable {B ℓ} {v0 : InfinitePlace K} (hv0 : IsConjAt v0) {s : ℕ} (h : B.Ok s) (hX : ∀ χ ∈ ℓ.X, IsAbsIrrChar χ)




end Block

end GlobalTheory.Mem.RowSides

end
