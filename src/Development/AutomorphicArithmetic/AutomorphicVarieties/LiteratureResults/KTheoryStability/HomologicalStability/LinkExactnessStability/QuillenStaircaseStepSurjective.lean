module

public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.PermRepSingle
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
public import Mathlib.RepresentationTheory.Homological.GroupHomology.LongExactSequence
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

open CategoryTheory CategoryTheory.Limits GlobalTheory.HomStab

namespace GlobalTheory

theorem homStab_step : ∀ (k G : Type) [CommRing k] [Group G] (C₃ C₂ Z₁ C₁ Z₀ : Rep k G) (a : C₃ ⟶ C₂)
    (b : C₂ ⟶ Z₁) (ι : Z₁ ⟶ C₁) (e : C₁ ⟶ Z₀) (h : ι ≫ e = 0), (ShortComplex.mk ι e h).ShortExact →
    a ≫ b = 0 → ∀ q : ℕ, Function.Surjective (hMap b q).hom →
    Function.Exact (hMap a q).hom (hMap (b ≫ ι) q).hom → Function.Surjective (hMap e (q + 1)).hom := by
  intro k G _ _ C₃ C₂ Z₁ C₁ Z₀ a b ι e h hX hab q hb hex
  have hcomp : ∀ {A B C : Rep k G} (f : A ⟶ B) (g : B ⟶ C) (n : ℕ),
      hMap (f ≫ g) n = hMap f n ≫ hMap g n :=
    fun f g n => (groupHomology.functor k G n).map_comp f g
  have hzero : hMap (0 : C₃ ⟶ Z₁) q = 0 := (groupHomology.functor k G q).map_zero _ _
  have hinj : Function.Injective (hMap ι q).hom := by
    rw [injective_iff_map_eq_zero]
    intro z hz
    obtain ⟨y, rfl⟩ := hb z
    have hy : (hMap (b ≫ ι) q).hom y = 0 := by
      rw [hcomp]
      simpa using hz
    obtain ⟨x, rfl⟩ := (hex y).1 hy
    rw [← LinearMap.comp_apply, ← ModuleCat.hom_comp, ← hcomp, hab, hzero]
    rfl
  intro w
  have h3 := groupHomology.mapShortComplex₃_exact hX (i := q + 1) (j := q) rfl
  have hδ : (groupHomology.δ hX (q + 1) q rfl).hom w = 0 := by
    apply hinj
    rw [map_zero]
    exact (groupHomology.mapShortComplex₁ hX (i := q + 1) (j := q) rfl).moduleCat_zero_apply w
  exact (ShortComplex.moduleCat_exact_iff _).1 h3 w hδ

end GlobalTheory

section
open CategoryTheory CategoryTheory.Limits GlobalTheory.HomStab
end
