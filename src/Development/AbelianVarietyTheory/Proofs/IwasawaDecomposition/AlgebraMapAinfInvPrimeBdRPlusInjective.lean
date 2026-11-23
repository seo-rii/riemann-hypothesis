module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsCrisP
public import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOfForallXiPowDvd
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCompatibleRootsOfUnityAndTiltPadic
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.KerThetaLocalizedEqSpanFontaineXiElementStatement
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

namespace GlobalTheory.MemLoc

theorem exists_isEps_for_inj (l : ℕ) [Fact l.Prime] : ∃ e : Per.Fl l, IsEps e := by
  obtain ⟨ζ, ε, h0, -, h1, h⟩ := GlobalTheory.MemLoc.exists_zeta_eps l
  refine ⟨ε, ?_, ?_⟩
  · have := h 0
    rw [h0, map_one] at this
    exact Subtype.ext this
  · intro hh
    have := h 1
    apply h1
    apply (algebraMap (Om l) ℂ_[l]).injective
    rw [← this, map_one]
    exact congrArg Subtype.val hh

theorem eq_zero_of_mem_span_pow_away {A B : Type*} [CommRing A] [CommRing B] [Algebra A B] (r ξ : A)
    [IsLocalization.Away r B] (hs : ∀ n : ℕ, ∀ a : A, ξ ^ n ∣ r * a → ξ ^ n ∣ a)
    (hh : ∀ a : A, (∀ n : ℕ, ξ ^ n ∣ a) → a = 0) (x : B)
    (hx : ∀ n : ℕ, x ∈ Ideal.span {algebraMap A B ξ} ^ n) : x = 0 := by
  have hs' : ∀ n m : ℕ, ∀ a : A, ξ ^ n ∣ r ^ m * a → ξ ^ n ∣ a := by
    intro n m
    induction m with
    | zero => intro a ha; simpa using ha
    | succ m ih =>
      intro a ha
      apply ih
      apply hs
      rwa [← mul_assoc, ← pow_succ']
  obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective (Submonoid.powers r) x
  have ha : a = 0 := by
    apply hh
    intro n
    have h1 : algebraMap A B a ∈ Ideal.map (algebraMap A B) (Ideal.span {ξ ^ n}) := by
      rw [Ideal.map_span, Set.image_singleton, map_pow, ← Ideal.span_singleton_pow,
        ← IsLocalization.mk'_spec B a s]
      exact Ideal.mul_mem_right _ _ (hx n)
    rw [IsLocalization.algebraMap_mem_map_algebraMap_iff (Submonoid.powers r)] at h1
    obtain ⟨_, ⟨m, rfl⟩, hm⟩ := h1
    exact hs' n m a (Ideal.mem_span_singleton.1 hm)
  simp [ha]

theorem algebraMap_AinfP_BdRp_injective (l : ℕ) [Fact l.Prime] :
    Function.Injective (algebraMap (Per.AinfP l) (Per.BdRp l)) := by
  obtain ⟨e, he⟩ := exists_isEps_for_inj l
  rw [injective_iff_map_eq_zero]
  intro x hx
  refine eq_zero_of_mem_span_pow_away (l : Per.Ainf l) (xi e)
    (fun n a h => XiHaus.xi_sat he n a h) (GlobalTheory.MemLoc.eq_zero_of_forall_xi_pow_dvd l e he) x fun n => ?_
  rw [← GlobalTheory.T.kerThetaLocalized_eq_span_fontaineXiElement l e he, ← Ideal.Quotient.eq_zero_iff_mem]
  have h1 : Per.ev l n (algebraMap (Per.AinfP l) (Per.BdRp l) x) = Ideal.Quotient.mk _ x :=
    GlobalTheory.RingIface.ev_alg l n x
  rw [← h1, hx, map_zero]

end GlobalTheory.MemLoc
