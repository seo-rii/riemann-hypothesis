module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsUnivRingBc
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RankLie

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj

namespace ReciprocityTheory.ChartRestriction.G.Chart

attribute [local instance] Over.cartesianMonoidalCategory

variable {S : Type} [CommRing S] (G : Over (Spec (CommRingCat.of S))) [GrpObj G]

abbrev Gs (s : S) : Over (Spec (CommRingCat.of (Localization.Away s))) :=
  (Over.pullback (fB S (Localization.Away s))).obj G


theorem chart_away (U : G.left.Opens) (hU : IsAffineOpen U) (s : S)
    (hs : ∀ x : Spec (CommRingCat.of S), s ∉ x.asIdeal → (η[G]).left x ∈ U) : Nonempty (Chart (Gs G s)) := by
  have hP := ReciprocityTheory.ChartRestriction.G.Geo.Tor.isGrpPullback_pullback G (fB S (Localization.Away s))
  have key : (η[Gs G s]).left ≫ pullback.fst G.hom (fB S (Localization.Away s)) =
      fB S (Localization.Away s) ≫ (η[G]).left := by
    have h1 := congrArg (fun m => m.left)
      (map_one (ReciprocityTheory.ChartRestriction.G.Geo.Tor.pushHom hP
        (Over.mk (𝟙 (Spec (CommRingCat.of (Localization.Away s)))))))
    simp only [one_left'] at h1
    change (1 : Over.mk (𝟙 (Spec (CommRingCat.of (Localization.Away s)))) ⟶ Gs G s).left ≫
      pullback.fst G.hom (fB S (Localization.Away s)) = _ at h1
    rw [one_left'] at h1
    simp
  have hs' : ∀ y : Spec (CommRingCat.of (Localization.Away s)),
      s ∉ ((fB S (Localization.Away s)).base y).asIdeal := by
    intro y hy
    have hu : IsUnit (algebraMap S (Localization.Away s) s) :=
      IsLocalization.Away.algebraMap_isUnit s
    have hmem : algebraMap S (Localization.Away s) s ∈ y.asIdeal := hy
    exact y.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ hmem hu)
  have hf : IsAffineHom (fB S (Localization.Away s)) := inferInstance
  have : IsAffineHom (pullback.fst G.hom (fB S (Localization.Away s))) :=
    isAffineHom_isStableUnderBaseChange.of_isPullback
      (IsPullback.of_hasPullback G.hom (fB S (Localization.Away s))).flip hf
  refine ⟨⟨pullback.fst G.hom (fB S (Localization.Away s)) ⁻¹ᵁ U, hU.preimage _, ?_⟩⟩
  intro y _
  have hk : (pullback.fst G.hom (fB S (Localization.Away s))).base ((η[Gs G s]).left.base y) =
      (η[G]).left.base ((fB S (Localization.Away s)).base y) := by
    change ((η[Gs G s]).left ≫ pullback.fst G.hom (fB S (Localization.Away s))).base y =
      (fB S (Localization.Away s) ≫ (η[G]).left).base y
    rw [key]
  show (pullback.fst G.hom (fB S (Localization.Away s))).base ((η[Gs G s]).left.base y) ∈ U
  rw [hk]
  exact hs _ (hs' y)

theorem exists_cover : ∃ (n : ℕ) (s : Fin n → S), Ideal.span (Set.range s) = ⊤ ∧ ∀ i, Nonempty (Chart (Gs G (s i))) := by
  classical
  have htop : Ideal.span {t : S | Nonempty (Chart (Gs G t))} = ⊤ := by
    by_contra hne
    obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal _ hne
    let p : Spec (CommRingCat.of S) := ⟨M, hM.isPrime⟩
    obtain ⟨U, hU, hpU, -⟩ := exists_isAffineOpen_mem_and_subset
      (show (η[G]).left p ∈ (⊤ : G.left.Opens) by simp)
    obtain ⟨V, ⟨t, rfl⟩, hpV, hVle⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.mp
      (PrimeSpectrum.isBasis_basic_opens (R := S)))
      (show p ∈ ((η[G]).left ⁻¹ᵁ U : (Spec (CommRingCat.of S)).Opens) from hpU)
    have hc : Nonempty (Chart (Gs G t)) := chart_away G U hU t (fun x hx => hVle hx)
    exact hpV (hle (Ideal.subset_span hc))
  obtain ⟨T, hsub, hspan⟩ := (Ideal.span_eq_top_iff_finite _).mp htop
  refine ⟨T.card, fun i => (T.equivFin.symm i : S), ?_, ?_⟩
  · have hr : Set.range (fun i => (T.equivFin.symm i : S)) = (T : Set S) := by
      ext x
      constructor
      · rintro ⟨i, rfl⟩
        exact (T.equivFin.symm i).2
      · intro hx
        exact ⟨T.equivFin ⟨x, hx⟩, by simp⟩
    rw [hr]
    exact hspan
  · intro i
    exact hsub (T.equivFin.symm i).2

end ReciprocityTheory.ChartRestriction.G.Chart
