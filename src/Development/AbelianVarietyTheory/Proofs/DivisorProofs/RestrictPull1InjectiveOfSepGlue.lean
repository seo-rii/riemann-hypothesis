module

public import Development.AbelianVarietyTheory.Definitions.Divisors.CommAlgFunctorCoboundaryZeroMemCocyclesOne
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
import Development.AbelianVarietyTheory.Definitions.Divisors.OneFormMapEqKaehlerDifferentialMap
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst

@[expose] public section

open CategoryTheory AlgebraicGeometry KaehlerDifferential ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.CechDR

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CatCoh.CoefMap

theorem restrict_pull1_injective_of_sep_glue {R : Type} [CommRing R] {C : Type} [Category.{0} C]
    {C' : Type} [Category.{0} C'] (F : C ⥤ CommAlgCat.{0} R) (G : C' ⥤ C)
    (hsep : ∀ (T : C) (x : F.obj T), (∀ t (u : T ⟶ G.obj t), mp F u x = 0) → x = 0)
    (hglue : ∀ (T : C) (s : ∀ t, (T ⟶ G.obj t) → F.obj (G.obj t)),
      (∀ t t' (u : T ⟶ G.obj t) (a : t ⟶ t'), s t' (u ≫ G.map a) = mp F (G.map a) (s t u)) →
      ∃ x : F.obj T, ∀ t u, mp F u x = s t u) :
    Function.Injective (CoefMap.restrict F G).pull1 := by
  rw [injective_iff_map_eq_zero]
  intro c hc
  obtain ⟨f, rfl⟩ := H1.mk_surjective F c
  rw [CoefMap.pullCohomologyOne_class, H1.mk_eq_zero] at hc
  obtain ⟨g₀, hg⟩ := hc
  let g : ∀ t, F.obj (G.obj t) := fun t ↦ g₀ t
  have hg' : ∀ t t' (a : t ⟶ t'), g t' - mp F (G.map a) (g t) = f.1 _ _ (G.map a) := fun t t' a ↦
    congrFun (congrFun (congrFun hg t) t') a
  have h1 : ∀ T : C, ∃ x : F.obj T, ∀ t (u : T ⟶ G.obj t), mp F u x = g t - f.1 T _ u := by
    intro T
    refine hglue T (fun t u ↦ g t - f.1 T _ u) fun t t' u a ↦ ?_
    have k1 := Z1.comp f u (G.map a)
    have k2 := hg' t t' a
    simp only [map_sub]
    linear_combination k2 - k1
  choose x hx using h1
  refine H1.mk_eq_zero.2 ⟨x, ?_⟩
  funext T T' φ
  rw [amitsur_d0_apply]
  refine (sub_eq_zero.1 (hsep T' _ fun t u ↦ ?_)).symm
  have k1 := Z1.comp f φ u
  have k2 := hx T' t u
  have k3 := hx T t (φ ≫ u)
  rw [mp_comp] at k3
  simp only [map_sub]
  linear_combination k3 - k2 - k1

end GlobalTheory.CatCoh.CoefMap
