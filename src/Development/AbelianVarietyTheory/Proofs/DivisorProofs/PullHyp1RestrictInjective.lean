module

public import Development.AbelianVarietyTheory.Definitions.Divisors.CechDeRhamCoefMapOneFormsRestrictAlongFunctor
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
import Mathlib.Topology.Sheaves.Init
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst

@[expose] public section

open CategoryTheory AlgebraicGeometry KaehlerDifferential ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.CechDR

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CechDR

theorem pullHyp1_restrict_injective {R : Type} [CommRing R] {C : Type} [Category.{0} C] {C' : Type}
    [Category.{0} C'] (F : C ⥤ CommAlgCat.{0} R) (G : C' ⥤ C)
    (h1 : Function.Injective (CoefMap.restrict F G).pull1)
    (h0 : ∀ g' : ∀ t, F.obj (G.obj t), (∀ ⦃t t' : C'⦄ (a : t ⟶ t'), g' t' = mp F (G.map a) (g' t)) →
      ∃ g : C0 F, (∀ ⦃T T' : C⦄ (φ : T ⟶ T'), g T' = mp F φ (g T)) ∧ ∀ t, g (G.obj t) = g' t)
    (hf : Function.Injective (pullGlob1 (CoefMap.restrict F G))) :
    Function.Injective (pullHyp1 (CoefMap.restrict F G)) := by
  rw [injective_iff_map_eq_zero]
  intro c hc
  obtain ⟨x, rfl⟩ := Hyp1.mk_surjective F c
  have ht : toO F (Hyp1.mk F x) = 0 := h1 (by rw [← toO_pullHyp1, hc, map_zero, map_zero])
  rw [pullHyp1_mk, Hyp1.mk_eq_zero] at hc
  obtain ⟨g, hg'⟩ := hc
  obtain ⟨g', rfl⟩ : ∃ g' : ∀ t, F.obj (G.obj t), (g' : Tot0 (G ⋙ F)) = g := ⟨g, rfl⟩
  have hf' : ∀ ⦃t t' : C'⦄ (a : t ⟶ t'), g' t' - mp F (G.map a) (g' t) = x.1.1 _ _ (G.map a) :=
    fun t t' a ↦ congrArg (fun y : Tot1 (G ⋙ F) ↦ y.1 t t' a) hg'
  have hω : ∀ t, D R _ (g' t) = x.1.2 (G.obj t) := fun t ↦
    (congrArg (fun y : Tot1 (G ⋙ F) ↦ y.2 t) hg').trans (cechDeRhamCoefMapOneForms_restrictAlongFunctor F G t _)
  rw [toO_mk, H1.mk_eq_zero] at ht
  obtain ⟨g₀, hg₀⟩ := ht
  have hg0 : ∀ (T T' : C) (φ : T ⟶ T'), g₀ T' - mp F φ (g₀ T) = x.1.1 T T' φ := fun T T' φ ↦
    congrFun (congrFun (congrFun hg₀ T) T') φ
  obtain ⟨h, hh, hhG⟩ := h0 (fun t ↦ g' t - g₀ (G.obj t)) (fun t t' a ↦ by
    have e1 := hf' a
    have e2 := hg0 _ _ (G.map a)
    rw [map_sub]
    linear_combination e1 - e2)
  let θ : Glob1 F := ⟨fun T ↦ x.1.2 T - D R _ (g₀ T), fun T T' φ ↦ by
    show x.1.2 T' - D R _ (g₀ T') = p1 F φ (x.1.2 T - D R _ (g₀ T))
    rw [map_sub, p1_D, cechDeRhamTotalCocyclesOne.conn x φ, ← hg0 T T' φ, map_sub]; abel⟩
  let ψ : Glob1 F := ⟨fun T ↦ D R _ (h T), fun T T' φ ↦ by
    show D R _ (h T') = p1 F φ (D R _ (h T))
    rw [p1_D, ← hh φ]⟩
  have hθψ : θ = ψ := hf (Subtype.ext (funext fun t ↦ by
    change q1 (CoefMap.restrict F G) t (θ.1 (G.obj t)) = q1 (CoefMap.restrict F G) t (ψ.1 (G.obj t))
    rw [cechDeRhamCoefMapOneForms_restrictAlongFunctor, cechDeRhamCoefMapOneForms_restrictAlongFunctor]
    show x.1.2 (G.obj t) - D R _ (g₀ (G.obj t)) = D R _ (h (G.obj t))
    rw [hhG, map_sub, hω]))
  refine Hyp1.mk_eq_zero.2 ⟨g₀ + h, Tot1.ext (fun T T' φ ↦ ?_) fun T ↦ ?_⟩
  · rw [dTot0_f]
    simp only [Pi.add_apply, map_add (f := _)]
    linear_combination hh φ + hg0 T T' φ
  · have e : x.1.2 T - D R _ (g₀ T) = D R _ (h T) := congrArg (fun ω : Glob1 F ↦ ω.1 T) hθψ
    rw [dTot0_ω, Pi.add_apply, map_add (f := _), ← e]
    abel

end GlobalTheory.CechDR
