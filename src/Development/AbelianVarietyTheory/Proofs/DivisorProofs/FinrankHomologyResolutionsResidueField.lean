module

public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PartialFreeResolutionsHomotopyEquivalentStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Divisors.AxesVanishingStructureSheafDegOne
import Development.AbelianVarietyTheory.Definitions.Divisors.CommAlgFunctorCoboundaryZeroMemCocyclesOne
import Development.AbelianVarietyTheory.Definitions.Divisors.OneFormMapEqKaehlerDifferentialMap
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.Dimension.Finite
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.QuadTie
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.NonzeroLocus

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.AbLaw GlobalTheory.CatCoh GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AbCoh

theorem finrank_add_le_of_image_mem {K V W : Type} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] [AddCommGroup W] [Module K W] [FiniteDimensional K W]
    (A : V →ₗ[K] W) (Z R : Submodule K V) (Z' R' : Submodule K W) (hR' : R' ≤ Z')
    (hZ : ∀ x ∈ Z, A x ∈ Z') (hk : ∀ x ∈ Z, A x ∈ R' → x ∈ R) :
    Module.finrank K Z + Module.finrank K R' ≤ Module.finrank K Z' + Module.finrank K R := by
  let g : (Z × R') →ₗ[K] W := LinearMap.coprod (A ∘ₗ Z.subtype) R'.subtype
  have h1 := LinearMap.finrank_range_add_finrank_ker g
  rw [Module.finrank_prod] at h1
  have h2 : Module.finrank K (LinearMap.range g) ≤ Module.finrank K Z' := by
    apply Submodule.finrank_mono
    rintro _ ⟨⟨x, r⟩, rfl⟩
    simp only [g, LinearMap.coprod_apply, LinearMap.comp_apply, Submodule.subtype_apply]
    exact Z'.add_mem (hZ x x.2) (hR' r.2)
  have h3 : Module.finrank K (LinearMap.ker g) ≤ Module.finrank K R := by
    let φ : LinearMap.ker g →ₗ[K] R :=
      LinearMap.codRestrict R (Z.subtype ∘ₗ LinearMap.fst K Z R' ∘ₗ (LinearMap.ker g).subtype) (by
        rintro ⟨⟨x, r⟩, hx⟩
        simp only [LinearMap.mem_ker, g, LinearMap.coprod_apply, LinearMap.comp_apply,
          Submodule.subtype_apply] at hx
        simp only [LinearMap.comp_apply, Submodule.subtype_apply, LinearMap.fst_apply]
        apply hk x x.2
        have : A x = -(r : W) := eq_neg_of_add_eq_zero_left hx
        rw [this]; exact R'.neg_mem r.2)
    refine LinearMap.finrank_le_finrank_of_injective (f := φ) ?_
    rw [injective_iff_map_eq_zero]
    rintro ⟨⟨x, r⟩, hx⟩ h0
    simp only [LinearMap.mem_ker, g, LinearMap.coprod_apply, LinearMap.comp_apply,
      Submodule.subtype_apply] at hx
    have hx0 : x = 0 := by
      apply Subtype.ext
      have := congrArg Subtype.val h0
      simpa [φ] using this
    subst hx0
    have hr : r = 0 := by
      apply Subtype.ext
      simpa using hx
    subst hr
    rfl
  omega

theorem finrank_homology_base_change_resolutions : ∀ (O : Type) [CommRing O] (K : Type) [Field K] [Algebra O K] (N : Type) [AddCommGroup N] [Module O N] (F₀ : Type) [AddCommGroup F₀] [Module O F₀] [Module.Free O F₀] [Module.Finite O F₀] (F₁ : Type) [AddCommGroup F₁] [Module O F₁] [Module.Free O F₁] [Module.Finite O F₁] (F₂ : Type) [AddCommGroup F₂] [Module O F₂] [Module.Free O F₂] [Module.Finite O F₂] (F₃ : Type) [AddCommGroup F₃] [Module O F₃] [Module.Free O F₃] [Module.Finite O F₃] (G₀ : Type) [AddCommGroup G₀] [Module O G₀] [Module.Free O G₀] [Module.Finite O G₀] (G₁ : Type) [AddCommGroup G₁] [Module O G₁] [Module.Free O G₁] [Module.Finite O G₁] (G₂ : Type) [AddCommGroup G₂] [Module O G₂] [Module.Free O G₂] [Module.Finite O G₂] (ε : F₀ →ₗ[O] N) (d₁ : F₁ →ₗ[O] F₀) (d₂ : F₂ →ₗ[O] F₁) (d₃ : F₃ →ₗ[O] F₂) (ν : G₀ →ₗ[O] N) (e₁ : G₁ →ₗ[O] G₀) (e₂ : G₂ →ₗ[O] G₁), Function.Surjective ε → Function.Exact d₁ ε → Function.Exact d₂ d₁ → Function.Exact d₃ d₂ → Function.Surjective ν → Function.Exact e₁ ν → Function.Exact e₂ e₁ → Module.finrank K (LinearMap.ker (d₁.baseChange K)) + Module.finrank K (LinearMap.range (e₂.baseChange K)) = Module.finrank K (LinearMap.ker (e₁.baseChange K)) + Module.finrank K (LinearMap.range (d₂.baseChange K)) ∧ Module.finrank K (LinearMap.ker (d₂.baseChange K)) ≤ Module.finrank K (LinearMap.range (d₃.baseChange K)) + Module.finrank K (K ⊗[O] G₂) := by
  intro O _ K _ _ N _ _ F₀ _ _ _ _ F₁ _ _ _ _ F₂ _ _ _ _ F₃ _ _ _ _ G₀ _ _ _ _ G₁ _ _ _ _
    G₂ _ _ _ _ ε d₁ d₂ d₃ ν e₁ e₂ hε hd₁ hd₂ hd₃ hν he₁ he₂
  obtain ⟨a₀, a₁, a₂, b₀, b₁, b₂, h₀, h₁, h₂, k₀, k₁, c1, c2, c3, c4, c5, c6, c7⟩ :=
    GlobalTheory.T.partialFreeResolutions_homotopyEquivalent O N F₀ F₁ F₂ F₃ G₀ G₁ G₂ ε d₁ d₂ d₃ ν e₁ e₂ hε hd₁ hd₂ hd₃ hν he₁ he₂
  have bc : ∀ {P Q : Type} [AddCommGroup P] [Module O P] [AddCommGroup Q] [Module O Q]
      {f g : P →ₗ[O] Q}, f = g → ∀ x, f.baseChange K x = g.baseChange K x := by
    intro P Q _ _ _ _ f g h x; rw [h]
  have z12 : ∀ x, d₁.baseChange K (d₂.baseChange K x) = 0 := by
    intro x; have := bc hd₂.linearMap_comp_eq_zero x
    simpa [LinearMap.baseChange_comp] using this
  have ze12 : ∀ x, e₁.baseChange K (e₂.baseChange K x) = 0 := by
    intro x; have := bc he₂.linearMap_comp_eq_zero x
    simpa [LinearMap.baseChange_comp] using this
  have q1 : ∀ x, e₁.baseChange K (a₁.baseChange K x) = a₀.baseChange K (d₁.baseChange K x) := by
    intro x; have := bc c1 x; simpa [LinearMap.baseChange_comp] using this
  have q2 : ∀ x, e₂.baseChange K (a₂.baseChange K x) = a₁.baseChange K (d₂.baseChange K x) := by
    intro x; have := bc c2 x; simpa [LinearMap.baseChange_comp] using this
  have q3 : ∀ x, d₁.baseChange K (b₁.baseChange K x) = b₀.baseChange K (e₁.baseChange K x) := by
    intro x; have := bc c3 x; simpa [LinearMap.baseChange_comp] using this
  have q4 : ∀ x, d₂.baseChange K (b₂.baseChange K x) = b₁.baseChange K (e₂.baseChange K x) := by
    intro x; have := bc c4 x; simpa [LinearMap.baseChange_comp] using this
  have q5 : ∀ x, x - b₁.baseChange K (a₁.baseChange K x) =
      d₂.baseChange K (h₁.baseChange K x) + h₀.baseChange K (d₁.baseChange K x) := by
    intro x; have := bc c5 x
    simpa [LinearMap.baseChange_comp, LinearMap.baseChange_sub, LinearMap.baseChange_add,
      LinearMap.baseChange_id] using this
  have q6 : ∀ x, x - b₂.baseChange K (a₂.baseChange K x) =
      d₃.baseChange K (h₂.baseChange K x) + h₁.baseChange K (d₂.baseChange K x) := by
    intro x; have := bc c6 x
    simpa [LinearMap.baseChange_comp, LinearMap.baseChange_sub, LinearMap.baseChange_add,
      LinearMap.baseChange_id] using this
  have q7 : ∀ x, x - a₁.baseChange K (b₁.baseChange K x) =
      e₂.baseChange K (k₁.baseChange K x) + k₀.baseChange K (e₁.baseChange K x) := by
    intro x; have := bc c7 x
    simpa [LinearMap.baseChange_comp, LinearMap.baseChange_sub, LinearMap.baseChange_add,
      LinearMap.baseChange_id] using this
  refine ⟨le_antisymm ?_ ?_, ?_⟩
  · refine finrank_add_le_of_image_mem (a₁.baseChange K) _ _ _ _ ?_ ?_ ?_
    · rintro _ ⟨y, rfl⟩; exact ze12 y
    · intro x hx; rw [LinearMap.mem_ker] at hx ⊢; rw [q1, hx, map_zero]
    · rintro x hx ⟨y, hy⟩
      rw [LinearMap.mem_ker] at hx
      refine ⟨b₂.baseChange K y + h₁.baseChange K x, ?_⟩
      have := q5 x
      rw [hx, map_zero, add_zero, ← hy, ← q4] at this
      rw [map_add (f := _), ← this]; abel
  · refine finrank_add_le_of_image_mem (b₁.baseChange K) _ _ _ _ ?_ ?_ ?_
    · rintro _ ⟨y, rfl⟩; exact z12 y
    · intro x hx; rw [LinearMap.mem_ker] at hx ⊢; rw [q3, hx, map_zero]
    · rintro x hx ⟨y, hy⟩
      rw [LinearMap.mem_ker] at hx
      refine ⟨a₂.baseChange K y + k₁.baseChange K x, ?_⟩
      have := q7 x
      rw [hx, map_zero, add_zero, ← hy, ← q2] at this
      rw [map_add (f := _), ← this]; abel
  · have := finrank_add_le_of_image_mem (a₂.baseChange K) (LinearMap.ker (d₂.baseChange K))
      (LinearMap.range (d₃.baseChange K)) ⊤ ⊥ bot_le (fun _ _ => Submodule.mem_top) (by
        intro x hx h0
        rw [LinearMap.mem_ker] at hx
        rw [Submodule.mem_bot] at h0
        refine ⟨h₂.baseChange K x, ?_⟩
        have := q6 x
        rw [hx, h0, map_zero, map_zero, add_zero, sub_zero] at this
        exact this.symm)
    simp only [finrank_top, finrank_bot, add_zero] at this
    omega

end GlobalTheory.AbCoh
