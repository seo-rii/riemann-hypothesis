module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.Basic.Complex.Basic
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.RingKrullDimQuotientEqOfMemMinimalPrimes
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SmoothOfRelativeDimensionOfDimOfFinrankDerivatio
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
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.PicardGroup
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.GoodClass
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.ZM

namespace GlobalTheory.GenericSmooth

theorem le_ringKrullDim_of_mem_minimalPrimes (o k R S : Type) [CommRing o] [IsDomain o] [Field k]
    [CommRing R] [CommRing S] [Algebra o k] [IsFractionRing o k] [Algebra o R] [Algebra k S]
    [Algebra R S] [Algebra o S] [IsScalarTower o R S] [IsScalarTower o k S]
    [IsLocalization (Algebra.algebraMapSubmonoid R (nonZeroDivisors o)) S]
    [Algebra.FiniteType k S] (d : ℕ)
    (h : ∀ (K : Type) [Field K] [Algebra o K] (φ : R →ₐ[o] K), RingHom.ker φ ∈ minimalPrimes R →
      (∀ z : K, ∃ a b, z = φ a / φ b) → ∃ y : Fin d → K, AlgebraicIndependent o y)
    (q : Ideal S) (hq : q ∈ minimalPrimes S) : (d : WithBot ℕ∞) ≤ ringKrullDim (S ⧸ q) := by
  have hp : q.IsPrime := hq.1.1
  let K := FractionRing (S ⧸ q)
  let ψ : S →ₐ[o] K := (IsScalarTower.toAlgHom o (S ⧸ q) K).comp (Ideal.Quotient.mkₐ o q)
  let φ : R →ₐ[o] K := ψ.comp (IsScalarTower.toAlgHom o R S)
  have hψ : ∀ s, ψ s = 0 ↔ s ∈ q := fun s ↦ by
    change algebraMap (S ⧸ q) K (Ideal.Quotient.mk q s) = 0 ↔ _
    rw [map_eq_zero_iff _ (IsFractionRing.injective (S ⧸ q) K), Ideal.Quotient.eq_zero_iff_mem]
  have hker : RingHom.ker φ = q.under R := by
    ext r
    exact hψ (algebraMap R S r)
  have hmin : RingHom.ker φ ∈ minimalPrimes R := by
    have h' := IsLocalization.minimalPrimes_map
      (Algebra.algebraMapSubmonoid R (nonZeroDivisors o)) S ⊥
    rw [Ideal.map_bot] at h'
    rw [hker]
    exact h'.le hq
  have hs : ∀ s : S, ∃ a b, φ b ≠ 0 ∧ ψ s = φ a / φ b := fun s ↦ by
    obtain ⟨⟨a, b⟩, hab⟩ := IsLocalization.surj
      (Algebra.algebraMapSubmonoid R (nonZeroDivisors o)) s
    have hb : φ b ≠ 0 := ((IsLocalization.map_units S b).map ψ).ne_zero
    refine ⟨a, b, hb, ?_⟩
    rw [eq_div_iff hb]
    have := congrArg ψ hab
    rw [map_mul] at this
    exact this
  have hsurj : ∀ z : K, ∃ a b, z = φ a / φ b := fun z ↦ by
    obtain ⟨x, y, -, rfl⟩ := IsFractionRing.div_surjective (A := S ⧸ q) z
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
    obtain ⟨a, b, hb, h₁⟩ := hs x
    obtain ⟨a', b', hb', h₂⟩ := hs y
    refine ⟨a * b', b * a', ?_⟩
    change ψ x / ψ y = _
    rw [h₁, h₂, map_mul, map_mul, div_div_div_eq]
  obtain ⟨y, hy⟩ := h K φ hmin hsurj
  obtain ⟨n, h₁, h₂⟩ := GlobalTheory.exists_ringKrullDim_eq_and_trdeg_eq k (S ⧸ q)
  have hk : AlgebraicIndependent k y := by
    have : Algebra.IsAlgebraic o k := IsLocalization.isAlgebraic k (nonZeroDivisors o)
    exact hy.extendScalars k
  have h₃ := hk.cardinalMk_le_trdeg
  have : Algebra.IsAlgebraic (S ⧸ q) K := IsLocalization.isAlgebraic K (nonZeroDivisors (S ⧸ q))
  have : FaithfulSMul k (S ⧸ q) :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr (algebraMap k (S ⧸ q)).injective
  rw [← trdeg_add_eq k (S ⧸ q) (A := K), trdeg_eq_zero (R := S ⧸ q) (A := K), add_zero, h₂,
    Cardinal.mk_fin] at h₃
  rw [h₁]
  exact_mod_cast h₃

theorem finrank_derivation_le (o k R S C : Type) [CommRing o] [CommRing k]
    [CommRing R] [CommRing S] [Field C] [Algebra o k] [Algebra o R] [Algebra k S]
    [Algebra R S] [Algebra o S] [IsScalarTower o R S] [IsScalarTower o k S]
    (M : Submonoid R) [IsLocalization M S] [Algebra.FiniteType o R]
    [Algebra k C] [Algebra S C] [IsScalarTower k S C] [Algebra o C] [Algebra R C]
    [IsScalarTower o R C] [IsScalarTower R S C] [IsScalarTower o S C] [IsScalarTower o k C] :
    Module.finrank C (Derivation k S C) ≤ Module.finrank C (Derivation o R C) := by
  have : Module.Finite C (Derivation o R C) :=
    Module.Finite.equiv (GlobalTheory.SmoothTangent.derivationEquivDual o R C).symm
  let f : Derivation k S C →ₗ[C] Derivation o R C :=
    { toFun := fun D ↦ (D.restrictScalars o).compAlgebraMap R
      map_add' := fun _ _ ↦ by ext; rfl
      map_smul' := fun _ _ ↦ by ext; rfl }
  refine LinearMap.finrank_le_finrank_of_injective (f := f) ?_
  rw [injective_iff_map_eq_zero]
  intro D hD
  have h0 : ∀ r, D (algebraMap R S r) = 0 := fun r ↦ congr($hD r)
  ext s
  obtain ⟨⟨a, b⟩, hab⟩ := IsLocalization.surj M s
  have := congrArg D hab
  rw [D.leibniz, h0, h0, smul_zero, zero_add, Algebra.smul_def] at this
  exact (mul_eq_zero.mp this).resolve_left
    ((IsLocalization.map_units S b).map (algebraMap S C)).ne_zero

end GlobalTheory.GenericSmooth

namespace GlobalTheory


attribute [local instance] Algebra.TensorProduct.rightAlgebra in
theorem smoothOfRelativeDimension_genericFibre_of_independent_of_finrank_derivation_le :
    ∀ (o : Type) [CommRing o] [IsDomain o] (em : o →+* ℂ) (R : Type) [CommRing R] [Algebra o R] (d : ℕ), Function.Injective em → Algebra.FiniteType o R → (∀ (K : Type) [Field K] [Algebra o K] (φ : R →ₐ[o] K), RingHom.ker φ ∈ minimalPrimes R → (∀ z : K, ∃ a b, z = φ a / φ b) → ∃ y : Fin d → K, AlgebraicIndependent o y) → (∀ [Algebra o ℂ] [Algebra R ℂ] [IsScalarTower o R ℂ], algebraMap o ℂ = em → Module.finrank ℂ (Derivation o R ℂ) ≤ d) → SmoothOfRelativeDimension d (spMap (algebraMap (FractionRing o) (FractionRing o ⊗[o] R))) := by
  intro o _ _ em R _ _ d hem hft hind htan
  let e : FractionRing o →+* ℂ := IsFractionRing.lift hem
  have : CharZero (FractionRing o) := e.charZero
  have := IsLocalization.tensorRight (S := R) (FractionRing o) (nonZeroDivisors o)
  refine smoothOfRelativeDimension_of_dim_of_finrank_derivation_le (FractionRing o) e _ d
    inferInstance
    (GenericSmooth.le_ringKrullDim_of_mem_minimalPrimes o (FractionRing o) R _ d hind) ?_
  intro _ _ _ he
  let : Algebra o ℂ := em.toAlgebra
  let : Algebra R ℂ :=
    ((algebraMap (FractionRing o ⊗[o] R) ℂ).comp (algebraMap R _)).toAlgebra
  have h₁ : IsScalarTower o (FractionRing o) ℂ := .of_algebraMap_eq fun x ↦ by
    rw [he]
    exact (IsFractionRing.lift_algebraMap hem x).symm
  have h₂ : IsScalarTower o (FractionRing o ⊗[o] R) ℂ := .of_algebraMap_eq fun x ↦ by
    rw [IsScalarTower.algebraMap_apply o (FractionRing o) ℂ,
      IsScalarTower.algebraMap_apply (FractionRing o) (FractionRing o ⊗[o] R) ℂ,
      ← IsScalarTower.algebraMap_apply o (FractionRing o) (FractionRing o ⊗[o] R)]
  have h₃ : IsScalarTower R (FractionRing o ⊗[o] R) ℂ := .of_algebraMap_eq fun _ ↦ rfl
  have h₄ : IsScalarTower o R ℂ := .of_algebraMap_eq fun x ↦ by
    rw [IsScalarTower.algebraMap_apply R (FractionRing o ⊗[o] R) ℂ,
      ← IsScalarTower.algebraMap_apply o R (FractionRing o ⊗[o] R),
      ← IsScalarTower.algebraMap_apply o (FractionRing o ⊗[o] R) ℂ]
  exact (GenericSmooth.finrank_derivation_le o (FractionRing o) R _ ℂ
    (Algebra.algebraMapSubmonoid R (nonZeroDivisors o))).trans (htan rfl)

end GlobalTheory
