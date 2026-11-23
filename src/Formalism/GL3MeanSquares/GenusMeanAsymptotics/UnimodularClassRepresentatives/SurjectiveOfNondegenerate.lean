module

public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.ApplyMemSmul
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.ExistsMulDvdUnif
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
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

@[expose] public section

open NumberField Module

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.D2.IA

variable {K : Type} [Field K] [StarRing K]
variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V]

theorem surjective_of_nondegenerate {h : V →ₗ⋆[K] V →ₗ[K] K} (hn : h.Nondegenerate) :
    Function.Surjective h := by
  have hinj : Function.Injective h := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    exact hn.1 x (fun y => by rw [hx]; rfl)
  have hbij : Function.Bijective (h.rangeRestrict) :=
    ⟨fun a b hab => hinj (congrArg Subtype.val hab), h.surjective_rangeRestrict⟩
  let j : V ≃+ LinearMap.range h := AddEquiv.ofBijective (h.rangeRestrict).toAddMonoidHom hbij
  have hr : Module.rank K V = Module.rank K (LinearMap.range h) :=
    rank_eq_of_equiv_equiv (starRingEnd K) j star_involutive.bijective (fun r m => by
      apply Subtype.ext
      show h (r • m) = (starRingEnd K) r • h m
      rw [map_smulₛₗ])
  have hf : finrank K (LinearMap.range h) = finrank K (Dual K V) := by
    rw [Subspace.dual_finrank_eq]
    unfold finrank
    rw [hr]
  have htop := Submodule.eq_top_of_finrank_eq hf
  exact LinearMap.range_eq_top.1 htop

theorem exists_adj {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (hn : h.Nondegenerate)
    (s : V →ₗ⋆[K] V →ₗ[K] K) : ∃ Y : V →ₗ[K] V, ∀ x y, h x (Y y) = s x y := by
  have hex : ∀ y, ∃ w, ∀ x, h x w = s x y := by
    intro y
    let l : V →ₗ[K] K :=
      { toFun := fun x => star (s x y)
        map_add' := fun a b => by simp
        map_smul' := fun a b => by simp [starRingEnd_apply] }
    obtain ⟨w, hw⟩ := surjective_of_nondegenerate hn l
    refine ⟨w, fun x => ?_⟩
    have h1 : h w x = star (s x y) := by rw [hw]; rfl
    have h2 := hs.eq w x
    rw [← h2, h1, starRingEnd_apply, star_star]
  choose Y hY using hex
  refine ⟨{ toFun := Y, map_add' := fun a b => ?_, map_smul' := fun a b => ?_ }, fun x y => hY y x⟩
  · rw [← sub_eq_zero]
    refine hn.2 _ (fun x => ?_)
    rw [map_sub, map_add (f := _), hY, hY, hY, map_add (f := _), sub_self]
  · rw [← sub_eq_zero]
    refine hn.2 _ (fun x => ?_)
    rw [RingHom.id_apply, map_sub, map_smul, hY, hY, map_smul, sub_self]

section Lat

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]

def phi (h : V →ₗ⋆[K] V →ₗ[K] K) (X : V ≃ₗ[K] V) : V →ₗ⋆[K] V →ₗ[K] K :=
  (h.comp (X : V →ₗ[K] V)).compl₂ (X : V →ₗ[K] V) - h

theorem phi_apply (h : V →ₗ⋆[K] V →ₗ[K] K) (X : V ≃ₗ[K] V) (x y : V) :
    phi h X x y = h (X x) (X y) - h x y := rfl

theorem star_phi {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (X : V ≃ₗ[K] V) (x y : V) :
    star (phi h X x y) = phi h X y x := by
  have e : ∀ a b, star (h a b) = h b a := fun a b => hs.eq a b
  rw [phi_apply, phi_apply, star_sub, e, e]

theorem unif_ne_zero {𝔭 : Ideal (𝓞 F)} {π : 𝓞 F} (hπ' : π ∉ 𝔭 ^ 2) : algebraMap F K (π : F) ≠ 0 := by
  intro h0
  have h1 : (π : F) = 0 := (map_eq_zero (algebraMap F K)).1 h0
  have h2 : π = 0 := by exact_mod_cast h1
  exact hπ' (h2 ▸ zero_mem _)

theorem sesq_scale (hF : IsFixF K F) {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {A₀ B₀ : Submodule (𝓞 K) V} {r : ℕ}
    (hr : extP K 𝔭 ^ r • locF 𝔭 A₀ ≤ locF 𝔭 B₀) (s : V →ₗ⋆[K] V →ₗ[K] K) {n m : ℕ} (hnm : n + 2 * r ≤ m)
    (hs : ∀ x ∈ locF 𝔭 B₀, ∀ y ∈ locF 𝔭 B₀, s x y ∈ pK K 𝔭 m) :
    ∀ x ∈ locF 𝔭 A₀, ∀ y ∈ locF 𝔭 A₀, s x y ∈ pK K 𝔭 n := by
  obtain ⟨π, hπ, hπ'⟩ := exists_unif h𝔭
  have h0 : algebraMap F K (π : F) ≠ 0 := unif_ne_zero hπ'
  have hst : star (algebraMap F K (π : F)) = algebraMap F K (π : F) := (hF _).2 ⟨_, rfl⟩
  intro x hx y hy
  have hx' : algebraMap F K (π : F) ^ r • x ∈ locF 𝔭 B₀ :=
    hr ((mem_smul_iff_unif h𝔭 hπ hπ' A₀).2 ⟨x, hx, rfl⟩)
  have hy' : algebraMap F K (π : F) ^ r • y ∈ locF 𝔭 B₀ :=
    hr ((mem_smul_iff_unif h𝔭 hπ hπ' A₀).2 ⟨y, hy, rfl⟩)
  have h1 := pK_anti (K := K) 𝔭 hnm (hs _ hx' _ hy')
  rw [map_smul, map_smulₛₗ, LinearMap.smul_apply, starRingEnd_apply, star_pow, hst, smul_eq_mul, smul_eq_mul] at h1
  obtain ⟨b, hb, e⟩ := (mem_pK_iff_unif h𝔭 hπ hπ').1 h1
  refine (mem_pK_iff_unif h𝔭 hπ hπ').2 ⟨b, hb, ?_⟩
  apply mul_left_cancel₀ (pow_ne_zero (2 * r) h0)
  calc algebraMap F K (π : F) ^ (2 * r) * s x y
      = algebraMap F K (π : F) ^ r * (algebraMap F K (π : F) ^ r * s x y) := by ring
    _ = algebraMap F K (π : F) ^ (n + 2 * r) * b := e
    _ = _ := by ring

theorem end_scale {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {A₀ B₀ : Submodule (𝓞 K) V} {r r' : ℕ}
    (hr : extP K 𝔭 ^ r • locF 𝔭 A₀ ≤ locF 𝔭 B₀) (hr' : extP K 𝔭 ^ r' • locF 𝔭 B₀ ≤ locF 𝔭 A₀)
    (Y : V →ₗ[K] V) {n m : ℕ} (hnm : n + r + r' ≤ m)
    (hY : ∀ x ∈ locF 𝔭 A₀, Y x ∈ extP K 𝔭 ^ m • locF 𝔭 A₀) :
    ∀ x ∈ locF 𝔭 B₀, Y x ∈ extP K 𝔭 ^ n • locF 𝔭 B₀ := by
  obtain ⟨π, hπ, hπ'⟩ := exists_unif h𝔭
  have h0 : algebraMap F K (π : F) ≠ 0 := unif_ne_zero hπ'
  intro x hx
  have hx' : algebraMap F K (π : F) ^ r' • x ∈ locF 𝔭 A₀ :=
    hr' ((mem_smul_iff_unif h𝔭 hπ hπ' B₀).2 ⟨x, hx, rfl⟩)
  have h1 := smul_anti 𝔭 (locF 𝔭 A₀) hnm (hY _ hx')
  obtain ⟨a, ha, e⟩ := (mem_smul_iff_unif h𝔭 hπ hπ' A₀).1 h1
  have ha' : algebraMap F K (π : F) ^ r • a ∈ locF 𝔭 B₀ :=
    hr ((mem_smul_iff_unif h𝔭 hπ hπ' A₀).2 ⟨a, ha, rfl⟩)
  refine (mem_smul_iff_unif h𝔭 hπ hπ' B₀).2 ⟨_, ha', ?_⟩
  rw [map_smul] at e
  apply smul_right_injective V (pow_ne_zero r' h0)
  show algebraMap F K (π : F) ^ r' • Y x = algebraMap F K (π : F) ^ r' • _
  rw [e, smul_smul, smul_smul]
  congr 1
  ring

end Lat

end Formalism.HermitianLattices.Ext.L3.D2.IA
