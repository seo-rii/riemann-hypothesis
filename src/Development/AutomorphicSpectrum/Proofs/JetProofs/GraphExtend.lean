module

public import Development.AutomorphicSpectrum.Definitions.JetCones.SymCapRev
public import Formalism.RealPlaceAnalysis.StatementA
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Development.AutomorphicSpectrum.Proofs.JetProofs.EvFirst
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.RingTheory.PiTensorProduct
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Formalism.PeriodIntegrals.UpqRep
public import Mathlib.Analysis.InnerProductSpace.Orthogonal
public import Mathlib.Analysis.InnerProductSpace.Projection.Basic

@[expose] public section

open GlobalTheory.CompanionTheory.AlgRepEndIrreducible PI.UpqRep Matrix
open scoped InnerProductSpace

namespace GlobalTheory.CompanionTheory.AlgRepEndIrreducible.HwMap

theorem word_adj {n : ℕ} {ε : Fin n → Bool} {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    {D : Fin n → Fin n → Module.End ℂ V} (h : KAdj ε D) (l : List (Fin n × Fin n))
    (hl : ∀ x ∈ l, ε x.1 = ε x.2) (x y : V) :
    ⟪(l.map fun x => D x.1 x.2).prod x, y⟫_ℂ =
      ⟪x, (((l.map Prod.swap).reverse).map fun x => D x.1 x.2).prod y⟫_ℂ := by
  induction l generalizing y with
  | nil => simp
  | cons a l ih =>
    have ha := hl a (by simp)
    have ih' := ih (fun x hx => hl x (by simp [hx])) (D a.2 a.1 y)
    simp only [List.map_cons, List.prod_cons, Module.End.mul_apply, List.reverse_cons,
      List.map_append, List.prod_append, List.map_nil, List.prod_nil, mul_one, Prod.fst_swap,
      Prod.snd_swap]
    rw [h _ _ ha, ih']

theorem graph_extend {n : ℕ} {ε : Fin n → Bool} {V V' : Type} [NormedAddCommGroup V]
    [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] [AddCommGroup V'] [Module ℂ V']
    {D : Fin n → Fin n → Module.End ℂ V} {D' : Fin n → Fin n → Module.End ℂ V'} (h : KAdj ε D)
    (G : Submodule ℂ (V × V')) (hG : ∀ g ∈ G, g.1 = 0 → g.2 = 0)
    (hst : ∀ a b, ε a = ε b → ∀ g ∈ G, (D a b g.1, D' a b g.2) ∈ G) :
    ∃ T : V →ₗ[ℂ] V', (∀ g ∈ G, T g.1 = g.2) ∧ KMap ε D D' T := by
  let A : G →ₗ[ℂ] V := (LinearMap.fst ℂ V V').comp G.subtype
  have hA : Function.Injective A := by
    rw [injective_iff_map_eq_zero]
    intro g hg
    have h1 : g.1.1 = 0 := hg
    exact Subtype.ext (Prod.ext h1 (hG _ g.2 h1))
  let U : Submodule ℂ V := LinearMap.range A
  let e : G ≃ₗ[ℂ] U := LinearEquiv.ofInjective A hA
  let T : V →ₗ[ℂ] V' := ((LinearMap.snd ℂ V V').comp G.subtype).comp
    (e.symm.toLinearMap.comp (U.orthogonalProjectionOnto : V →ₗ[ℂ] U))
  have key : ∀ g ∈ G, ∀ z ∈ Uᗮ, T (g.1 + z) = g.2 := by
    intro g hg z hz
    have h1 : U.orthogonalProjectionOnto (g.1 + z) = e ⟨g, hg⟩ := by
      rw [map_add (f := _), Submodule.orthogonalProjectionOnto_eq_zero_iff.2 hz, add_zero]
      exact Submodule.orthogonalProjectionOnto_mem_subspace_eq_self (e ⟨g, hg⟩)
    show ((e.symm (U.orthogonalProjectionOnto (g.1 + z)) : G) : V × V').2 = g.2
    rw [h1, e.symm_apply_apply]
  refine ⟨T, fun g hg => by simpa using key g hg 0 (zero_mem _), ?_⟩
  intro a b hab w
  obtain ⟨u, hu, z, hz, rfl⟩ := U.exists_add_mem_mem_orthogonal w
  obtain ⟨g, rfl⟩ := hu
  have hz' : D a b z ∈ Uᗮ := by
    rw [Submodule.mem_orthogonal]
    rintro _ ⟨g', rfl⟩
    rw [← h b a hab.symm]
    exact (Submodule.mem_orthogonal _ _).1 hz _ ⟨⟨_, hst b a hab.symm _ g'.2⟩, rfl⟩
  have h1 := key _ (hst a b hab _ g.2) _ hz'
  have h2 := key _ g.2 _ hz
  have h3 : A g = g.1.1 := rfl
  rw [h3, h2, map_add (f := _)]
  exact h1

theorem hwmap : ∀ (n : ℕ) (ε : Fin n → Bool) (V V' : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] [NormedAddCommGroup V'] [InnerProductSpace ℂ V'] (D : Fin n → Fin n → Module.End ℂ V) (D' : Fin n → Fin n → Module.End ℂ V') (μ : Fin n → ℝ) (v : V) (v' : V'), KRel ε D → KRel ε D' → KAdj ε D → KAdj ε D' → Formalism.REAL.KHighest ε D μ v → Formalism.REAL.KHighest ε D' μ v' → v ≠ 0 → ∃ T : V →ₗ[ℂ] V', T v = v' ∧ KMap ε D D' T := by
  intro n ε V V' _ _ _ _ _ D D' μ v v' hR hR' hA hA' hv hv' hv0
  have vev := GlobalTheory.CompanionTheory.AlgRepEndIrreducible.Vev.vev_eq n ε V V' D D' μ v v' hR hR' hA hA' hv hv'
  let S : Set (V × V') := {g | ∃ l : List (Fin n × Fin n), (∀ x ∈ l, ε x.1 = ε x.2) ∧
    g = ((l.map fun x => D x.1 x.2).prod v, (l.map fun x => D' x.1 x.2).prod v')}
  have hin : ∀ g ∈ Submodule.span ℂ S, ∀ g' ∈ Submodule.span ℂ S,
      ⟪g.1, g'.1⟫_ℂ * ⟪v', v'⟫_ℂ = ⟪g.2, g'.2⟫_ℂ * ⟪v, v⟫_ℂ := by
    intro g hg g' hg'
    induction hg using Submodule.span_induction with
    | zero => simp
    | add x y _ _ hx hy => simp only [Prod.fst_add, Prod.snd_add, inner_add_left, add_mul, hx, hy]
    | smul c x _ hx => simp only [Prod.smul_fst, Prod.smul_snd, inner_smul_left, mul_assoc, hx]
    | mem x hx =>
      induction hg' using Submodule.span_induction with
      | zero => simp
      | add x y _ _ hx hy =>
        simp only [Prod.fst_add, Prod.snd_add, inner_add_right, add_mul, hx, hy]
      | smul c x _ hx => simp only [Prod.smul_fst, Prod.smul_snd, inner_smul_right, mul_assoc, hx]
      | mem y hy =>
        obtain ⟨l, hl, rfl⟩ := hx
        obtain ⟨l', hl', rfl⟩ := hy
        have := vev ((l.map Prod.swap).reverse ++ l') (by
          intro x hx
          rcases List.mem_append.1 hx with hx | hx
          · obtain ⟨y, hy, rfl⟩ := List.mem_map.1 (List.mem_reverse.1 hx)
            exact (hl y hy).symm
          · exact hl' x hx)
        simp only [List.map_append, List.prod_append, Module.End.mul_apply] at this
        dsimp only
        rw [word_adj hA l hl, word_adj hA' l hl, this]
  obtain ⟨T, hT, hK⟩ := graph_extend (D' := D') hA (Submodule.span ℂ S) (by
    intro g hg h0
    have := hin g hg g hg
    rw [h0, inner_zero_left, zero_mul] at this
    rcases mul_eq_zero.1 this.symm with h | h
    · exact inner_self_eq_zero.1 h
    · exact absurd (inner_self_eq_zero.1 h) hv0) (by
    intro a b hab g hg
    induction hg using Submodule.span_induction with
    | zero =>
      simp only [Prod.fst_zero, Prod.snd_zero, map_zero]
      exact Submodule.zero_mem _
    | add x y _ _ hx hy => simpa using Submodule.add_mem _ hx hy
    | smul c x _ hx => simpa using Submodule.smul_mem _ c hx
    | mem x hx =>
      obtain ⟨l, hl, rfl⟩ := hx
      refine Submodule.subset_span ⟨(a, b) :: l, ?_, by simp⟩
      intro x hx
      rcases List.mem_cons.1 hx with rfl | hx
      · exact hab
      · exact hl x hx)
  exact ⟨T, hT (v, v') (Submodule.subset_span ⟨[], by simp, by simp⟩), hK⟩

end GlobalTheory.CompanionTheory.AlgRepEndIrreducible.HwMap
