module

public import Development.EtaleCohomology.EtaleSheaves.LeafGhostCut
public import Development.EtaleCohomology.EtaleSheaves.StalkCut
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
import Mathlib.Tactic.Basify
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
import Development.EtaleCohomology.EtaleSheaves.LocalDescent

@[expose] public section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry CochainComplex CochainComplex.HomComplex GlobalTheory.EtC LateralTheory.E.t_E3Cut LateralTheory.E.StalkCut LateralTheory.E.DescLocPf LateralTheory.E.LeafGhostCut

namespace LateralTheory.E.TruncationKernel

def RelDesc : Prop := Hyp → ∀ (q : ℕ) [NeZero q] (i n : ℤ) {A Y : CommRingCat.{0}} (φ : A ⟶ Y), IsUnit (q : A) →
  ∀ P : ∀ C : CommRingCat.{0}, (A ⟶ C) → Prop, PushClosed P → EtClosed P →
  (∀ m < n, ∀ (C : CommRingCat.{0}) (c : A ⟶ C), P C c → BCn q i m φ c) →
  ∀ (D : CommRingCat.{0}) (d : A ⟶ D), P D d →
  ∀ (Y' : CommRingCat.{0}) (w : Y ⟶ Y') (φ' : D ⟶ Y'), IsPushout φ d w φ' →
  ∀ (E : CommRingCat.{0}) (e : D ⟶ E) (Y'' : CommRingCat.{0}) (u : Y' ⟶ Y'') (φ'' : E ⟶ Y''),
    Et e → SpS e → P E (d ≫ e) → ∀ hpo' : IsPushout φ' e u φ'',
  Function.Injective (rpl q i (Spec.map φ') (Spec.map φ'') (Spec.map u) (Spec.map e)
    (by rw [← Spec.map_comp, ← Spec.map_comp, hpo'.w]) n)

theorem fgt_injective_of_pull_surjective : ∀ (R : Type) [CommRing R] (F : Shv R) {U E : Spc} (f : U ⟶ E) (n : ℤ),
  (∀ m : ℤ, m + 1 = n → Function.Surjective (pull R f F m)) → Function.Injective (fgt R f F n) := by
  intro R _ F U E f n hs
  rw [injective_iff_map_eq_zero]
  intro y hy
  obtain ⟨c, rfl⟩ := y.mk_surjective
  change CohomologyClass.mk (zcomp (Cocycle.ofHom (mappingCone.inr ((chains R).map f))) c (zero_add n)) = 0 at hy
  rw [CohomologyClass.mk_eq_zero_iff] at hy
  obtain ⟨m, hm, γ, hγ⟩ := hy
  change δ m n γ = (Cochain.ofHom (mappingCone.inr ((chains R).map f))).comp c.1 (zero_add n) at hγ
  have hdec : c.1 = mappingCone.descCochain _ ((mappingCone.inl ((chains R).map f)).comp c.1 (show -1 + n = m by lia))
      (δ m n γ) hm := by
    rw [mappingCone.ext_cochain_from_iff _ m n hm, hγ]
    simp
  have hc : δ n (n + 1) c.1 = 0 := Cocycle.δ_eq_zero c (n + 1)
  rw [hdec, mappingCone.δ_descCochain _ _ _ _ _ rfl] at hc
  have hc' := congrArg (fun z => (mappingCone.inl ((chains R).map f)).comp z (show -1 + (n + 1) = n by lia)) hc
  simp at hc'
  set a := (mappingCone.inl ((chains R).map f)).comp c.1 (show -1 + n = m by lia) with ha
  have hz : δ m n (a - n.negOnePow • (Cochain.ofHom ((chains R).map f)).comp γ (zero_add m)) = 0 := by
    rw [δ_sub, δ_units_smul, δ_ofHom_comp]
    rw [Int.negOnePow_succ, Units.neg_smul, ← sub_eq_add_neg] at hc'
    exact hc'
  obtain ⟨w, hw⟩ := hs m hm (CohomologyClass.mk (Cocycle.mk _ n hm hz))
  obtain ⟨w', rfl⟩ := w.mk_surjective
  change CohomologyClass.mk (zcomp (Cocycle.ofHom ((chains R).map f)) w' (zero_add m)) = _ at hw
  rw [← sub_eq_zero, ← CohomologyClass.mk_sub, CohomologyClass.mk_eq_zero_iff] at hw
  obtain ⟨k, hk, α0, hα0⟩ := hw
  change δ k m α0 = (Cochain.ofHom ((chains R).map f)).comp w'.1 (zero_add m) -
    (a - n.negOnePow • (Cochain.ofHom ((chains R).map f)).comp γ (zero_add m)) at hα0
  rw [CohomologyClass.mk_eq_zero_iff]
  refine ⟨m, hm, mappingCone.descCochain _ (-α0) (γ + n.negOnePow • w'.1) hk, ?_⟩
  rw [mappingCone.δ_descCochain _ _ _ _ _ hm, δ_add, δ_units_smul, Cocycle.δ_eq_zero, smul_zero, add_zero]
  conv_rhs => rw [hdec]
  rw [mappingCone.ext_cochain_from_iff _ m n hm]
  refine ⟨?_, ?_⟩
  · simp only [mappingCone.inl_descCochain, Cochain.comp_add, mappingCone.inl_fst_assoc]
    simp only [δ_neg, hα0, Cochain.comp_units_smul, smul_add, smul_smul, Int.units_mul_self, one_smul, mappingCone.inl_snd_assoc, zero_comp, Cochain.zero_comp, add_zero]
    abel
  · simp

end LateralTheory.E.TruncationKernel
