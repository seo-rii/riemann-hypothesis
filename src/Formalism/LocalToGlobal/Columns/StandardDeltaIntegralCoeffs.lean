module

public import Formalism.LocalToGlobal.Divisibility.CoefMod
import Formalism.GradedWeylDivisibility.DualWeylDominanceOf
import Formalism.GradedWeylDivisibility.FinalD
public import Formalism.LocalToGlobal.Divisibility.CoefModLemmas
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.Finsupp.Interval
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
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
import Formalism.LocalToGlobal.GlobalTheory.HLatOps
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc

@[expose] public section

open NumberField IsDedekindDomain Module MvPolynomial
open scoped Matrix ComplexOrder

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.GlobalTheoryTheory.HLatOps Formalism.HermitianLatticesTheory Formalism.HN

section Mon

variable {ι : Type} [Fintype ι] {n : ℕ}

def MonOK (lam : ι → DomWeight n) (m : (ι × Fin n × Fin n) →₀ ℕ) : Prop :=
  ∀ τ s, ∑ a, m (τ, a, s) = (lam τ).natW s

def MonI (lam : ι → DomWeight n) : Type := {m : (ι × Fin n × Fin n) →₀ ℕ // MonOK lam m}

theorem monOK_finite (lam : ι → DomWeight n) : {m | MonOK lam m}.Finite := by
  classical
  let M : (ι × Fin n × Fin n) →₀ ℕ := Finsupp.equivFunOnFinite.symm fun v => (lam v.1).natW v.2.2
  refine (Set.finite_Icc (0 : (ι × Fin n × Fin n) →₀ ℕ) M).subset ?_
  intro m hm
  refine ⟨zero_le, fun v => ?_⟩
  obtain ⟨τ, a, s⟩ := v
  show m (τ, a, s) ≤ (lam τ).natW s
  rw [← hm τ s]
  exact Finset.single_le_sum (f := fun a => m (τ, a, s)) (fun _ _ => Nat.zero_le _) (Finset.mem_univ a)

instance (lam : ι → DomWeight n) : Finite (MonI lam) := (monOK_finite lam).to_subtype

instance (lam : ι → DomWeight n) : Fintype (MonI lam) := Fintype.ofFinite _

instance (lam : ι → DomWeight n) : DecidableEq (MonI lam) := Classical.decEq _

theorem column_sum_eq_weight {r : ℕ} (ν : Fin n → ℕ) (u : (Fin r × Fin n) →₀ ℕ) (h : Finsupp.weight (Formalism.GradedWeylDivisibility.colW r n) u = ν) (s : Fin n) :
    ∑ a, u (a, s) = ν s := by
  classical
  have e : u.sum (fun i c => c • Formalism.GradedWeylDivisibility.colW r n i) = ∑ i, u i • Formalism.GradedWeylDivisibility.colW r n i :=
    Finsupp.sum_fintype _ _ (fun i => zero_smul ℕ _)
  rw [← h, Finsupp.weight_apply, e, Finset.sum_apply, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun a _ => ?_
  simp [Formalism.GradedWeylDivisibility.colW, Pi.single_apply]

open Classical in
theorem product_support_weights (K : Type) [Field K] (lam : ι → DomWeight n) (f : ι → MvPolynomial (Fin n × Fin n) K)
    (hf : ∀ τ, f τ ∈ nablaSq K n (lam τ)) (T : Finset ι) :
    ∀ m, AddMonoidAlgebra.coeff (∏ τ ∈ T, Formalism.GradedWeylDivisibility.blockEmb K τ (f τ)) m ≠ 0 → ∀ τ s, ∑ a, m (τ, a, s) = if τ ∈ T then (lam τ).natW s else 0 := by
  classical
  induction T using Finset.induction_on with
  | empty =>
    intro m hm τ s
    rw [Finset.prod_empty, coeff_one] at hm
    have : m = 0 := by
      by_contra h
      exact hm (if_neg fun h' => h h'.symm)
    subst this
    simp
  | insert t T ht ih =>
    intro m hm τ s
    rw [Finset.prod_insert ht] at hm
    have hm' := support_mul _ _ (mem_support_iff.2 hm)
    obtain ⟨m1, h1, m2, h2, rfl⟩ := Finset.mem_add.1 hm'
    have i2 := ih m2 (mem_support_iff.1 h2) τ s
    obtain ⟨u, hu, hu0⟩ := coeff_rename_ne_zero _ _ _ (mem_support_iff.1 h1)
    have hinj : Function.Injective (fun v : Fin n × Fin n => (t, v)) := fun a b h => (Prod.mk.inj h).2
    have hw : Finsupp.weight (Formalism.GradedWeylDivisibility.colW n n) u = (lam t).natW := by
      have := (hf t).1
      exact this hu0
    simp only [Finsupp.add_apply, Finset.sum_add_distrib, i2]
    by_cases hτ : τ = t
    · subst hτ
      have : ∀ a, m1 (τ, a, s) = u (a, s) := fun a => by
        rw [← hu]; exact Finsupp.mapDomain_apply_of_injective hinj u (a, s)
      simp only [this, column_sum_eq_weight _ u hw s, if_neg ht, Finset.mem_insert, true_or, if_true, add_zero]
    · have : ∀ a, m1 (τ, a, s) = 0 := fun a => by
        rw [← hu]
        refine Finsupp.mapDomain_of_notMem_range _ _ ?_
        rintro ⟨v, hv⟩
        exact hτ (Prod.mk.inj hv).1.symm
      simp only [this, Finset.sum_const_zero, zero_add, Finset.mem_insert, hτ, false_or]

theorem coefficient_space_support (K : Type) [Field K] (lam : ι → DomWeight n) {F : Pol K ι n} (hF : F ∈ VV K lam) :
    ∀ m, AddMonoidAlgebra.coeff F m ≠ 0 → MonOK lam m := by
  unfold VV Formalism.GradedWeylDivisibility.tensorLat at hF
  induction hF using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨f, hf, rfl⟩ := hx
    intro m hm τ s
    have := product_support_weights K lam f hf Finset.univ m hm τ s
    simpa using this
  | zero => intro m hm; exact False.elim (hm (by simp))
  | add x y _ _ hx hy =>
    intro m hm
    simp only [AddMonoidAlgebra.coeff_add, Finsupp.add_apply] at hm
    by_cases h : AddMonoidAlgebra.coeff x m = 0
    · exact hy m (by rw [h, zero_add] at hm; exact hm)
    · exact hx m h
  | smul c x _ hx =>
    intro m hm
    rw [MvPolynomial.coeff_smul] at hm
    exact hx m (fun h => hm (by rw [h, smul_zero]))

variable {K : Type} [Field K]

def cfMap (lam : ι → DomWeight n) (g : ι → GL (Fin n) K) : VV K lam →ₗ[K] (MonI lam → K) where
  toFun x := fun m => AddMonoidAlgebra.coeff (trAct g x.1) m.1
  map_add' x y := by funext m; simp
  map_smul' c x := by funext m; simp

theorem cfMap_apply (lam : ι → DomWeight n) (g : ι → GL (Fin n) K) (x : VV K lam) (m : MonI lam) :
    cfMap lam g x m = AddMonoidAlgebra.coeff (trAct g x.1) m.1 := rfl

theorem transpose_action_mem (lam : ι → DomWeight n) (g : ι → GL (Fin n) K) {F : Pol K ι n} (hF : F ∈ VV K lam) : trAct g F ∈ VV K lam :=
  (Formalism.GradedWeylDivisibility.blockActTensor K K ι n n (fun τ => ((g τ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)ᵀ)).2
    (fun τ => nablaSq K n (lam τ)) (fun τ => nablaSq K n (lam τ))
    (fun _ f hf => Formalism.GradedWeylDivisibility.dualWeylRowStable K n n _ _ f hf) F hF

theorem transpose_action_inv_right (g : ι → GL (Fin n) K) (F : Pol K ι n) : trAct g (trAct g⁻¹ F) = F := by
  rw [← AlgHom.comp_apply, ← trAct_mul, mul_inv_cancel, trAct_one]
  rfl

theorem transpose_action_inv_left (g : ι → GL (Fin n) K) (F : Pol K ι n) : trAct g⁻¹ (trAct g F) = F := by
  rw [← AlgHom.comp_apply, ← trAct_mul, inv_mul_cancel, trAct_one]
  rfl

theorem cfMap_injective (lam : ι → DomWeight n) (g : ι → GL (Fin n) K) : Function.Injective (cfMap lam g) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  have h0 : trAct g x.1 = 0 := by
    ext m
    simp only [AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply]
    by_contra h
    have hm := coefficient_space_support K lam (transpose_action_mem lam g x.2) m h
    exact h (congrFun hx ⟨m, hm⟩)
  apply Subtype.ext
  have := transpose_action_inv_left g x.1
  rw [h0, map_zero] at this
  exact this.symm

end Mon

section Int

variable {K : Type} [Field K] [NumberField K]

def locRing (w : HeightOneSpectrum (𝓞 K)) : Subring K where
  carrier := {x | x ∈ localization₂ w.asIdeal (1 : Submodule (𝓞 K) K)}
  mul_mem' := by
    rintro x y ⟨s, hs, hx⟩ ⟨t, ht, hy⟩
    obtain ⟨a, ha⟩ := Submodule.mem_one.1 hx
    obtain ⟨b, hb⟩ := Submodule.mem_one.1 hy
    refine ⟨s * t, mul_mem hs ht, Submodule.mem_one.2 ⟨a * b, ?_⟩⟩
    rw [map_mul, ha, hb, Algebra.smul_def, Algebra.smul_def, Algebra.smul_def, map_mul]
    ring
  one_mem' := ⟨1, one_mem _, by rw [one_smul]; exact Submodule.one_le.1 le_rfl⟩
  add_mem' := fun {x y} hx hy => (localization₂ w.asIdeal (1 : Submodule (𝓞 K) K)).add_mem hx hy
  zero_mem' := (localization₂ w.asIdeal (1 : Submodule (𝓞 K) K)).zero_mem
  neg_mem' := fun {x} hx => (localization₂ w.asIdeal (1 : Submodule (𝓞 K) K)).neg_mem hx

theorem mem_locRing (w : HeightOneSpectrum (𝓞 K)) (x : K) : x ∈ locRing w ↔ x ∈ localization₂ w.asIdeal (1 : Submodule (𝓞 K) K) := Iff.rfl

theorem mem_range_of_coeff_mem {σ : Type} (R0 : Subring K) {P : MvPolynomial σ K} (h : ∀ m, AddMonoidAlgebra.coeff P m ∈ R0) :
    P ∈ (map (σ := σ) R0.subtype).range := by
  refine ⟨∑ m ∈ P.support, monomial m ⟨AddMonoidAlgebra.coeff P m, h m⟩, ?_⟩

  rw [map_sum]
  simp only [map_monomial, Subring.coe_subtype]
  exact P.support_sum_monomial_coeff

theorem coeff_mem_of_mem_range {σ : Type} (R0 : Subring K) {P : MvPolynomial σ K} (hP : P ∈ (map (σ := σ) R0.subtype).range) (m : σ →₀ ℕ) :
    AddMonoidAlgebra.coeff P m ∈ R0 := by
  obtain ⟨Q, rfl⟩ := hP
  rw [coeff_map]
  exact (AddMonoidAlgebra.coeff Q m).2

theorem block_action_integral (R0 : Subring K) {ι : Type} [Fintype ι] {n : ℕ} (U : ι → Matrix (Fin n) (Fin n) K) (hU : ∀ τ a b, U τ a b ∈ R0)
    {P : MvPolynomial (ι × Fin n × Fin n) K} (hP : P ∈ (map (σ := ι × Fin n × Fin n) R0.subtype).range) :
    Formalism.GradedWeylDivisibility.blockAct K U P ∈ (map (σ := ι × Fin n × Fin n) R0.subtype).range := by
  obtain ⟨Q, rfl⟩ := hP
  induction Q using MvPolynomial.induction_on with
  | C a =>
    rw [map_C, algHom_C]
    exact ⟨C a, by simp⟩
  | add p q hp hq =>
    rw [map_add (map R0.subtype), map_add (f := _)]
    exact add_mem hp hq
  | mul_X p v hp =>
    rw [map_mul (map R0.subtype), map_X, map_mul, blockAct_X]
    exact mul_mem hp (sum_mem fun b _ => mul_mem ⟨C ⟨_, hU v.1 v.2.1 b⟩, by simp⟩ ⟨X (v.1, b, v.2.2), by simp⟩)

variable {ι : Type} [Fintype ι] {n : ℕ}

def twId (lam : ι → DomWeight n) (M : ι → Submodule (𝓞 K) (Fin n → K)) : Submodule (𝓞 K) K :=
  ⨅ (w : HeightOneSpectrum (𝓞 K)) (B : ι → GL (Fin n) K) (_ : ∀ τ, IsBasisAt w (M τ) (B τ)),
    (localization₂ w.asIdeal (1 : Submodule (𝓞 K) K)).comap ((LinearMap.mulLeft K (detTwK lam B⁻¹)).restrictScalars (𝓞 K))

theorem mem_twId (lam : ι → DomWeight n) (M : ι → Submodule (𝓞 K) (Fin n → K)) (a : K) :
    a ∈ twId lam M ↔ ∀ (w : HeightOneSpectrum (𝓞 K)) (B : ι → GL (Fin n) K), (∀ τ, IsBasisAt w (M τ) (B τ)) →
      detTwK lam B⁻¹ * a ∈ localization₂ w.asIdeal (1 : Submodule (𝓞 K) K) := by
  simp only [twId, Submodule.mem_iInf, Submodule.mem_comap, LinearMap.restrictScalars_apply, LinearMap.mulLeft_apply]

theorem le_localisation {W : Type} [AddCommGroup W] [Module (𝓞 K) W] (w : HeightOneSpectrum (𝓞 K)) (L : Submodule (𝓞 K) W) :
    L ≤ localization₂ w.asIdeal L := fun x hx => ⟨1, one_mem _, by rwa [one_smul]⟩

end Int

end Formalism.L2.Col
