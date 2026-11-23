module

public import Mathlib.Algebra.Module.LocalizedModule.Basic
public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.Tactic.Continuity
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
public import Mathlib.RingTheory.MvPolynomial.Ideal
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.LinearAlgebra.TensorProduct.Pi
public import Mathlib.LinearAlgebra.TensorProduct.Quotient
public import Mathlib.RingTheory.Flat.Localization

@[expose] public section

open scoped TensorProduct

namespace GlobalTheory

section Monomials

abbrev MonoDeg (ι : Type*) (a : ℕ) : Type _ := {α : ι →₀ ℕ // α.degree = a}

instance MonoDeg.finite (ι : Type*) [Finite ι] (a : ℕ) : Finite (MonoDeg ι a) :=
  (Finsupp.finite_of_degree_eq (σ := ι) a).to_subtype

noncomputable instance MonoDeg.fintype (ι : Type*) [Finite ι] (a : ℕ) : Fintype (MonoDeg ι a) :=
  Fintype.ofFinite _

theorem MonoDeg.sum_eq_sum_finsuppAntidiag {ι N : Type*} [Fintype ι] [DecidableEq ι]
    [AddCommMonoid N] (a : ℕ) (g : (ι →₀ ℕ) → N) :
    ∑ α : MonoDeg ι a, g α.1 = ∑ α ∈ Finset.finsuppAntidiag Finset.univ a, g α := by
  symm
  refine Finset.sum_subtype _ (fun α => ?_) g
  simp [Finsupp.degree_eq_sum]

theorem MonoDeg.card_eq_card_finsuppAntidiag (ι : Type*) [Fintype ι] [DecidableEq ι] (a : ℕ) :
    Fintype.card (MonoDeg ι a) = (Finset.finsuppAntidiag (Finset.univ : Finset ι) a).card := by
  have := MonoDeg.sum_eq_sum_finsuppAntidiag (ι := ι) a (fun _ => (1 : ℕ))
  simpa using this

noncomputable def MonoDeg.congr {ι κ : Type*} (e : ι ≃ κ) (a : ℕ) : MonoDeg ι a ≃ MonoDeg κ a :=
  (Finsupp.equivCongrLeft e).subtypeEquiv fun α => by
    simp [Finsupp.equivMapDomain_eq_mapDomain, Finsupp.degree_mapDomain]

variable {R : Type*} {ι : Type*}

def monoVal [CommMonoid R] (f : ι → R) (α : ι →₀ ℕ) : R := α.prod fun i k => f i ^ k

@[simp] theorem monoVal_zero [CommMonoid R] (f : ι → R) : monoVal f 0 = 1 := by
  simp [monoVal]

@[simp] theorem monoVal_single [CommMonoid R] (f : ι → R) (i : ι) (k : ℕ) :
    monoVal f (Finsupp.single i k) = f i ^ k := by
  simp [monoVal]

theorem monoVal_add [CommMonoid R] (f : ι → R) (α β : ι →₀ ℕ) :
    monoVal f (α + β) = monoVal f α * monoVal f β :=
  Finsupp.prod_add_index' (by simp) (fun _ _ _ => pow_add _ _ _)

theorem monoVal_mul [CommMonoid R] (f g : ι → R) (α : ι →₀ ℕ) :
    monoVal (fun i => f i * g i) α = monoVal f α * monoVal g α := by
  simp [monoVal, mul_pow, Finsupp.prod_mul]

theorem map_monoVal [CommMonoid R] {S F : Type*} [CommMonoid S] [FunLike F R S]
    [MonoidHomClass F R S] (φ : F) (f : ι → R) (α : ι →₀ ℕ) :
    φ (monoVal f α) = monoVal (fun i => φ (f i)) α := by
  simp [monoVal, Finsupp.prod, map_prod]

theorem monoVal_eq_eval [CommSemiring R] (f : ι → R) (α : ι →₀ ℕ) :
    monoVal f α = MvPolynomial.eval f (MvPolynomial.monomial α 1) := by
  simp [monoVal, MvPolynomial.eval_monomial]

theorem monoVal_X [CommSemiring R] (α : ι →₀ ℕ) :
    monoVal (MvPolynomial.X : ι → MvPolynomial ι R) α = MvPolynomial.monomial α 1 := by
  simp [monoVal, MvPolynomial.monomial_eq]

theorem monoVal_congr [CommMonoid R] {κ : Type*} (e : ι ≃ κ) (f : κ → R) (a : ℕ)
    (α : MonoDeg ι a) : monoVal f (MonoDeg.congr e a α).1 = monoVal (f ∘ e) α.1 := by
  simp [monoVal, MonoDeg.congr, Finsupp.prod_equivMapDomain]

variable [CommRing R]

theorem monoVal_mem_pow (f : ι → R) {a : ℕ} (α : MonoDeg ι a) :
    monoVal f α.1 ∈ Ideal.span (Set.range f) ^ a := by
  rw [Ideal.mem_span_pow_iff_exists_isHomogeneous]
  exact ⟨_, MvPolynomial.isHomogeneous_monomial 1 α.2, (monoVal_eq_eval f α.1).symm⟩

theorem span_range_pow_eq_span_monoVal (f : ι → R) (a : ℕ) :
    Ideal.span (Set.range f) ^ a =
      Ideal.span (Set.range fun α : MonoDeg ι a => monoVal f α.1) := by
  apply le_antisymm
  · intro y hy
    obtain ⟨p, hp, rfl⟩ := (Ideal.mem_span_pow_iff_exists_isHomogeneous f y).mp hy
    rw [MvPolynomial.eval_eq]
    refine Ideal.sum_mem _ fun d hd => Ideal.mul_mem_left _ _ (Ideal.subset_span ?_)
    refine ⟨⟨d, ?_⟩, rfl⟩
    have := hp (MvPolynomial.mem_support_iff.mp hd)
    rwa [Finsupp.degree_eq_weight_one]
  · rw [Ideal.span_le]
    rintro _ ⟨α, rfl⟩
    exact monoVal_mem_pow f α

variable [Finite ι] {M : Type*} [AddCommGroup M] [Module R M]

theorem mem_pow_smul_top_iff (f : ι → R) (a : ℕ) (x : M) :
    x ∈ (Ideal.span (Set.range f) ^ a • ⊤ : Submodule R M) ↔
      ∃ c : MonoDeg ι a → M, ∑ α, monoVal f α.1 • c α = x := by
  constructor
  · intro hx
    refine Submodule.smul_induction_on hx ?_ ?_
    · intro r hr m _
      rw [span_range_pow_eq_span_monoVal, Ideal.mem_span_range_iff_exists_fun] at hr
      obtain ⟨b, rfl⟩ := hr
      exact ⟨fun α => b α • m, by simp [Finset.sum_smul, mul_comm, smul_smul]⟩
    · rintro _ _ ⟨c, rfl⟩ ⟨d, rfl⟩
      exact ⟨c + d, by simp [Finset.sum_add_distrib]⟩
  · rintro ⟨c, rfl⟩
    exact Submodule.sum_mem _ fun α _ => Submodule.smul_mem_smul (monoVal_mem_pow f α) trivial

end Monomials

section Piece

variable {R : Type*} [CommRing R]

abbrev powGr (I : Ideal R) (M : Type*) [AddCommGroup M] [Module R M] (a : ℕ) : Type _ :=
  ↥(I ^ a • ⊤ : Submodule R M) ⧸
    (I ^ (a + 1) • ⊤ : Submodule R M).submoduleOf (I ^ a • ⊤ : Submodule R M)

namespace powGr

variable (I : Ideal R) (M : Type*) [AddCommGroup M] [Module R M] (a : ℕ)

def mk : ↥(I ^ a • ⊤ : Submodule R M) →ₗ[R] powGr I M a := Submodule.mkQ _

theorem mk_surjective : Function.Surjective (mk I M a) := Submodule.mkQ_surjective _


variable {I M a} in
theorem mk_eq_zero (x : ↥(I ^ a • ⊤ : Submodule R M)) :
    mk I M a x = 0 ↔ (x : M) ∈ (I ^ (a + 1) • ⊤ : Submodule R M) :=
  Submodule.Quotient.mk_eq_zero _


theorem pow_succ_smul_le : (I ^ (a + 1) • ⊤ : Submodule R M) ≤ I ^ a • ⊤ :=
  Submodule.smul_mono_left (Ideal.pow_le_pow_right (Nat.le_succ a))

theorem isTorsionBySet : Module.IsTorsionBySet R (powGr I M a) I := by
  rintro x ⟨r, hr⟩
  obtain ⟨x, rfl⟩ := mk_surjective I M a x
  change r • mk I M a x = 0
  rw [← map_smul, mk_eq_zero, pow_succ', mul_smul]
  exact Submodule.smul_mem_smul hr x.2

instance module : Module (R ⧸ I) (powGr I M a) := (isTorsionBySet I M a).module


instance isScalarTower {A : Type*} [Semiring A] [SMul A R] [IsScalarTower A R R] [Module A M]
    [IsScalarTower A R M] : IsScalarTower A (R ⧸ I) (powGr I M a) where
  smul_assoc s r x := by
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective r
    exact smul_assoc s r x


variable {M} in
def map {N : Type*} [AddCommGroup N] [Module R N] (g : M →ₗ[R] N) :
    powGr I M a →ₗ[R ⧸ I] powGr I N a :=
  LinearMap.extendScalarsOfSurjective Ideal.Quotient.mk_surjective <|
    Submodule.mapQ _ _
      (g.restrict fun _ hx => Submodule.smul_top_le_comap_smul_top (I ^ a) g hx)
      fun _ hx => Submodule.smul_top_le_comap_smul_top (I ^ (a + 1)) g hx


def toQuot : powGr I M a →ₗ[R] M ⧸ (I ^ (a + 1) • ⊤ : Submodule R M) :=
  Submodule.mapQ _ _ (Submodule.subtype _) le_rfl


variable {I M a} in
@[simp] theorem toQuot_mk (x : ↥(I ^ a • ⊤ : Submodule R M)) :
    toQuot (I := I) (M := M) (a := a) (mk I M a x) = Submodule.Quotient.mk (x : M) := rfl

theorem toQuot_injective : Function.Injective (toQuot (I := I) (M := M) (a := a)) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨x, rfl⟩ := mk_surjective I M a x
  rwa [toQuot_mk, Submodule.Quotient.mk_eq_zero, ← mk_eq_zero] at hx


variable {I a} in
def mulElem (r : R) (hr : r ∈ I ^ a) : (M ⧸ (I • ⊤ : Submodule R M)) →ₗ[R ⧸ I] powGr I M a :=
  LinearMap.extendScalarsOfSurjective Ideal.Quotient.mk_surjective <|
    Submodule.mapQ _ _
      ((LinearMap.lsmul R M r).codRestrict _ fun _ => Submodule.smul_mem_smul hr trivial)
      fun x hx => by
        change r • x ∈ (I ^ (a + 1) • ⊤ : Submodule R M)
        rw [pow_succ, mul_smul]
        exact Submodule.smul_mem_smul hr hx


variable {I M a} in
theorem mulElem_mk (r : R) (hr : r ∈ I ^ a) (x : M) :
    mulElem M r hr (Submodule.Quotient.mk x) =
      mk I M a ⟨r • x, Submodule.smul_mem_smul hr trivial⟩ := rfl

end powGr

end Piece

section Quasi

variable {R : Type*} [CommRing R] {ι : Type*} [Finite ι]

def IsQuasiRegularSeq (M : Type*) [AddCommGroup M] [Module R M] (f : ι → R) : Prop :=
  ∀ (a : ℕ) (c : MonoDeg ι a → M),
    ∑ α, monoVal f α.1 • c α ∈ (Ideal.span (Set.range f) ^ (a + 1) • ⊤ : Submodule R M) →
      ∀ α, c α ∈ (Ideal.span (Set.range f) • ⊤ : Submodule R M)

variable (M : Type*) [AddCommGroup M] [Module R M]

noncomputable def monoToPowGr (f : ι → R) (a : ℕ) :
    (MonoDeg ι a → M ⧸ (Ideal.span (Set.range f) • ⊤ : Submodule R M)) →ₗ[R ⧸
      Ideal.span (Set.range f)] powGr (Ideal.span (Set.range f)) M a :=
  ∑ α : MonoDeg ι a, powGr.mulElem M (monoVal f α.1) (monoVal_mem_pow f α) ∘ₗ LinearMap.proj α

variable {M}

theorem monoToPowGr_apply (f : ι → R) (a : ℕ)
    (c : MonoDeg ι a → M ⧸ (Ideal.span (Set.range f) • ⊤ : Submodule R M)) :
    monoToPowGr M f a c = ∑ α, powGr.mulElem M (monoVal f α.1) (monoVal_mem_pow f α) (c α) := by
  simp only [monoToPowGr, LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.proj_apply]

theorem monoToPowGr_mk (f : ι → R) (a : ℕ) (c : MonoDeg ι a → M) :
    monoToPowGr M f a (fun α => Submodule.Quotient.mk (c α)) =
      powGr.mk _ M a ⟨∑ α, monoVal f α.1 • c α, (mem_pow_smul_top_iff f a _).mpr ⟨c, rfl⟩⟩ := by
  rw [monoToPowGr_apply]
  simp only [powGr.mulElem_mk]

  rw [← map_sum]
  congr 1
  ext
  simp


variable (M) in
theorem monoToPowGr_surjective (f : ι → R) (a : ℕ) : Function.Surjective (monoToPowGr M f a) := by
  intro x
  obtain ⟨⟨x, hx⟩, rfl⟩ := powGr.mk_surjective _ M a x
  obtain ⟨c, rfl⟩ := (mem_pow_smul_top_iff f a x).mp hx
  exact ⟨_, monoToPowGr_mk f a c⟩

theorem monoToPowGr_injective_iff (f : ι → R) (a : ℕ) :
    Function.Injective (monoToPowGr M f a) ↔ ∀ c : MonoDeg ι a → M,
      ∑ α, monoVal f α.1 • c α ∈ (Ideal.span (Set.range f) ^ (a + 1) • ⊤ : Submodule R M) →
        ∀ α, c α ∈ (Ideal.span (Set.range f) • ⊤ : Submodule R M) := by
  rw [injective_iff_map_eq_zero]
  constructor
  · intro h c hc α
    have := h _ ((monoToPowGr_mk f a c).trans ((powGr.mk_eq_zero _).mpr hc))
    exact (Submodule.Quotient.mk_eq_zero _).mp (congrFun this α)
  · intro h c hc
    choose d hd using fun α => Submodule.Quotient.mk_surjective _ (c α)
    obtain rfl : c = fun α => Submodule.Quotient.mk (d α) := funext fun α => (hd α).symm
    rw [monoToPowGr_mk, powGr.mk_eq_zero] at hc
    exact funext fun α => (Submodule.Quotient.mk_eq_zero _).mpr (h d hc α)

theorem isQuasiRegularSeq_iff_injective (f : ι → R) :
    IsQuasiRegularSeq M f ↔ ∀ a, Function.Injective (monoToPowGr M f a) :=
  forall_congr' fun a => (monoToPowGr_injective_iff f a).symm

theorem isQuasiRegularSeq_iff_bijective (f : ι → R) :
    IsQuasiRegularSeq M f ↔ ∀ a, Function.Bijective (monoToPowGr M f a) :=
  (isQuasiRegularSeq_iff_injective f).trans <| forall_congr' fun a =>
    ⟨fun h => ⟨h, monoToPowGr_surjective M f a⟩, fun h => h.1⟩

theorem isQuasiRegularSeq_self_iff (f : ι → R) :
    IsQuasiRegularSeq R f ↔ ∀ (a : ℕ) (p : MvPolynomial ι R), p.IsHomogeneous a →
      MvPolynomial.eval f p ∈ Ideal.span (Set.range f) ^ (a + 1) →
        ∀ α, p.coeff α ∈ Ideal.span (Set.range f) := by
  classical
  have key : ∀ (a : ℕ) (p : MvPolynomial ι R), p.IsHomogeneous a →
      MvPolynomial.eval f p = ∑ α : MonoDeg ι a, monoVal f α.1 • p.coeff α.1 := by
    intro a p hp
    have hs := Finset.sum_subtype (p := fun α : ι →₀ ℕ => α.degree = a) (F := MonoDeg.fintype ι a)
      (Finsupp.finite_of_degree_eq (σ := ι) a).toFinset (by simp)
      (fun α => monoVal f α • p.coeff α)
    rw [← hs, MvPolynomial.eval_eq]
    rw [Finset.sum_subset (s₂ := (Finsupp.finite_of_degree_eq (σ := ι) a).toFinset)]
    · exact Finset.sum_congr rfl fun α _ => mul_comm _ _
    · intro d hd
      have := hp (MvPolynomial.mem_support_iff.mp hd)
      rw [Set.Finite.mem_toFinset, Set.mem_setOf_eq]
      rwa [Finsupp.degree_eq_weight_one]
    · intro d _ hd
      simp [MvPolynomial.notMem_support_iff.mp hd]
  simp only [IsQuasiRegularSeq, smul_eq_mul, Ideal.mul_top] at key ⊢
  constructor
  · intro h a p hp hf α
    by_cases hα : α.degree = a
    · exact h a (fun β => p.coeff β.1) (key a p hp ▸ hf) ⟨α, hα⟩
    · rw [hp.coeff_eq_zero hα]
      exact zero_mem _
  · intro h a c hc α
    have hco : ∀ β : MonoDeg ι a,
        (∑ γ : MonoDeg ι a, MvPolynomial.monomial γ.1 (c γ)).coeff β.1 = c β := by
      intro β
      simp [MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial, Subtype.val_inj]
    have hp : (∑ γ : MonoDeg ι a, MvPolynomial.monomial γ.1 (c γ)).IsHomogeneous a :=
      MvPolynomial.IsHomogeneous.sum _ _ _ fun γ _ => MvPolynomial.isHomogeneous_monomial _ γ.2
    rw [← hco α]
    refine h a _ hp ?_ _
    rw [key a _ hp]
    simpa only [hco] using hc

namespace IsQuasiRegularSeq

noncomputable def powGrEquiv {f : ι → R} (h : IsQuasiRegularSeq M f) (a : ℕ) :
    (MonoDeg ι a → M ⧸ (Ideal.span (Set.range f) • ⊤ : Submodule R M)) ≃ₗ[R ⧸
      Ideal.span (Set.range f)] powGr (Ideal.span (Set.range f)) M a :=
  LinearEquiv.ofBijective (monoToPowGr M f a) ((isQuasiRegularSeq_iff_bijective f).mp h a)

theorem comp_equiv {κ : Type*} [Finite κ] {f : ι → R} (h : IsQuasiRegularSeq M f) (e : κ ≃ ι) :
    IsQuasiRegularSeq M (f ∘ e) := by
  intro a c hc α
  rw [e.surjective.range_comp] at hc ⊢
  have := h a (fun β => c ((MonoDeg.congr e a).symm β)) (by
    rw [← (MonoDeg.congr e a).sum_comp]
    simpa only [monoVal_congr, Equiv.symm_apply_apply] using hc) (MonoDeg.congr e a α)
  simpa using this

theorem of_linearEquiv {N : Type*} [AddCommGroup N] [Module R N] {f : ι → R}
    (h : IsQuasiRegularSeq M f) (e : M ≃ₗ[R] N) : IsQuasiRegularSeq N f := by
  intro a c hc α
  have := h a (fun β => e.symm (c β)) (by
    have := Submodule.smul_top_le_comap_smul_top _ e.symm.toLinearMap hc
    simpa using this) α
  simpa using Submodule.smul_top_le_comap_smul_top _ e.toLinearMap this

end IsQuasiRegularSeq

theorem isQuasiRegularSeq_comp_equiv_iff {κ : Type*} [Finite κ] (f : ι → R) (e : κ ≃ ι) :
    IsQuasiRegularSeq M (f ∘ e) ↔ IsQuasiRegularSeq M f :=
  ⟨fun h => by simpa [Function.comp_assoc] using h.comp_equiv e.symm, fun h => h.comp_equiv e⟩

theorem isQuasiRegularSeq_of_smul_top_eq_top {f : ι → R}
    (h : (Ideal.span (Set.range f) • ⊤ : Submodule R M) = ⊤) : IsQuasiRegularSeq M f :=
  fun _ _ _ _ => by rw [h]; trivial

theorem isQuasiRegularSeq_algebraMap_iff (S : Type*) [CommRing S] [Algebra R S] [Module S M]
    [IsScalarTower R S M] (f : ι → R) :
    IsQuasiRegularSeq M (fun i => algebraMap R S (f i)) ↔ IsQuasiRegularSeq M f := by
  have hI : Ideal.span (Set.range fun i => algebraMap R S (f i)) =
      (Ideal.span (Set.range f)).map (algebraMap R S) := by
    rw [Ideal.map_span, ← Set.range_comp]
    rfl
  have hm : ∀ (J : Ideal R) (x : M),
      x ∈ (J.map (algebraMap R S) • ⊤ : Submodule S M) ↔ x ∈ (J • ⊤ : Submodule R M) := by
    intro J x
    rw [← Submodule.restrictScalars_mem R, Ideal.smul_restrictScalars, Submodule.restrictScalars_top]
  simp only [IsQuasiRegularSeq, hI, ← Ideal.map_pow, hm, ← map_monoVal, algebraMap_smul]

end Quasi

section Basis

variable {R : Type*} [CommRing R] {ι : Type*} [Finite ι]

noncomputable def quotSMulTopEquivQuot (I : Ideal R) :
    (R ⧸ (I • ⊤ : Submodule R R)) ≃ₗ[R ⧸ I] R ⧸ I :=
  LinearEquiv.extendScalarsOfSurjective Ideal.Quotient.mk_surjective <|
    Submodule.quotEquivOfEq _ _ (by simp)

noncomputable def IsQuasiRegularSeq.powGrBasis {f : ι → R} (h : IsQuasiRegularSeq R f) (a : ℕ) :
    Module.Basis (MonoDeg ι a) (R ⧸ Ideal.span (Set.range f))
      (powGr (Ideal.span (Set.range f)) R a) :=
  Module.Basis.ofEquivFun <| (h.powGrEquiv a).symm ≪≫ₗ
    LinearEquiv.piCongrRight fun _ => quotSMulTopEquivQuot _

end Basis

section Flat

variable {R : Type*} [CommRing R] {ι : Type*} [Finite ι]

noncomputable def monoToQuotPow (f : ι → R) (a : ℕ) :
    (MonoDeg ι a → R ⧸ Ideal.span (Set.range f)) →ₗ[R] R ⧸ Ideal.span (Set.range f) ^ (a + 1) :=
  ∑ α : MonoDeg ι a,
    Submodule.mapQ (Ideal.span (Set.range f)) (Ideal.span (Set.range f) ^ (a + 1))
      (LinearMap.lsmul R R (monoVal f α.1))
      (fun _ hx => by
        rw [pow_succ]
        exact Ideal.mul_mem_mul (monoVal_mem_pow f α) hx) ∘ₗ LinearMap.proj α

theorem monoToQuotPow_mk (f : ι → R) (a : ℕ) (c : MonoDeg ι a → R) :
    monoToQuotPow f a (fun α => Ideal.Quotient.mk _ (c α)) =
      Ideal.Quotient.mk _ (∑ α, monoVal f α.1 * c α) := by

  rw [monoToQuotPow, LinearMap.sum_apply, map_sum]
  rfl

variable {M : Type*} [AddCommGroup M] [Module R M]

theorem monoToPowGr_injective_iff_lTensor (f : ι → R) (a : ℕ) :
    Function.Injective (monoToPowGr M f a) ↔
      Function.Injective ((monoToQuotPow f a).lTensor M) := by
  classical
  set I := Ideal.span (Set.range f) with hI
  let e₁ : M ⊗[R] (MonoDeg ι a → R ⧸ I) ≃ₗ[R] (MonoDeg ι a → M ⧸ (I • ⊤ : Submodule R M)) :=
    TensorProduct.piRight R R M _ ≪≫ₗ
      LinearEquiv.piCongrRight fun _ => TensorProduct.tensorQuotEquivQuotSMul M I
  let e₂ := TensorProduct.tensorQuotEquivQuotSMul M (I ^ (a + 1))
  have hsq : e₂.toLinearMap ∘ₗ (monoToQuotPow f a).lTensor M =
      (powGr.toQuot (I := I) (M := M) (a := a) ∘ₗ
        (monoToPowGr M f a).restrictScalars R) ∘ₗ e₁.toLinearMap := by
    refine TensorProduct.ext' fun m c => ?_
    choose d hd using fun α => Ideal.Quotient.mk_surjective (c α)
    obtain rfl : c = fun α => Ideal.Quotient.mk I (d α) := funext fun α => (hd α).symm
    have h1 : e₁ (m ⊗ₜ fun α => Ideal.Quotient.mk I (d α)) =
        fun α => Submodule.Quotient.mk (d α • m) := by
      funext α
      exact TensorProduct.tensorQuotEquivQuotSMul_tmul_mk I m (d α)
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, h1, LinearMap.lTensor_tmul,
      LinearMap.restrictScalars_apply]
    rw [monoToQuotPow_mk, monoToPowGr_mk, powGr.toQuot_mk]
    refine (TensorProduct.tensorQuotEquivQuotSMul_tmul_mk _ m _).trans ?_
    simp [Finset.sum_smul, mul_smul]
  have hfun : e₂ ∘ (monoToQuotPow f a).lTensor M =
      (powGr.toQuot (I := I) (M := M) (a := a) ∘ monoToPowGr M f a) ∘ e₁ :=
    congrArg DFunLike.coe hsq
  rw [← e₂.injective.of_comp_iff, hfun, Function.Injective.of_comp_iff' _ e₁.bijective,
    (powGr.toQuot_injective (I := I) (M := M) (a := a)).of_comp_iff]

theorem isQuasiRegularSeq_iff_lTensor (f : ι → R) :
    IsQuasiRegularSeq M f ↔ ∀ a, Function.Injective ((monoToQuotPow f a).lTensor M) :=
  (isQuasiRegularSeq_iff_injective f).trans <| forall_congr' fun a =>
    monoToPowGr_injective_iff_lTensor f a

private theorem injective_lTensor_tensor_iff (N : Type*) [AddCommGroup N] [Module R N]
    {P Q : Type*} [AddCommGroup P] [Module R P] [AddCommGroup Q] [Module R Q] (g : P →ₗ[R] Q) :
    Function.Injective (g.lTensor (N ⊗[R] M)) ↔ Function.Injective ((g.lTensor M).lTensor N) := by
  rw [LinearMap.lTensor_tensor, LinearMap.coe_comp, LinearMap.coe_comp, LinearEquiv.coe_coe,
    LinearEquiv.coe_coe, (TensorProduct.assoc R N M Q).symm.injective.of_comp_iff,
    Function.Injective.of_comp_iff' _ (TensorProduct.assoc R N M P).bijective]

theorem IsQuasiRegularSeq.tensor {f : ι → R} (h : IsQuasiRegularSeq M f) (N : Type*)
    [AddCommGroup N] [Module R N] [Module.Flat R N] : IsQuasiRegularSeq (N ⊗[R] M) f := by
  rw [isQuasiRegularSeq_iff_lTensor] at h ⊢
  exact fun a => (injective_lTensor_tensor_iff N _).mpr
    (Module.Flat.lTensor_preserves_injective_linearMap _ (h a))

theorem IsQuasiRegularSeq.of_flat_module {f : ι → R} (h : IsQuasiRegularSeq R f) (N : Type*)
    [AddCommGroup N] [Module R N] [Module.Flat R N] : IsQuasiRegularSeq N f :=
  (h.tensor N).of_linearEquiv (TensorProduct.rid R N)

variable (S : Type*) [CommRing S] [Algebra R S]

theorem IsQuasiRegularSeq.baseChange [Module.Flat R S] {f : ι → R} (h : IsQuasiRegularSeq M f) :
    IsQuasiRegularSeq (S ⊗[R] M) fun i => algebraMap R S (f i) :=
  (isQuasiRegularSeq_algebraMap_iff S f).mpr (h.tensor S)

theorem IsQuasiRegularSeq.of_flat [Module.Flat R S] {f : ι → R} (h : IsQuasiRegularSeq R f) :
    IsQuasiRegularSeq S fun i => algebraMap R S (f i) :=
  (isQuasiRegularSeq_algebraMap_iff S f).mpr (h.of_flat_module S)

variable {N : Type*} [AddCommGroup N] [Module R N]

theorem IsQuasiRegularSeq.of_flat_of_isBaseChange [Module S N] [IsScalarTower R S N]
    [Module.Flat R S] {g : M →ₗ[R] N} (hg : IsBaseChange S g) {f : ι → R}
    (h : IsQuasiRegularSeq M f) : IsQuasiRegularSeq N fun i => algebraMap R S (f i) :=
  (h.baseChange S).of_linearEquiv hg.equiv

theorem IsQuasiRegularSeq.of_isLocalizedModule [Module S N] [IsScalarTower R S N]
    (T : Submonoid R) [IsLocalization T S] (g : M →ₗ[R] N) [IsLocalizedModule T g] {f : ι → R}
    (h : IsQuasiRegularSeq M f) : IsQuasiRegularSeq N fun i => algebraMap R S (f i) :=
  have : Module.Flat R S := IsLocalization.flat S T
  h.of_flat_of_isBaseChange S (IsLocalizedModule.isBaseChange T S g)

theorem IsQuasiRegularSeq.of_isLocalization (T : Submonoid R) [IsLocalization T S] {f : ι → R}
    (h : IsQuasiRegularSeq R f) : IsQuasiRegularSeq S fun i => algebraMap R S (f i) :=
  h.of_isLocalizedModule S T (Algebra.linearMap R S)

end Flat

section Examples

variable {R : Type*} [CommRing R]

theorem isQuasiRegularSeq_X (ι : Type*) [Finite ι] :
    IsQuasiRegularSeq (MvPolynomial ι R) (MvPolynomial.X : ι → MvPolynomial ι R) := by
  classical
  intro a c hc α
  simp only [smul_eq_mul, Ideal.mul_top, monoVal_X] at hc ⊢
  have h1 := (MvPolynomial.mem_pow_idealOfVars_iff' _ _).mp hc α.1 (by simp [α.2])
  rw [MvPolynomial.coeff_sum, Finset.sum_eq_single α] at h1
  · rw [← pow_one (Ideal.span _)]
    refine (MvPolynomial.mem_pow_idealOfVars_iff' _ _).mpr fun x hx => ?_
    obtain rfl : x = 0 := (Finsupp.degree_eq_zero_iff x).mp (by omega)
    simpa [MvPolynomial.coeff_monomial_mul'] using h1
  · intro β _ hβ
    rw [MvPolynomial.coeff_monomial_mul', if_neg]
    intro hle
    obtain ⟨γ, hγ⟩ := exists_add_of_le hle
    have hd := congrArg Finsupp.degree hγ
    rw [map_add (f := _), α.2, β.2] at hd
    obtain rfl : γ = 0 := (Finsupp.degree_eq_zero_iff γ).mp (by omega)
    exact hβ (Subtype.ext (by simpa using hγ.symm))
  · simp

noncomputable instance MonoDeg.unique (ι : Type*) [Unique ι] (a : ℕ) : Unique (MonoDeg ι a) where
  default := ⟨Finsupp.single default a, by simp⟩
  uniq α := by
    obtain ⟨α, rfl⟩ := α
    ext
    simp [Finsupp.degree_eq_sum]

theorem isQuasiRegularSeq_singleton_iff {M : Type*} [AddCommGroup M] [Module R M] (x : R) :
    IsQuasiRegularSeq M ![x] ↔
      ∀ (a : ℕ) (m m' : M), x ^ a • m = x ^ (a + 1) • m' → ∃ m'', m = x • m'' := by
  have hI : Ideal.span (Set.range ![x]) = Ideal.span {x} := by simp
  have hm : ∀ (y : R) (m : M), m ∈ (Ideal.span {y} • ⊤ : Submodule R M) ↔ ∃ m', m = y • m' := by
    intro y m
    simp [Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists, eq_comm]
  have hv : ∀ a, monoVal ![x] (default : MonoDeg (Fin 1) a).1 = x ^ a :=
    fun a => monoVal_single _ _ _
  simp only [IsQuasiRegularSeq, hI, Ideal.span_singleton_pow, hm, Fintype.sum_unique, hv,
    Unique.forall_iff]
  exact ⟨fun h a m m' hm => h a (fun _ => m) ⟨m', hm⟩, fun h a c ⟨m', hm⟩ => h a _ m' hm⟩

theorem isQuasiRegularSeq_singleton {M : Type*} [AddCommGroup M] [Module R M] {x : R}
    (hx : IsSMulRegular M x) : IsQuasiRegularSeq M ![x] :=
  (isQuasiRegularSeq_singleton_iff x).mpr fun a _ m' h =>
    ⟨m', hx.pow a (by simpa only [pow_succ, mul_smul] using h)⟩

end Examples

end GlobalTheory
