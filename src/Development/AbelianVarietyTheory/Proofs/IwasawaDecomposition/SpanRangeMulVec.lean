module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PlaceCharacterEqReferenceIff
public import Formalism.LocalToGlobal.Divisibility.ClassSumLemmas
public import Formalism.LocalToGlobal.Divisibility.LiftLatLemmas
import Formalism.LocalToGlobal.Divisibility.ProjLemmas
import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.AuxStatement14
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH NumberField IsDedekindDomain Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.DivisionValues
open scoped InnerProductSpace Matrix

namespace GlobalTheory.Mem.LiftForms

section Core

variable {K V M : Type} [Field K] {σ : K →+* ℂ} [AddCommGroup V] [Module K V]
  [NormedAddCommGroup M] [InnerProductSpace ℂ M] [FiniteDimensional ℂ M]


omit [FiniteDimensional ℂ M] in
theorem inner_of_norm_sq {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (f : M →ₗ[ℂ] H) {n : ℝ} (hn : 0 < n)
    (h : ∀ x, ‖f x‖ ^ 2 = n * ‖x‖ ^ 2) (x y : M) : inner ℂ (f x) (f y) = (n : ℂ) * inner ℂ x y := by
  have hs : 0 < Real.sqrt n := Real.sqrt_pos.2 hn
  have h1 : ∀ x, ‖((((Real.sqrt n)⁻¹ : ℝ) : ℂ) • f) x‖ = ‖x‖ := by
    intro x
    have h2 : ‖f x‖ = Real.sqrt n * ‖x‖ := by
      rw [← sq_eq_sq₀ (norm_nonneg _) (by positivity), h, mul_pow, Real.sq_sqrt hn.le]
    rw [LinearMap.smul_apply, norm_smul, h2, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
    field_simp
  have h3 := (LinearMap.norm_map_iff_inner_map_map _).1 h1 x y
  rw [LinearMap.smul_apply, LinearMap.smul_apply, inner_smul_left, inner_smul_right, Complex.conj_ofReal, ← mul_assoc,
    ← Complex.ofReal_mul, ← mul_inv, Real.mul_self_sqrt hn.le] at h3
  rw [← h3, ← mul_assoc, ← Complex.ofReal_mul, mul_inv_cancel₀ hn.ne']
  simp

omit [FiniteDimensional ℂ M] in
theorem inj_of_norm_sq {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (f : M →ₗ[ℂ] H) {n : ℝ} (hn : 0 < n)
    (h : ∀ x, ‖f x‖ ^ 2 = n * ‖x‖ ^ 2) : Function.Injective f := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  have := h x
  rw [hx, norm_zero] at this
  have h2 : ‖x‖ ^ 2 = 0 := by
    rcases mul_eq_zero.1 (show n * ‖x‖ ^ 2 = 0 by rw [← this]; simp) with h | h
    · exact absurd h hn.ne'
    · exact h
  simpa using h2

end Core

section Coord

variable {K : Type} [Field K] [NumberField K] [StarRing K]

theorem hform_dot {n : ℕ} (H : Matrix (Fin n) (Fin n) K) (x y : Fin n → K) : hform H x y = star x ⬝ᵥ H *ᵥ y := by
  simp only [hform, Matrix.toLinearMapₛₗ₂'_apply, starRingEnd_apply, RingHom.id_apply, smul_eq_mul, dotProduct, Matrix.mulVec,
    Pi.star_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem hform_mulVec {n a b : ℕ} (H : Matrix (Fin n) (Fin n) K) (E : Matrix (Fin n) (Fin a) K) (E' : Matrix (Fin n) (Fin b) K)
    (x : Fin a → K) (y : Fin b → K) : hform H (E *ᵥ x) (E' *ᵥ y) = star x ⬝ᵥ (Eᴴ * H * E') *ᵥ y := by
  rw [hform_dot, Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]

theorem hform_orth {n d : ℕ} {H : Matrix (Fin n) (Fin n) K} {E : Matrix (Fin n) (Fin d) K} {Pr : Matrix (Fin d) (Fin n) K}
    (h : IsOrthProj H E Pr) (z : Fin d → K) (x : Fin n → K) : hform H (E *ᵥ z) (E *ᵥ (Pr *ᵥ x)) = hform H (E *ᵥ z) x := by
  have h1 := hform_mulVec H E (1 - E * Pr) z x
  rw [h.2, Matrix.zero_mulVec, dotProduct_zero, Matrix.sub_mulVec, Matrix.one_mulVec, map_sub, sub_eq_zero,
    ← Matrix.mulVec_mulVec] at h1
  exact h1.symm

variable (S : CSD K) {G : Type} [Group G] [Fintype G] (r : Representation K G S.Forms)

theorem csum_hform (x y : Fin S.dim → K) :
    S.csum (S.basis.equivFun.symm x : S.Forms) (S.basis.equivFun.symm y : S.Forms) = hform S.H x y :=
  (S.isClassSum x y).symm

theorem act_coord (t : G) (x : Fin S.dim → K) :
    r t (S.basis.equivFun.symm x) = S.basis.equivFun.symm (S.actMat r t *ᵥ x) :=
  Subtype.ext (S.I_actMat r t x).symm

theorem gaOp_coord (a : MonoidAlgebra K G) (x : Fin S.dim → K) :
    S.gaOp r a (S.basis.equivFun.symm x) = S.basis.equivFun.symm (S.gaMat r a *ᵥ x) := by

  simp only [CSD.gaOp, CSD.gaMat, LinearMap.sum_apply, LinearMap.smul_apply, Matrix.sum_mulVec, Matrix.smul_mulVec, map_sum,
  map_smul, act_coord]

def lvlForm (P : Subgroup G) (ψ : P →* Kˣ) : (Fin (S.lvlDim r P ψ) → K) →ₗ[K] S.Forms :=
  (S.basis.equivFun.symm : (Fin S.dim → K) →ₗ[K] S.Forms) ∘ₗ (S.lvlE r P ψ).mulVecLin

theorem lvlForm_apply (P : Subgroup G) (ψ : P →* Kˣ) (x : Fin (S.lvlDim r P ψ) → K) :
    lvlForm S r P ψ x = S.basis.equivFun.symm (S.lvlE r P ψ *ᵥ x) := rfl

theorem lvlForm_injective (P : Subgroup G) (ψ : P →* Kˣ) : Function.Injective (lvlForm S r P ψ) :=
  S.basis.equivFun.symm.injective.comp (image_idempotent_spec K _ _).1

theorem range_lvlE (P : Subgroup G) (ψ : P →* Kˣ) : LinearMap.range (S.lvlE r P ψ).mulVecLin = S.lvlPart r P ψ :=
  (image_idempotent_spec K _ _).2.trans (level_part_spec K S G r P ψ)

theorem range_lvlForm (P : Subgroup G) (ψ : P →* Kˣ) : Set.range (lvlForm S r P ψ) = lvlForms S r P ψ := by
  ext f
  obtain ⟨u, rfl⟩ := S.basis.equivFun.symm.surjective f
  have key : S.basis.equivFun.symm u ∈ lvlForms S r P ψ ↔ u ∈ S.lvlPart r P ψ := by
    refine forall_congr' fun h => ?_
    rw [act_coord, ← map_smul, S.basis.equivFun.symm.injective.eq_iff]
  rw [key, ← range_lvlE]
  constructor
  · rintro ⟨x, hx⟩
    exact ⟨x, S.basis.equivFun.symm.injective hx⟩
  · rintro ⟨x, rfl⟩
    exact ⟨x, rfl⟩

theorem csum_lvlForm (P : Subgroup G) (ψ : P →* Kˣ) (x y : Fin (S.lvlDim r P ψ) → K) :
    S.csum (lvlForm S r P ψ x) (lvlForm S r P ψ y) = (Nat.card P : K) * hform (S.lvlH r P ψ) x y := by
  have hc : (Nat.card P : K) ≠ 0 := by exact_mod_cast (Nat.card_pos (α := P)).ne'
  rw [lvlForm_apply, lvlForm_apply, csum_hform, hform_mulVec, hform_dot, CSD.lvlH, Matrix.smul_mulVec, dotProduct_smul,
    smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ hc, one_mul]
  rfl

theorem mem_lvlNab (P : Subgroup G) (ψ : P →* Kˣ) (x : Fin (S.lvlDim r P ψ) → K) :
    x ∈ S.lvlNab r P ψ ↔ lvlForm S r P ψ x ∈ intForms S := by
  unfold CSD.lvlNab CSD.cutNab CSD.nabLat
  rw [exponent_index_lattice.mem_cutLat, mem_valLatF]
  rfl

end Coord

section Block

variable {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] [Fintype G] {Pl0 : Type}
  {B : BlockDat K G Pl0} {ℓ : Lvl K G} {Z : Submodule K B.S.Forms} {v0 : InfinitePlace K} {s : ℕ}

theorem lvlE_lvlOp (h : BlockHyp B ℓ v0 s) (x : Fin (B.S.lvlDim B.r ℓ.P ℓ.ψ) → K) :
    B.S.lvlE B.r ℓ.P ℓ.ψ *ᵥ (B.S.lvlOp B.r ℓ.P ℓ.ψ (idemOf ℓ.X) *ᵥ x) =
      B.S.gaMat B.r (idemOf ℓ.X) *ᵥ (B.S.lvlE B.r ℓ.P ℓ.ψ *ᵥ x) := by
  have hc := (idempotent_spec K v0 h.conj G ℓ.X h.irr).2 (lvlIdem ℓ.P ℓ.ψ)
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
    (level_operator_spec K v0 h.conj B.S (h.ok.hpos v0) G B.r h.ok.act ℓ.P ℓ.ψ _ hc.symm).1]

theorem lvlE_lE (h : BlockHyp B ℓ v0 s) (z : Fin (B.dZ ℓ Z) → K) :
    B.S.lvlE B.r ℓ.P ℓ.ψ *ᵥ (B.lE ℓ Z *ᵥ z) = B.vE ℓ *ᵥ (B.zE ℓ Z *ᵥ z) := by
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, BlockDat.lf_lvlE_lE h]
  rfl

theorem lvlForm_lE (h : BlockHyp B ℓ v0 s) (z : Fin (B.dZ ℓ Z) → K) :
    lvlForm B.S B.r ℓ.P ℓ.ψ (B.lE ℓ Z *ᵥ z) = B.toF ℓ Z z := by
  rw [lvlForm_apply, lvlE_lE h]
  rfl

theorem range_vE (h : BlockHyp B ℓ v0 s) : LinearMap.range (B.vE ℓ).mulVecLin =
    LinearMap.range (B.S.gaMat B.r (idemOf ℓ.X)).mulVecLin ⊓ B.S.lvlPart B.r ℓ.P ℓ.ψ :=
  good_part_spec K B.S G B.r ℓ.X h.irr ℓ.P ℓ.ψ

theorem lvlOp_lE (h : BlockHyp B ℓ v0 s) (z : Fin (B.dZ ℓ Z) → K) :
    B.S.lvlOp B.r ℓ.P ℓ.ψ (idemOf ℓ.X) *ᵥ (B.lE ℓ Z *ᵥ z) = B.lE ℓ Z *ᵥ z := by
  apply BlockDat.lf_lvlE_inj
  show B.S.lvlE B.r ℓ.P ℓ.ψ *ᵥ _ = B.S.lvlE B.r ℓ.P ℓ.ψ *ᵥ _
  rw [lvlE_lvlOp h, lvlE_lE h]
  have hm : B.vE ℓ *ᵥ (B.zE ℓ Z *ᵥ z) ∈ LinearMap.range (B.vE ℓ).mulVecLin := ⟨_, rfl⟩
  rw [range_vE h] at hm
  obtain ⟨⟨u, hu⟩, -⟩ := hm
  rw [← hu, Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, ← (group_action_matrix_hom K B.S G B.r).2,
    (idempotent_spec K v0 h.conj G ℓ.X h.irr).1.idem]

theorem span_range_mulVec {σ : K →+* ℂ} {M : Type} [AddCommGroup M] [Module ℂ M] {n d : ℕ} (J : (Fin n → K) →ₛₗ[σ] M)
    (E : Matrix (Fin n) (Fin d) K) :
    Submodule.span ℂ (J '' Set.range fun z => E *ᵥ z) = Submodule.span ℂ (Set.range fun k => J (E *ᵥ Pi.single k 1)) := by
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨_, ⟨z, rfl⟩, rfl⟩
    have hz : z = ∑ k, z k • (Pi.single k 1 : Fin d → K) := by
      ext i; simp [Pi.single_apply]
    rw [SetLike.mem_coe]
    beta_reduce

    rw [hz, Matrix.mulVec_sum, map_sum]
    refine Submodule.sum_mem _ fun k _ => ?_
    rw [Matrix.mulVec_smul, map_smulₛₗ]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)
  · apply Submodule.span_mono
    rintro _ ⟨k, rfl⟩
    exact ⟨_, ⟨_, rfl⟩, rfl⟩

variable {σ : K →+* ℂ} {H M ML : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup M] [InnerProductSpace ℂ M] [FiniteDimensional ℂ M] [AddCommGroup ML] [Module K ML]



end Block

end GlobalTheory.Mem.LiftForms

end
