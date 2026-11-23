module

public import Formalism.LocalToGlobal.Divisibility.DivisionCompatibleToSub2Indef2
public import Formalism.LocalToGlobal.Divisibility.LiftLatLemmas
import Formalism.LocalToGlobal.Divisibility.RowLatLemmas
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Formalism.LocalToGlobal.HilbertRowConditions.CenterIdempotentAction

@[expose] public section

section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.DivisionValues Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows
open scoped Matrix

namespace GlobalTheory.CompanionTheory.MemQ

theorem iota_starProjection_Qsp {D : D7} {EE : Type} [NormedAddCommGroup EE] [InnerProductSpace ℂ EE]
    [FiniteDimensional ℂ EE] (X : RowSide D EE) (μ : D.what₂.Tup) {x : X.Amb μ} (hx : x ∈ X.V0 μ) :
    X.iota μ ((X.Qsp μ).starProjection x) = X.iota μ x := by
  have hQV : X.Qsp μ ≤ X.V0 μ := inf_le_left
  have hQU : X.Qsp μ ≤ (X.Usp μ)ᗮ := inf_le_right
  have hUV : X.Usp μ ≤ X.V0 μ := inf_le_left
  have hUker : X.Usp μ ≤ LinearMap.ker (X.iota μ) := inf_le_right
  have hUQ : X.Usp μ ≤ (X.Qsp μ)ᗮ :=
    (Submodule.le_orthogonal_orthogonal _).trans (Submodule.orthogonal_le hQU)

  set y := x - (X.Qsp μ).starProjection x with hy
  have hyV : y ∈ X.V0 μ := (X.V0 μ).sub_mem hx (hQV ((X.Qsp μ).starProjection_apply_mem x))
  have hyQ : y ∈ (X.Qsp μ)ᗮ := (X.Qsp μ).sub_starProjection_mem_orthogonal x

  set z := y - (X.Usp μ).starProjection y with hz
  have hzQ : z ∈ X.Qsp μ :=
    ⟨(X.V0 μ).sub_mem hyV (hUV ((X.Usp μ).starProjection_apply_mem y)),
      (X.Usp μ).sub_starProjection_mem_orthogonal y⟩
  have hzQ' : z ∈ (X.Qsp μ)ᗮ := (X.Qsp μ)ᗮ.sub_mem hyQ (hUQ ((X.Usp μ).starProjection_apply_mem y))
  have hz0 : z = 0 := by
    have := Submodule.inf_orthogonal_eq_bot (X.Qsp μ)
    have hmem : z ∈ X.Qsp μ ⊓ (X.Qsp μ)ᗮ := ⟨hzQ, hzQ'⟩
    rw [this] at hmem
    exact (Submodule.mem_bot ℂ).mp hmem
  have hyU : y ∈ X.Usp μ := by
    have : y = (X.Usp μ).starProjection y := sub_eq_zero.mp hz0
    rw [this]
    exact (X.Usp μ).starProjection_apply_mem y
  have hiy : X.iota μ y = 0 := hUker hyU
  have hsplit : x = (X.Qsp μ).starProjection x + y := by rw [hy]; abel
  calc X.iota μ ((X.Qsp μ).starProjection x)
      = X.iota μ ((X.Qsp μ).starProjection x) + X.iota μ y := by rw [hiy, add_zero]
    _ = X.iota μ x := by rw [← map_add (f := _), ← hsplit]

theorem RRset_eq_iota_image : ∀ (D : D7) (EE : Type) [NormedAddCommGroup EE] [InnerProductSpace ℂ EE]
    [FiniteDimensional ℂ EE] (X : RowSide D EE) (μ : D.what₂.Tup),
    X.RRset μ = X.iota μ '' ((X.Mtilde μ).carrier ∩ (X.V0 μ : Set (X.Amb μ))) := by
  intro D EE _ _ _ X μ
  unfold RowSide.RRset RowSide.LamSet
  rw [Set.image_image]
  refine Set.image_congr ?_
  rintro x ⟨-, hx⟩
  exact iota_starProjection_Qsp X μ hx

end GlobalTheory.CompanionTheory.MemQ

end

section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.DivisionValues Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows
open scoped Matrix

end

section

open NumberField
open scoped Matrix MatrixOrder ComplexOrder

noncomputable section

namespace GlobalTheory.CompanionTheory.Mem

variable {K : Type} [Field K]

structure IsCxBasis {n : ℕ} (σ : K →+* ℂ) {W : Type} [AddCommGroup W] [Module ℂ W]
    (j : (Fin n → K) →ₛₗ[σ] W) : Prop where

  li : LinearIndependent ℂ fun i => j (Pi.single i 1)

  span : Submodule.span ℂ (Set.range fun i => j (Pi.single i 1)) = ⊤

structure Chain (m : ℕ) (A B : Type) [NormedAddCommGroup A] [InnerProductSpace ℂ A]
    [NormedAddCommGroup B] [InnerProductSpace ℂ B] where

  Mult : ℕ → Type
  [inst1 : ∀ j, NormedAddCommGroup (Mult j)]
  [inst2 : ∀ j, InnerProductSpace ℂ (Mult j)]
  [inst3 : ∀ j, FiniteDimensional ℂ (Mult j)]

  zero : Mult 0 ≃ₗᵢ[ℂ] B

  top : Mult m ≃ₗᵢ[ℂ] A

  io : ∀ j, Mult (j + 1) →ₗ[ℂ] Mult j

attribute [instance] Chain.inst1 Chain.inst2 Chain.inst3

namespace Chain

variable {m : ℕ} {A B : Type} [NormedAddCommGroup A] [InnerProductSpace ℂ A]
  [NormedAddCommGroup B] [InnerProductSpace ℂ B] (C : Chain m A B)

end Chain

end GlobalTheory.CompanionTheory.Mem

end
end

section

open NumberField GlobalTheory.CompanionTheory.Mem Formalism.DivisionValues
open scoped Matrix ComplexOrder

namespace GlobalTheory.CompanionTheory.Mem

theorem semilinear_eq_sum_single {K : Type} [Field K] {σ : K →+* ℂ} {n : ℕ} {W : Type} [AddCommGroup W] [Module ℂ W]
    (j : (Fin n → K) →ₛₗ[σ] W) (x : Fin n → K) : j x = ∑ i, σ (x i) • j (Pi.single i 1) := by
  have hx : x = ∑ i, x i • (Pi.single i 1 : Fin n → K) := by
    ext k; simp [Finset.sum_apply, Pi.single_apply]
  conv_lhs => rw [hx]

  rw [map_sum]
  simp only [map_smulₛₗ]

theorem isCxBasis_coord : ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (σ : K →+* ℂ) (n : ℕ) (W : Type) [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W] (j : (Fin n → K) →ₛₗ[σ] W), IsCxBasis σ j → (∀ x, j x = ∑ i, σ (x i) • j (Pi.single i 1)) ∧ Function.Injective j ∧ Module.finrank ℂ W = n := by
  intro K _ _ _ σ n W _ _ _ j hj
  have hco : ∀ x, j x = ∑ i, σ (x i) • j (Pi.single i 1) := fun x => semilinear_eq_sum_single j x
  refine ⟨hco, ?_, ?_⟩
  · rw [injective_iff_map_eq_zero]
    intro x hx
    rw [hco x] at hx
    have h0 := Fintype.linearIndependent_iff.mp hj.li (fun i => σ (x i)) hx
    funext i
    exact (map_eq_zero σ).mp (h0 i)
  · rw [Module.finrank_eq_card_basis (Module.Basis.mk hj.li hj.span.ge)]
    simp

end GlobalTheory.CompanionTheory.Mem

end

section

open NumberField GlobalTheory.CompanionTheory.Mem Formalism.DivisionValues Formalism.L2.DIV
open scoped Matrix ComplexOrder

namespace GlobalTheory.CompanionTheory.Mem

private theorem rv0_projection_identities {K : Type} [Field K] {n d d0 : ℕ} (A L : Matrix (Fin n) (Fin n) K)
    (E : Matrix (Fin n) (Fin d) K) (Pr : Matrix (Fin d) (Fin n) K)
    (E0 : Matrix (Fin n) (Fin d0) K) (Pr0 : Matrix (Fin d0) (Fin n) K)
    (hPE : Pr * E = 1) (hEP : E * Pr = L) (hP0 : Pr0 * E0 = 1) (hE0 : E0 * Pr0 = A * L)
    (hLAL : L * (A * L) = A * L) :
    Pr * A * E * (Pr * E0) = Pr * E0 ∧ E * (Pr * E0) = E0 ∧ E * (Pr * A * E) = A * E ∧
      E0 * Pr0 * E = A * E ∧ Pr * E0 * (Pr0 * E) = Pr * A * E := by
  have hLE : L * E = E := by rw [← hEP, Matrix.mul_assoc, hPE, Matrix.mul_one]
  have hALE0 : A * L * E0 = E0 := by rw [← hE0, Matrix.mul_assoc, hP0, Matrix.mul_one]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · calc Pr * A * E * (Pr * E0) = Pr * (A * (E * Pr)) * E0 := by simp only [Matrix.mul_assoc]
      _ = Pr * (E0 * Pr0) * E0 := by rw [hEP, hE0]
      _ = Pr * E0 * (Pr0 * E0) := by simp only [Matrix.mul_assoc]
      _ = Pr * E0 := by rw [hP0, Matrix.mul_one]
  · calc E * (Pr * E0) = L * (A * L * E0) := by rw [hALE0, ← Matrix.mul_assoc, hEP]
      _ = L * (A * L) * E0 := by simp only [Matrix.mul_assoc]
      _ = E0 := by rw [hLAL, hALE0]
  · calc E * (Pr * A * E) = L * A * (L * E) := by rw [hLE, ← hEP]; simp only [Matrix.mul_assoc]
      _ = L * (A * L) * E := by simp only [Matrix.mul_assoc]
      _ = A * E := by rw [hLAL, Matrix.mul_assoc, hLE]
  · rw [hE0, Matrix.mul_assoc, hLE]
  · calc Pr * E0 * (Pr0 * E) = Pr * (E0 * Pr0) * E := by simp only [Matrix.mul_assoc]
      _ = Pr * A * (L * E) := by rw [hE0]; simp only [Matrix.mul_assoc]
      _ = Pr * A * E := by rw [hLE]

end GlobalTheory.CompanionTheory.Mem

end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.DivisionValues Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows
open scoped Matrix

namespace GlobalTheory.CompanionTheory.MemQ

private theorem gaMat_mul {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] [Fintype G]
    {Pl0 : Type} (B : BlockDat K G Pl0) (a b : MonoidAlgebra K G) :
    B.S.gaMat B.r (a * b) = B.S.gaMat B.r a * B.S.gaMat B.r b := by
  rw [CSD.gaMat_eq_toMatrix, CSD.gaMat_eq_toMatrix, CSD.gaMat_eq_toMatrix, ← LinearMap.toMatrix_mul]
  congr 1
  exact LinearMap.ext fun φ => BlockDat.gaOp_mul B a b φ

private theorem v0_int_lemma_5 {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] [Fintype G]
    {Pl0 : Type} (B : BlockDat K G Pl0) (ℓ : Lvl K G) (v0 : InfinitePlace K) (s : ℕ) (hB : BlockHyp B ℓ v0 s)
    {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W] (σ : K →+* ℂ)
    (j : (Fin (B.S.lvlDim B.r ℓ.P ℓ.ψ) → K) →ₛₗ[σ] W) (op : W →ₗ[ℂ] W) (hop : op ∘ₗ op = op)
    {O : Type} [CommRing O] {φO : O →+* ℂ} (M : Formalism.BasicNotions.Rows.OLat O φO W)
    (H : Matrix (Fin (B.S.lvlDim B.r ℓ.P ℓ.ψ)) (Fin (B.S.lvlDim B.r ℓ.P ℓ.ψ)) K)
    (hF : FormsTie σ j H (B.S.lvlOp B.r ℓ.P ℓ.ψ (idemOf ℓ.X)) op)
    (hM : OLatTie σ M j (B.S.lvlNab B.r ℓ.P ℓ.ψ)) (x : W) :
    ((∃ c : W → 𝓞 K, x = ∑ v ∈ M.gen, σ (c v : K) • v) ∧ x ∈ LinearMap.range op) ↔
      ∃ F ∈ B.Mt ℓ, x = j ((B.S.lvlPr B.r ℓ.P ℓ.ψ * B.vE ℓ).mulVec F) := by
  obtain ⟨⟨hPE, -⟩, hEP⟩ := BlockDat.lf_lvl_proj hB
  obtain ⟨⟨hP0E0, -⟩, hE0P0⟩ := BlockDat.lf_v_proj hB
  have hE0 : B.vE ℓ * B.vPr ℓ = B.S.gaMat B.r (idemOf ℓ.X) * B.S.gaMat B.r (lvlIdem ℓ.P ℓ.ψ) :=
    hE0P0.trans (gaMat_mul B _ _)
  have hLAL : B.S.gaMat B.r (lvlIdem ℓ.P ℓ.ψ) *
      (B.S.gaMat B.r (idemOf ℓ.X) * B.S.gaMat B.r (lvlIdem ℓ.P ℓ.ψ)) =
      B.S.gaMat B.r (idemOf ℓ.X) * B.S.gaMat B.r (lvlIdem ℓ.P ℓ.ψ) := by
    rw [← gaMat_mul, ← gaMat_mul]
    exact congrArg (B.S.gaMat B.r) (BlockDat.lf_lvl_mul_good hB)
  obtain ⟨hM1, hM2, hM3, hM4, hM5⟩ := GlobalTheory.CompanionTheory.Mem.rv0_projection_identities _ _ _ _ _ _ hPE hEP hP0E0 hE0 hLAL

  have hM1' : B.S.lvlOp B.r ℓ.P ℓ.ψ (idemOf ℓ.X) * (B.S.lvlPr B.r ℓ.P ℓ.ψ * B.vE ℓ) =
      B.S.lvlPr B.r ℓ.P ℓ.ψ * B.vE ℓ := hM1
  have hM3' : B.S.lvlE B.r ℓ.P ℓ.ψ * B.S.lvlOp B.r ℓ.P ℓ.ψ (idemOf ℓ.X) =
      B.S.gaMat B.r (idemOf ℓ.X) * B.S.lvlE B.r ℓ.P ℓ.ψ := hM3
  have hM5' : B.S.lvlPr B.r ℓ.P ℓ.ψ * B.vE ℓ * (B.vPr ℓ * B.S.lvlE B.r ℓ.P ℓ.ψ) =
      B.S.lvlOp B.r ℓ.P ℓ.ψ (idemOf ℓ.X) := hM5
  have hinj : Function.Injective j :=
    (GlobalTheory.CompanionTheory.Mem.isCxBasis_coord K σ _ W j ⟨hF.li, hF.span⟩).2.1
  constructor
  · rintro ⟨⟨c, hc⟩, z, hz⟩

    have hgen : ∀ v ∈ M.gen, ∃ y, j y = v := hM.1
    choose! pre hpre using hgen
    have hjy : j (∑ v ∈ M.gen, (c v : K) • pre v) = x := by

      rw [map_sum, hc]
      refine Finset.sum_congr rfl fun v hv => ?_
      rw [map_smulₛₗ, hpre v hv]
    set y := ∑ v ∈ M.gen, (c v : K) • pre v with hy
    have hyN : (B.S.lvlE B.r ℓ.P ℓ.ψ).mulVec y ∈ B.S.nabLat := (hM.2 y).2 ⟨c, by rw [hjy, hc]⟩

    have hfix : (B.S.lvlOp B.r ℓ.P ℓ.ψ (idemOf ℓ.X)).mulVec y = y := by
      apply hinj
      rw [← hF.op_eq, hjy, ← hz]
      exact LinearMap.congr_fun hop z
    have hAE : (B.S.gaMat B.r (idemOf ℓ.X) * B.S.lvlE B.r ℓ.P ℓ.ψ).mulVec y =
        (B.S.lvlE B.r ℓ.P ℓ.ψ).mulVec y := by
      conv_rhs => rw [← hfix]
      rw [Matrix.mulVec_mulVec, hM3']
    refine ⟨(B.vPr ℓ * B.S.lvlE B.r ℓ.P ℓ.ψ).mulVec y, ?_, ?_⟩
    · show (B.vE ℓ).mulVec ((B.vPr ℓ * B.S.lvlE B.r ℓ.P ℓ.ψ).mulVec y) ∈ B.S.nabLat
      rw [Matrix.mulVec_mulVec, ← Matrix.mul_assoc, hM4, hAE]
      exact hyN
    · rw [Matrix.mulVec_mulVec, hM5', hfix, hjy]
  · rintro ⟨F, hF0, rfl⟩
    have hyN : (B.S.lvlPr B.r ℓ.P ℓ.ψ * B.vE ℓ).mulVec F ∈ B.S.lvlNab B.r ℓ.P ℓ.ψ := by
      show (B.S.lvlE B.r ℓ.P ℓ.ψ).mulVec ((B.S.lvlPr B.r ℓ.P ℓ.ψ * B.vE ℓ).mulVec F) ∈ B.S.nabLat
      rw [Matrix.mulVec_mulVec, hM2]
      exact hF0
    refine ⟨(hM.2 _).1 hyN, j ((B.S.lvlPr B.r ℓ.P ℓ.ψ * B.vE ℓ).mulVec F), ?_⟩
    rw [hF.op_eq, Matrix.mulVec_mulVec, hM1']

theorem integral_iff_matrix_indefinite_side : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (m : ℕ) (A : FamIn D.what₂.LL G Pl0 T m) (EE : Type) [NormedAddCommGroup EE] [InnerProductSpace ℂ EE] [FiniteDimensional ℂ EE] (X : RowSide D EE) (P : Subgroup G) (ψ : P →* D.what₂.LLˣ) (Zs : DefSub A.fam.amb) (S : IndefData (A.side P ψ Zs)) (tup : T → D.what₂.Tup) (eRR : (Fin S.D → D.what₂.LL) ≃ₗ[D.what₂.LL] X.RR.V) (jA : ∀ t, (Fin (rDim D A P ψ t) → D.what₂.LL) →ₛₗ[D.what₂.embLL] X.Amb (tup t)) (s : ℕ), A.fam.Ok s → RowSideDef3 D A X P ψ Zs S tup eRR jA → ∀ (t : T) (x : X.Amb (tup t)), ((∃ c : X.Amb (tup t) → 𝓞 D.what₂.LL, x = ∑ v ∈ (X.Mtilde (tup t)).gen, D.what₂.embLL (c v : D.what₂.LL) • v) ∧ x ∈ X.V0 (tup t)) ↔ ∃ F ∈ (A.side P ψ Zs).Mt t, x = jA t ((rV0 D A P ψ t).mulVec F) := by
  intro D G _ _ Pl0 T m A EE _ _ _ X P ψ Zs S tup eRR jA s hOk hX t x
  exact v0_int_lemma_5 (A.fam.R t) (A.fam.lvl P ψ) A.fam.v0 s ⟨hOk.conj, hOk.irr, hOk.what₂ t⟩ D.what₂.embLL (jA t)
    (X.eOp (tup t)) (X.eOp_idem (tup t)) (X.Mtilde (tup t)) _ (hX.forms t) (hX.Mtilde t) x

end GlobalTheory.CompanionTheory.MemQ

end

section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.DivisionValues Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows
open scoped Matrix

end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.DivisionValues Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows
open scoped Matrix

namespace GlobalTheory.CompanionTheory.MemQ

private theorem jEE_injective' {D : D7} {EE : Type} [NormedAddCommGroup EE] [InnerProductSpace ℂ EE]
    [FiniteDimensional ℂ EE] (X : RowSide D EE) : Function.Injective X.jEE := by
  rw [injective_iff_map_eq_zero]
  intro y hy
  have hsum : y = ∑ i, X.RR.b.repr y i • X.RR.b i := (X.RR.b.sum_repr y).symm

  rw [hsum, map_sum] at hy
  simp only [map_smulₛₗ] at hy
  have h0 := Fintype.linearIndependent_iff.mp X.jEE_basis.1 _ hy
  rw [hsum]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [(map_eq_zero D.what₂.embLL).mp (h0 i), zero_smul]

private theorem span_le_lemma_8 (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (m : ℕ) (A : FamIn D.what₂.LL G Pl0 T m)
    (EE : Type) [NormedAddCommGroup EE] [InnerProductSpace ℂ EE] [FiniteDimensional ℂ EE] (X : RowSide D EE)
    (P : Subgroup G) (ψ : P →* D.what₂.LLˣ) (Zs : DefSub A.fam.amb) (S : IndefData (A.side P ψ Zs))
    (tup : T → D.what₂.Tup) (eRR : (Fin S.D → D.what₂.LL) ≃ₗ[D.what₂.LL] X.RR.V)
    (jA : ∀ t, (Fin (rDim D A P ψ t) → D.what₂.LL) →ₛₗ[D.what₂.embLL] X.Amb (tup t)) (s : ℕ) (hOk : A.fam.Ok s) (hX : RowSideDef3 D A X P ψ Zs S tup eRR jA)
    (t : T) :
    Submodule.span (𝓞 D.what₂.LL) {y : X.RR.V | X.jEE y ∈ X.RRset (tup t)} ≤
      (matLat (S.ι t) ((A.side P ψ Zs).abelian₂ t)).map
        ((eRR : (Fin S.D → D.what₂.LL) →ₗ[D.what₂.LL] X.RR.V).restrictScalars (𝓞 D.what₂.LL)) := by
  rw [Submodule.span_le]
  intro y hy
  change X.jEE y ∈ X.RRset (tup t) at hy
  rw [RRset_eq_iota_image] at hy
  obtain ⟨u, ⟨⟨c, hc⟩, hu⟩, hiu⟩ := hy

  obtain ⟨F, hF, rfl⟩ := (integral_iff_matrix_indefinite_side D G Pl0 T m A EE X P ψ Zs S tup eRR jA s hOk hX t u).1
    ⟨⟨fun v => ⟨D.what₂.OtoLL (c v), D.O_int (c v)⟩, hc⟩, hu⟩
  rw [hX.iota t F] at hiu
  exact Submodule.mem_map.mpr ⟨_, ⟨_, ⟨F, hF, rfl⟩, rfl⟩, jEE_injective' X hiu⟩

private theorem le_span_lemma_9 (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (m : ℕ) (A : FamIn D.what₂.LL G Pl0 T m)
    (EE : Type) [NormedAddCommGroup EE] [InnerProductSpace ℂ EE] [FiniteDimensional ℂ EE] (X : RowSide D EE)
    (P : Subgroup G) (ψ : P →* D.what₂.LLˣ) (Zs : DefSub A.fam.amb) (S : IndefData (A.side P ψ Zs))
    (tup : T → D.what₂.Tup) (eRR : (Fin S.D → D.what₂.LL) ≃ₗ[D.what₂.LL] X.RR.V)
    (jA : ∀ t, (Fin (rDim D A P ψ t) → D.what₂.LL) →ₛₗ[D.what₂.embLL] X.Amb (tup t)) (s : ℕ) (hOk : A.fam.Ok s) (hX : RowSideDef3 D A X P ψ Zs S tup eRR jA)
    (t : T)
    (hint : ∀ x : X.Amb (tup t), ((∃ c : X.Amb (tup t) → 𝓞 D.what₂.LL,
        x = ∑ v ∈ (X.Mtilde (tup t)).gen, D.what₂.embLL (c v : D.what₂.LL) • v) ∧ x ∈ X.V0 (tup t)) →
      ∃ (s : Finset (X.Amb (tup t))) (c : X.Amb (tup t) → 𝓞 D.what₂.LL),
        (s : Set (X.Amb (tup t))) ⊆ (X.Mtilde (tup t)).carrier ∩ (X.V0 (tup t) : Set (X.Amb (tup t))) ∧
          x = ∑ y ∈ s, D.what₂.embLL (c y : D.what₂.LL) • y) :
    (matLat (S.ι t) ((A.side P ψ Zs).abelian₂ t)).map
        ((eRR : (Fin S.D → D.what₂.LL) →ₗ[D.what₂.LL] X.RR.V).restrictScalars (𝓞 D.what₂.LL)) ≤
      Submodule.span (𝓞 D.what₂.LL) {y : X.RR.V | X.jEE y ∈ X.RRset (tup t)} := by
  intro y hy
  obtain ⟨w, ⟨q, ⟨F, hF, rfl⟩, rfl⟩, rfl⟩ := hy
  have hx := (integral_iff_matrix_indefinite_side D G Pl0 T m A EE X P ψ Zs S tup eRR jA s hOk hX t
    (jA t ((rV0 D A P ψ t).mulVec F))).2 ⟨F, hF, rfl⟩
  obtain ⟨s', c, hs', hxs⟩ := hint _ hx

  have hpt : ∀ u ∈ s', ∃ z : X.RR.V, X.jEE z = X.iota (tup t) u := by
    intro u hu
    obtain ⟨⟨c', hc'⟩, hu0⟩ := hs' hu
    obtain ⟨F', -, rfl⟩ := (integral_iff_matrix_indefinite_side D G Pl0 T m A EE X P ψ Zs S tup eRR jA s hOk hX t u).1
      ⟨⟨fun v => ⟨D.what₂.OtoLL (c' v), D.O_int (c' v)⟩, hc'⟩, hu0⟩
    exact ⟨_, (hX.iota t F').symm⟩
  choose! z hz using hpt
  have key : eRR ((S.ι t).mulVec (((A.side P ψ Zs).Pq t).mulVec F)) =
      ∑ u ∈ s', (c u : D.what₂.LL) • z u := by
    apply jEE_injective' X

    rw [← hX.iota t F, hxs, map_sum, map_sum]
    refine Finset.sum_congr rfl fun u hu => ?_
    rw [LinearMap.map_smul, map_smulₛₗ, hz u hu]
  have hsm : ∀ (a : 𝓞 D.what₂.LL) (v : X.RR.V), (a : D.what₂.LL) • v = a • v := fun a v => by
    rw [← smul_one_smul D.what₂.LL a v, Algebra.smul_def, mul_one]
  show eRR ((S.ι t).mulVec (((A.side P ψ Zs).Pq t).mulVec F)) ∈ _
  rw [key]
  refine Submodule.sum_mem _ fun u hu => ?_
  rw [hsm]
  refine Submodule.smul_mem _ _ (Submodule.subset_span ?_)
  show X.jEE (z u) ∈ X.RRset (tup t)
  rw [hz u hu, RRset_eq_iota_image]
  exact ⟨u, hs' hu, rfl⟩

theorem span_ratPoints_eq_matLat : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (m : ℕ) (A : FamIn D.what₂.LL G Pl0 T m) (EE : Type) [NormedAddCommGroup EE] [InnerProductSpace ℂ EE] [FiniteDimensional ℂ EE] (X : RowSide D EE) (P : Subgroup G) (ψ : P →* D.what₂.LLˣ) (Zs : DefSub A.fam.amb) (S : IndefData (A.side P ψ Zs)) (tup : T → D.what₂.Tup) (eRR : (Fin S.D → D.what₂.LL) ≃ₗ[D.what₂.LL] X.RR.V) (jA : ∀ t, (Fin (rDim D A P ψ t) → D.what₂.LL) →ₛₗ[D.what₂.embLL] X.Amb (tup t)) (s : ℕ), A.fam.Ok s → RowSideDef3 D A X P ψ Zs S tup eRR jA → ∀ (t : T), (∀ x : X.Amb (tup t), ((∃ c : X.Amb (tup t) → 𝓞 D.what₂.LL, x = ∑ v ∈ (X.Mtilde (tup t)).gen, D.what₂.embLL (c v : D.what₂.LL) • v) ∧ x ∈ X.V0 (tup t)) → ∃ (s : Finset (X.Amb (tup t))) (c : X.Amb (tup t) → 𝓞 D.what₂.LL), (s : Set (X.Amb (tup t))) ⊆ (X.Mtilde (tup t)).carrier ∩ (X.V0 (tup t) : Set (X.Amb (tup t))) ∧ x = ∑ y ∈ s, D.what₂.embLL (c y : D.what₂.LL) • y) → Submodule.span (𝓞 D.what₂.LL) {y : X.RR.V | X.jEE y ∈ X.RRset (tup t)} = (matLat (S.ι t) ((A.side P ψ Zs).abelian₂ t)).map ((eRR : (Fin S.D → D.what₂.LL) →ₗ[D.what₂.LL] X.RR.V).restrictScalars (𝓞 D.what₂.LL)) := by
  intro D G _ _ Pl0 T m A EE _ _ _ X P ψ Zs S tup eRR jA s hOk hX t hint
  exact le_antisymm (span_le_lemma_8 D G Pl0 T m A EE X P ψ Zs S tup eRR jA s hOk hX t)
    (le_span_lemma_9 D G Pl0 T m A EE X P ψ Zs S tup eRR jA s hOk hX t hint)

end GlobalTheory.CompanionTheory.MemQ

end

section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.DivisionValues Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows
open scoped Matrix

end

section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.DivisionValues Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows
open scoped Matrix

namespace GlobalTheory.CompanionTheory.MemQ

private theorem mem_glued_lemma_10 (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (m : ℕ) (A : FamIn D.what₂.LL G Pl0 T m)
    (EE : Type) [NormedAddCommGroup EE] [InnerProductSpace ℂ EE] [FiniteDimensional ℂ EE] (X : RowSide D EE)
    (P : Subgroup G) (ψ : P →* D.what₂.LLˣ) (Zs : DefSub A.fam.amb) (S : IndefData (A.side P ψ Zs))
    (tup : T → D.what₂.Tup) (eRR : (Fin S.D → D.what₂.LL) ≃ₗ[D.what₂.LL] X.RR.V)
    (hmu : ∀ w, D.what₂.muAt w = tup (S.μ (D.plEq w)))
    (hspan : ∀ t : T, (∃ w, t = S.μ w) →
      Submodule.span (𝓞 D.what₂.LL) {y : X.RR.V | X.jEE y ∈ X.RRset (tup t)} =
        (matLat (S.ι t) ((A.side P ψ Zs).abelian₂ t)).map
          ((eRR : (Fin S.D → D.what₂.LL) →ₗ[D.what₂.LL] X.RR.V).restrictScalars (𝓞 D.what₂.LL)))
    (x : X.RR.V) :
    (∀ w : D.what₂.places.Pl, ∃ d : 𝓞 D.what₂.LL, d ∉ (D.plEq w).asIdeal ∧
      d • x ∈ Submodule.span (𝓞 D.what₂.LL) {y | X.jEE y ∈ X.RRset (D.what₂.muAt w)}) ↔
      x ∈ S.RR.map ((eRR : (Fin S.D → D.what₂.LL) →ₗ[D.what₂.LL] X.RR.V).restrictScalars (𝓞 D.what₂.LL)) := by
  have hsm : ∀ (a : 𝓞 D.what₂.LL) (v : X.RR.V), (a : D.what₂.LL) • v = a • v := fun a v => by
    rw [← smul_one_smul D.what₂.LL a v, Algebra.smul_def, mul_one]
  have hsym : ∀ (a : 𝓞 D.what₂.LL) (v : X.RR.V), eRR.symm (a • v) = a • eRR.symm v := fun a v => by
    rw [← hsm, LinearEquiv.map_smul]
    rfl
  have hmap : ∀ (L : Submodule (𝓞 D.what₂.LL) (Fin S.D → D.what₂.LL)) (v : X.RR.V),
      v ∈ L.map ((eRR : (Fin S.D → D.what₂.LL) →ₗ[D.what₂.LL] X.RR.V).restrictScalars (𝓞 D.what₂.LL)) ↔
        eRR.symm v ∈ L := by
    intro L v
    constructor
    · rintro ⟨z, hz, rfl⟩
      simpa using hz
    · intro h
      exact ⟨_, h, by simp⟩

  have hloc : ∀ w : D.what₂.places.Pl,
      Submodule.span (𝓞 D.what₂.LL) {y : X.RR.V | X.jEE y ∈ X.RRset (D.what₂.muAt w)} =
        (matLat (S.ι (S.μ (D.plEq w))) ((A.side P ψ Zs).abelian₂ (S.μ (D.plEq w)))).map
          ((eRR : (Fin S.D → D.what₂.LL) →ₗ[D.what₂.LL] X.RR.V).restrictScalars (𝓞 D.what₂.LL)) := fun w => by
    rw [hmu w]
    exact hspan _ ⟨_, rfl⟩
  rw [hmap]
  simp only [hloc, hmap, hsym]
  simp only [IndefData.RR, glueLat, Submodule.mem_iInf]
  constructor
  · intro h w'
    obtain ⟨d, hd, hdx⟩ := h (D.plEq.symm w')
    rw [Equiv.apply_symm_apply] at hd hdx
    exact ⟨d, hd, hdx⟩
  · intro h w
    exact h (D.plEq w)

theorem rrDef_iff_glued : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (m : ℕ) (A : FamIn D.what₂.LL G Pl0 T m) (EE : Type) [NormedAddCommGroup EE] [InnerProductSpace ℂ EE] [FiniteDimensional ℂ EE] (X : RowSide D EE) (P : Subgroup G) (ψ : P →* D.what₂.LLˣ) (Zs : DefSub A.fam.amb) (S : IndefData (A.side P ψ Zs)) (tup : T → D.what₂.Tup) (eRR : (Fin S.D → D.what₂.LL) ≃ₗ[D.what₂.LL] X.RR.V) (jA : ∀ t, (Fin (rDim D A P ψ t) → D.what₂.LL) →ₛₗ[D.what₂.embLL] X.Amb (tup t)), (∀ w, D.what₂.muAt w = tup (S.μ (D.plEq w))) → (∀ t : T, (∃ w, t = S.μ w) → Submodule.span (𝓞 D.what₂.LL) {y : X.RR.V | X.jEE y ∈ X.RRset (tup t)} = (matLat (S.ι t) ((A.side P ψ Zs).abelian₂ t)).map ((eRR : (Fin S.D → D.what₂.LL) →ₗ[D.what₂.LL] X.RR.V).restrictScalars (𝓞 D.what₂.LL))) → (X.RRDef ↔ X.RR.L = S.RR.map ((eRR : (Fin S.D → D.what₂.LL) →ₗ[D.what₂.LL] X.RR.V).restrictScalars (𝓞 D.what₂.LL))) := by
  intro D G _ _ Pl0 T m A EE _ _ _ X P ψ Zs S tup eRR jA hmu hspan
  have key := GlobalTheory.CompanionTheory.MemQ.mem_glued_lemma_10 D G Pl0 T m A EE X P ψ Zs S tup eRR hmu hspan
  unfold RowSide.RRDef
  constructor
  · intro h
    ext x
    rw [← key x]
    exact h x
  · intro h x
    rw [h]
    exact (key x).symm

end GlobalTheory.CompanionTheory.MemQ

end

section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.DivisionValues Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows
open scoped Matrix

end

section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.DivisionValues Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows
open scoped Matrix

namespace GlobalTheory.CompanionTheory.MemQ

theorem rr_lat_of_rowSide : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (m : ℕ) (A : FamIn D.what₂.LL G Pl0 T m) (EE : Type) [NormedAddCommGroup EE] [InnerProductSpace ℂ EE] [FiniteDimensional ℂ EE] (X : RowSide D EE) (P : Subgroup G) (ψ : P →* D.what₂.LLˣ) (Zs : DefSub A.fam.amb) (S : IndefData (A.side P ψ Zs)) (tup : T → D.what₂.Tup) (eRR : (Fin S.D → D.what₂.LL) ≃ₗ[D.what₂.LL] X.RR.V) (jA : ∀ t, (Fin (rDim D A P ψ t) → D.what₂.LL) →ₛₗ[D.what₂.embLL] X.Amb (tup t)) (s : ℕ), A.fam.Ok s → RowSideDef3 D A X P ψ Zs S tup eRR jA → (∀ w, D.what₂.muAt w = tup (S.μ (D.plEq w))) → (∀ w, (∀ x : X.Amb (D.what₂.muAt w), ((∃ c : X.Amb (D.what₂.muAt w) → 𝓞 D.what₂.LL, x = ∑ v ∈ (X.Mtilde (D.what₂.muAt w)).gen, D.what₂.embLL (c v : D.what₂.LL) • v) ∧ x ∈ X.V0 (D.what₂.muAt w)) → ∃ (s : Finset (X.Amb (D.what₂.muAt w))) (c : X.Amb (D.what₂.muAt w) → 𝓞 D.what₂.LL), (s : Set (X.Amb (D.what₂.muAt w))) ⊆ (X.Mtilde (D.what₂.muAt w)).carrier ∩ (X.V0 (D.what₂.muAt w) : Set (X.Amb (D.what₂.muAt w))) ∧ x = ∑ y ∈ s, D.what₂.embLL (c y : D.what₂.LL) • y)) → (X.RRDef ↔ X.RR.L = S.RR.map ((eRR : (Fin S.D → D.what₂.LL) →ₗ[D.what₂.LL] X.RR.V).restrictScalars (𝓞 D.what₂.LL))) := by
  intro D G _ _ Pl0 T m A EE _ _ _ X P ψ Zs S tup eRR jA s hOk hX hmu hint
  refine rrDef_iff_glued D G Pl0 T m A EE X P ψ Zs S tup eRR jA hmu ?_
  rintro t ⟨w', rfl⟩
  apply span_ratPoints_eq_matLat D G Pl0 T m A EE X P ψ Zs S tup eRR jA s hOk hX
  have h := hint (D.plEq.symm w')
  rw [hmu, Equiv.apply_symm_apply] at h
  exact h

end GlobalTheory.CompanionTheory.MemQ

end

section
open Formalism.BasicNotions NumberField IsDedekindDomain Matrix Formalism.L2.DIV Formalism.L2.Indef
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.Twist

theorem oLat_add_mem {O : Type} [CommRing O] {φ : O →+* ℂ} {V : Type} [AddCommGroup V] [Module ℂ V]
    (L : Formalism.BasicNotions.Rows.OLat O φ V) {x y : V} (hx : x ∈ L.carrier) (hy : y ∈ L.carrier) :
    x + y ∈ L.carrier := by
  obtain ⟨c, rfl⟩ := hx
  obtain ⟨d, rfl⟩ := hy
  refine ⟨c + d, ?_⟩
  simp [add_smul, Finset.sum_add_distrib]

theorem oLat_zero_mem {O : Type} [CommRing O] {φ : O →+* ℂ} {V : Type} [AddCommGroup V] [Module ℂ V]
    (L : Formalism.BasicNotions.Rows.OLat O φ V) : (0 : V) ∈ L.carrier := by
  exact ⟨0, by simp⟩

theorem oLat_gen_mem {O : Type} [CommRing O] {φ : O →+* ℂ} {V : Type} [AddCommGroup V] [Module ℂ V]
    (L : Formalism.BasicNotions.Rows.OLat O φ V) {v : V} (hv : v ∈ L.gen) : v ∈ L.carrier := by
  classical
  refine ⟨fun w => if w = v then 1 else 0, ?_⟩
  simp [hv]

private theorem exists_finset_sum_of_mem_V0_Mtilde {D : D7} {EE : Type} [NormedAddCommGroup EE] [InnerProductSpace ℂ EE]
    [FiniteDimensional ℂ EE] (X : RowSide D EE)
    (hstab : ∀ μ (a : 𝓞 D.what₂.LL), ∀ y ∈ (X.Mtilde μ).carrier,
      D.what₂.embLL (a : D.what₂.LL) • y ∈ (X.Mtilde μ).carrier)
    (μ : D.what₂.Tup) (x : X.Amb μ)
    (hx : (∃ c : X.Amb μ → 𝓞 D.what₂.LL, x = ∑ v ∈ (X.Mtilde μ).gen, D.what₂.embLL (c v : D.what₂.LL) • v) ∧
      x ∈ X.V0 μ) :
    ∃ (s : Finset (X.Amb μ)) (c : X.Amb μ → 𝓞 D.what₂.LL),
      (s : Set (X.Amb μ)) ⊆ (X.Mtilde μ).carrier ∩ (X.V0 μ : Set (X.Amb μ)) ∧
        x = ∑ y ∈ s, D.what₂.embLL (c y : D.what₂.LL) • y := by
  classical
  obtain ⟨⟨c, hc⟩, hx0⟩ := hx

  have hxM : x ∈ (X.Mtilde μ).carrier := by
    rw [hc]
    exact Finset.sum_induction _ (· ∈ (X.Mtilde μ).carrier) (fun a b ha hb => oLat_add_mem _ ha hb)
      (oLat_zero_mem _) fun v hv => hstab μ (c v) v (oLat_gen_mem _ hv)
  refine ⟨{x}, fun _ => 1, ?_, ?_⟩
  · intro y hy
    rw [Finset.coe_singleton, Set.mem_singleton_iff] at hy
    subst hy
    exact ⟨hxM, hx0⟩
  · simp

end GlobalTheory.CompanionTheory.Twist

end

section
open Formalism.BasicNotions NumberField IsDedekindDomain Matrix Formalism.L2.DIV Formalism.L2.Indef
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
theorem _root_.GlobalTheory.Adopt.indefinite_side_row_lattice_adopted : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (m : ℕ) (A : FamIn D.what₂.LL G Pl0 T m) (s : ℕ)
    (EE : Type) [NormedAddCommGroup EE] [InnerProductSpace ℂ EE] [FiniteDimensional ℂ EE] (X : RowSide D EE)
    (P : Subgroup G) (ψ : P →* D.what₂.LLˣ) (Zs : DefSub A.fam.amb) (S : IndefData (A.side P ψ Zs)) (tup : T → D.what₂.Tup)
    (eRR : (Fin S.D → D.what₂.LL) ≃ₗ[D.what₂.LL] X.RR.V)
    (jA : ∀ t, (Fin (rDim D A P ψ t) → D.what₂.LL) →ₛₗ[D.what₂.embLL] X.Amb (tup t)),
    A.fam.Ok s → RowSideDef3 D A X P ψ Zs S tup eRR jA → X.RRDef → (∀ w, D.what₂.muAt w = tup (S.μ (D.plEq w))) →
    (∀ μ (a : 𝓞 D.what₂.LL), ∀ y ∈ (X.Mtilde μ).carrier, D.what₂.embLL (a : D.what₂.LL) • y ∈ (X.Mtilde μ).carrier) →
    X.RR.L = S.RR.map ((eRR : (Fin S.D → D.what₂.LL) →ₗ[D.what₂.LL] X.RR.V).restrictScalars (𝓞 D.what₂.LL)) := by
  intro D G _ _ Pl0 T m A s EE _ _ _ X P ψ Zs S tup eRR jA hOk hX hRR hmu hstab
  refine (GlobalTheory.CompanionTheory.MemQ.rr_lat_of_rowSide D G Pl0 T m A EE X P ψ Zs S tup eRR jA s hOk hX hmu ?_).mp hRR
  intro w x hx
  exact GlobalTheory.CompanionTheory.Twist.exists_finset_sum_of_mem_V0_Mtilde X hstab _ x hx

end
