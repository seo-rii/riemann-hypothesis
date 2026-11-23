module

public import Formalism.HermitianLattices.StatementMass
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.DefiniteUnimodularPlaneSplitAlongVector
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.DefClassNum
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LayerProd
import Formalism.SharpRestriction.CuspSpanNormBounds.Point

@[expose] public section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas
namespace GlobalTheory.PlaneSplit

private theorem planeSplit_of_lattice : ∀ (E : Type) [Field E] [NumberField E] [StarRing E], Formalism.HermitianLatticesTheory.IsCMUnram E → ∀ (J : Matrix (Fin 2) (Fin 2) E), Jᴴ = J → (∀ (φ : E →+* ℂ) (y : Fin 2 → E), y ≠ 0 → 0 < (φ (star y ⬝ᵥ (J *ᵥ y))).re) → ∀ Λ : Submodule (𝓞 E) (Fin 2 → E), Submodule.IsLattice E Λ → (∀ x, x ∈ Λ ↔ ∀ y ∈ Λ, star y ⬝ᵥ (J *ᵥ x) ∈ (algebraMap (𝓞 E) E).range) → ∀ u ∈ Λ, u ≠ 0 → ∀ ρ : ℝ, (∀ φ : E →+* ℂ, (φ (star u ⬝ᵥ (J *ᵥ u))).re ≤ ρ) → ∃ (γ : GL (Fin 2) E) (β₁ β₂ : E) (N₁ N₂ : Submodule (𝓞 E) E) (𝔫 : Ideal (𝓞 E)), (γ : Matrix (Fin 2) (Fin 2) E)ᴴ * J * (γ : Matrix (Fin 2) (Fin 2) E) = Matrix.diagonal ![β₁, β₂] ∧ star β₁ = β₁ ∧ star β₂ = β₂ ∧ (∀ φ : E →+* ℂ, 0 < (φ β₁).re ∧ 0 < (φ β₂).re) ∧ Submodule.IsFullLattice E N₁ ∧ Submodule.IsFullLattice E N₂ ∧ (∀ t, t ∈ N₁ ↔ (γ : Matrix (Fin 2) (Fin 2) E) *ᵥ ![t, 0] ∈ Λ) ∧ (∀ t, t ∈ N₂ ↔ (γ : Matrix (Fin 2) (Fin 2) E) *ᵥ ![0, t] ∈ Λ) ∧ Submodule.span (𝓞 E) {t | ∃ x ∈ N₁, ∃ y ∈ N₁, t = star x * β₁ * y} = Submodule.map (Algebra.linearMap (𝓞 E) E) 𝔫 ∧ Submodule.span (𝓞 E) {t | ∃ x ∈ N₂, ∃ y ∈ N₂, t = star x * β₂ * y} = Submodule.map (Algebra.linearMap (𝓞 E) E) 𝔫 ∧ 𝔫 ≠ ⊥ ∧ 𝔫 = Ideal.span {t | t ∈ 𝔫 ∧ star (t : E) = t} ∧ (Ideal.absNorm 𝔫 : ℝ) ≤ ρ ^ (2 * Formalism.HermitianLatticesTheory.fDeg E) := by
  intro E _ _ _ hE J hJ hpos Λ hΛ hdual u hu hu0 ρ hρ
  have hne : ∀ y : Fin 2 → E, y ≠ 0 → star y ⬝ᵥ (J *ᵥ y) ≠ 0 := by
    intro y hy h
    obtain ⟨φ⟩ : Nonempty (E →+* ℂ) := inferInstance
    have := hpos φ y hy
    rw [h] at this
    simp at this
  set v := star u ᵥ* J with hv
  let w : Fin 2 → E := ![-v 1, v 0]
  have huw : star u ⬝ᵥ (J *ᵥ w) = 0 := by
    rw [dotProduct_mulVec, ← hv]; simp [w, dotProduct, Fin.sum_univ_two]; ring
  have hwu : star w ⬝ᵥ (J *ᵥ u) = 0 := by rw [← herm_star J hJ, huw, star_zero]
  set β₁ := star u ⬝ᵥ (J *ᵥ u) with hβ₁
  set β₂ := star w ⬝ᵥ (J *ᵥ w) with hβ₂
  have h10 : β₁ ≠ 0 := hne u hu0
  have hb1 : β₁ = v 0 * u 0 + v 1 * u 1 := by
    rw [hβ₁, dotProduct_mulVec, ← hv]; simp [dotProduct, Fin.sum_univ_two]
  have hw0 : w ≠ 0 := by
    intro h
    have a0 := congrFun h 0
    have a1 := congrFun h 1
    simp [w] at a0 a1
    exact h10 (by rw [hb1, a0, a1]; ring)
  have h20 : β₂ ≠ 0 := hne w hw0
  have h1 : star β₁ = β₁ := herm_star J hJ u u
  have h2 : star β₂ = β₂ := herm_star J hJ w w
  let G : Matrix (Fin 2) (Fin 2) E := Matrix.of fun i j => ![u, w] j i
  have hG : G.det ≠ 0 := by
    rw [Matrix.det_fin_two]
    simp only [G, w, Matrix.of_apply]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    intro h; apply h10; rw [hb1, ← h]; ring
  have hGv : ∀ a b : E, G *ᵥ ![a, b] = a • u + b • w := by
    intro a b; ext i; simp [G, mulVec, dotProduct, Fin.sum_univ_two, mul_comm]
  have hGJ : Gᴴ * J * G = Matrix.diagonal ![β₁, β₂] := by
    have : ∀ i j, (Gᴴ * J * G) i j = star (![u, w] i) ⬝ᵥ (J *ᵥ (![u, w] j)) := by
      intro i j
      simp [G, Matrix.mul_apply, mulVec, dotProduct, Fin.sum_univ_two]; ring
    ext i j
    rw [this]
    fin_cases i <;> fin_cases j
    exacts [rfl, huw, hwu, rfl]
  let f : (E × E) →ₗ[E] (Fin 2 → E) :=
    (LinearMap.toSpanSingleton E _ u).coprod (LinearMap.toSpanSingleton E _ w)
  have hf : ∀ x : E × E, f x = x.1 • u + x.2 • w := fun x => rfl
  have hpair : ∀ x y : E × E, star (f y) ⬝ᵥ (J *ᵥ f x) = star y.1 * β₁ * x.1 + star y.2 * β₂ * x.2 := by
    intro x y
    rw [hf, hf]
    simp only [star_add, star_smul, mulVec_add, mulVec_smul, add_dotProduct, dotProduct_add, smul_dotProduct,
      dotProduct_smul, huw, hwu, ← hβ₁, ← hβ₂, smul_eq_mul]
    ring
  have hinj : Function.Injective f := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    have a0 := hpair x (1, 0)
    have a1 := hpair x (0, 1)
    simp [hx, h10, h20] at a0 a1
    exact Prod.ext a0 a1
  have hsurj : Function.Surjective f :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (by simp)).1 hinj
  let L : Submodule (𝓞 E) (E × E) := Λ.comap (f.restrictScalars (𝓞 E))
  have hLm : ∀ x, x ∈ L ↔ f x ∈ Λ := fun x => Iff.rfl
  have hLfg : L.FG := by
    apply Submodule.fg_of_fg_map_injective (f.restrictScalars (𝓞 E)) hinj
    rw [Submodule.map_comap_eq_of_surjective (f := f.restrictScalars (𝓞 E)) hsurj]
    exact hΛ.fg
  have hu1 : ((1, 0) : E × E) ∈ L := by rw [hLm, hf]; simpa using hu
  have hq : ∃ x ∈ L, x.2 ≠ 0 := by
    by_contra h
    push Not at h
    have hwmem : f (0, 1) ∈ Λ := by
      apply (hdual _).2
      intro y hy
      obtain ⟨z, rfl⟩ := hsurj y
      have hz : z.2 = 0 := h z hy
      rw [hpair]
      simp [hz]
    have := h (0, 1) hwmem
    simp at this
  have hL : ∀ x, x ∈ L ↔ ∀ y ∈ L, IsIntegral ℤ (star y.1 * β₁ * x.1 + star y.2 * β₂ * x.2) := by
    intro x
    rw [hLm, hdual]
    constructor
    · intro h y hy
      rw [← hpair, ← mem_range_iff]; exact h _ hy
    · intro h y hy
      obtain ⟨y, rfl⟩ := hsurj y
      rw [mem_range_iff, hpair]; exact h y hy
  obtain ⟨A, B, 𝔫, hA, hB, hA', hB', hS, hT, hfix⟩ :=
    diag_split β₁ β₂ h1 h2 h10 h20 L hLfg ⟨_, hu1, one_ne_zero⟩ hq hL
  have hβn : β₁ ∈ Submodule.map (Algebra.linearMap (𝓞 E) E) 𝔫 := by
    rw [← hS]
    exact Submodule.subset_span ⟨1, (hA' 1).2 hu1, 1, (hA' 1).2 hu1, by simp⟩
  obtain ⟨b, hb, hbβ⟩ := hβn
  have hbβ' : (b : E) = β₁ := hbβ
  have hb0 : b ≠ 0 := by
    rintro rfl
    exact h10 (by rw [← hbβ']; rfl)
  refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero G hG, β₁, β₂, A, B, 𝔫, hGJ, h1, h2,
    fun φ => ⟨hpos φ u hu0, hpos φ w hw0⟩, hA, hB, fun t => ?_, fun t => ?_, hS, hT, ?_, hfix, ?_⟩
  · rw [hA', hLm, hf]
    change _ ↔ G *ᵥ _ ∈ Λ
    rw [hGv]
  · rw [hB', hLm, hf]
    change _ ↔ G *ᵥ _ ∈ Λ
    rw [hGv]
  · rintro rfl
    exact hb0 hb
  · refine absNorm_le hE.1 𝔫 b hb hb0 ρ fun φ => ?_
    rw [hbβ']
    have him : (φ β₁).im = 0 := by
      have := hE.2.1 φ β₁
      rw [h1] at this
      exact Complex.conj_eq_iff_im.1 this.symm
    rw [← Complex.abs_re_eq_norm.2 him, abs_of_pos (hpos φ u hu0)]
    exact hρ φ


end GlobalTheory.PlaneSplit


theorem _root_.GlobalTheory.T.definiteUnimodularPlane_split_along_vector : ∀ (E : Type) [Field E] [NumberField E] [StarRing E], Formalism.HermitianLatticesTheory.IsCMUnram E → ∀ (J : Matrix (Fin 2) (Fin 2) E), Jᴴ = J → (∀ (φ : E →+* ℂ) (y : Fin 2 → E), y ≠ 0 → 0 < (φ (star y ⬝ᵥ (J *ᵥ y))).re) → ∀ Λ : Submodule (𝓞 E) (Fin 2 → E), Submodule.IsLattice E Λ → (∀ x, x ∈ Λ ↔ ∀ y ∈ Λ, star y ⬝ᵥ (J *ᵥ x) ∈ (algebraMap (𝓞 E) E).range) → ∀ u ∈ Λ, u ≠ 0 → ∀ ρ : ℝ, (∀ φ : E →+* ℂ, (φ (star u ⬝ᵥ (J *ᵥ u))).re ≤ ρ) → ∃ (γ : GL (Fin 2) E) (β₁ β₂ : E) (N₁ N₂ : Submodule (𝓞 E) E) (𝔫 : Ideal (𝓞 E)), (γ : Matrix (Fin 2) (Fin 2) E)ᴴ * J * (γ : Matrix (Fin 2) (Fin 2) E) = Matrix.diagonal ![β₁, β₂] ∧ star β₁ = β₁ ∧ star β₂ = β₂ ∧ (∀ φ : E →+* ℂ, 0 < (φ β₁).re ∧ 0 < (φ β₂).re) ∧ Submodule.IsLattice E N₁ ∧ Submodule.IsLattice E N₂ ∧ (∀ t, t ∈ N₁ ↔ (γ : Matrix (Fin 2) (Fin 2) E) *ᵥ ![t, 0] ∈ Λ) ∧ (∀ t, t ∈ N₂ ↔ (γ : Matrix (Fin 2) (Fin 2) E) *ᵥ ![0, t] ∈ Λ) ∧ Submodule.span (𝓞 E) {t | ∃ x ∈ N₁, ∃ y ∈ N₁, t = star x * β₁ * y} = Submodule.map (Algebra.linearMap (𝓞 E) E) 𝔫 ∧ Submodule.span (𝓞 E) {t | ∃ x ∈ N₂, ∃ y ∈ N₂, t = star x * β₂ * y} = Submodule.map (Algebra.linearMap (𝓞 E) E) 𝔫 ∧ 𝔫 ≠ ⊥ ∧ 𝔫 = Ideal.span {t | t ∈ 𝔫 ∧ star (t : E) = t} ∧ (Ideal.absNorm 𝔫 : ℝ) ≤ ρ ^ (2 * Formalism.HermitianLatticesTheory.fDeg E) := by
  intro E _ _ _ hE J hJ hpos Λ hΛ hdual u hu hu0 ρ hρ
  obtain ⟨γ, β₁, β₂, N₁, N₂, 𝔫, hγ, hβ₁, hβ₂, hpos', hN₁, hN₂, hrest⟩ :=
    GlobalTheory.PlaneSplit.planeSplit_of_lattice E hE J hJ hpos Λ hΛ hdual u hu hu0 ρ hρ
  exact ⟨γ, β₁, β₂, N₁, N₂, 𝔫, hγ, hβ₁, hβ₂, hpos', hN₁.toIsLattice, hN₂.toIsLattice, hrest⟩
