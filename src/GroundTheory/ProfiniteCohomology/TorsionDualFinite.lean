module

public import GroundTheory.ProfiniteCohomology.TorsionDualDefs
public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.Fourier.FiniteAbelian.Orthogonality
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Algebra.Category.Grp.Injective
public import Mathlib.Algebra.Module.CharacterModule

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open Function

namespace QZ

theorem finite_setOf_nsmul_eq_zero {n : ℕ} (hn : 0 < n) : {x : QZ | n • x = 0}.Finite :=
  AddCircle.finite_torsion (1 : ℚ) hn

noncomputable def toReal : QZ →+ AddCircle (1 : ℝ) :=
  (QuotientAddGroup.map (AddSubgroup.zmultiples (1 : ℚ)) (AddSubgroup.zmultiples (1 : ℝ))
    (Rat.castHom ℝ).toAddMonoidHom (by
      rw [AddSubgroup.zmultiples_le]
      exact ⟨1, by simp⟩)).comp toAddCircle.toAddMonoidHom

theorem toReal_mk (q : ℚ) : toReal (mk q) = ((q : ℝ) : AddCircle (1 : ℝ)) :=
  rfl

theorem toReal_injective : Injective toReal := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨q, rfl⟩ := mk_surjective x
  rw [toReal_mk, AddCircle.coe_eq_zero_iff] at hx
  obtain ⟨n, hn⟩ := hx
  rw [mk_eq_zero_iff]
  refine ⟨n, ?_⟩
  have : ((n : ℚ) : ℝ) = (q : ℝ) := by simpa using hn
  exact_mod_cast this

noncomputable def toComplex (x : QZ) : ℂ :=
  (AddCircle.toCircle (toReal x) : ℂ)

theorem toComplex_injective : Injective toComplex := fun _ _ h =>
  toReal_injective (AddCircle.injective_toCircle one_ne_zero (Circle.ext h))

@[simp]
theorem toComplex_zero : toComplex 0 = 1 := by
  simp [toComplex]

theorem toComplex_add (x y : QZ) : toComplex (x + y) = toComplex x * toComplex y := by
  simp [toComplex, AddCircle.toCircle_add]

variable {G H : Type*} [AddCommGroup G] [AddCommGroup H]

noncomputable def toAddChar (f : G →+ QZ) : AddChar G ℂ where
  toFun g := toComplex (f g)
  map_zero_eq_one' := by simp
  map_add_eq_mul' a b := by simp [toComplex_add]

theorem toAddChar_injective : Injective (toAddChar (G := G)) := fun _ _ h =>
  AddMonoidHom.ext fun a => toComplex_injective (DFunLike.congr_fun h a)

theorem exists_comp_eq_of_injective (i : G →+ H) (hi : Injective i) (f : G →+ QZ) :
    ∃ g : H →+ QZ, g.comp i = f := by
  obtain ⟨g, hg⟩ := (Module.Baer.of_divisible (AddCircle (1 : ℚ))).extension_property_addMonoidHom
    i hi (toAddCircle.toAddMonoidHom.comp f)
  refine ⟨toAddCircle.symm.toAddMonoidHom.comp g, AddMonoidHom.ext fun a => ?_⟩
  have h1 := DFunLike.congr_fun hg a
  simp only [AddMonoidHom.coe_comp, comp_apply, AddEquiv.coe_toAddMonoidHom] at h1 ⊢
  rw [h1, AddEquiv.symm_apply_apply]

theorem exists_comp_eq_of_ker_le (h : G →+ H) (χ : G →+ QZ) (hχ : h.ker ≤ χ.ker) :
    ∃ ψ : H →+ QZ, ψ.comp h = χ := by
  let χ₀ : h.range →+ QZ := (QuotientAddGroup.lift h.ker χ hχ).comp
    (QuotientAddGroup.quotientKerEquivRange h).symm.toAddMonoidHom
  obtain ⟨ψ, hψ⟩ := exists_comp_eq_of_injective h.range.subtype h.range.subtype_injective χ₀
  refine ⟨ψ, AddMonoidHom.ext fun a => ?_⟩
  have h1 := DFunLike.congr_fun hψ ⟨h a, a, rfl⟩
  have h2 : (QuotientAddGroup.quotientKerEquivRange h).symm ⟨h a, a, rfl⟩ =
      (a : G ⧸ h.ker) := by
    rw [AddEquiv.symm_apply_eq]
    rfl
  simp only [AddMonoidHom.coe_comp, comp_apply, AddSubgroup.coe_subtype, χ₀,
    AddEquiv.coe_toAddMonoidHom, h2] at h1
  simpa using h1

theorem exists_apply_ne_zero {a : G} (ha : a ≠ 0) : ∃ f : G →+ QZ, f a ≠ 0 := by
  obtain ⟨c, hc⟩ := CharacterModule.exists_character_apply_ne_zero_of_ne_zero ha
  refine ⟨toAddCircle.symm.toAddMonoidHom.comp (c : G →+ AddCircle (1 : ℚ)), fun h => hc ?_⟩
  exact (AddEquiv.map_eq_zero_iff toAddCircle.symm).mp h


variable (G) in
def evalHom : G →+ ((G →+ QZ) →+ QZ) where
  toFun a :=
    { toFun := fun f => f a
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  map_zero' := by ext f; simp
  map_add' a b := by ext f; simp

theorem evalHom_injective : Injective (evalHom (G := G)) := by
  rw [injective_iff_map_eq_zero]
  intro a ha
  by_contra hne
  obtain ⟨f, hf⟩ := exists_apply_ne_zero hne
  exact hf (DFunLike.congr_fun ha f)

instance [Finite G] : Finite (G →+ QZ) :=
  Finite.of_injective _ toAddChar_injective

theorem card_hom_le [Finite G] : Nat.card (G →+ QZ) ≤ Nat.card G := by
  have := Fintype.ofFinite G
  calc Nat.card (G →+ QZ) ≤ Nat.card (AddChar G ℂ) :=
        Nat.card_le_card_of_injective _ toAddChar_injective
    _ ≤ Nat.card G := by
        rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
        exact AddChar.card_addChar_le G ℂ

theorem card_hom [Finite G] : Nat.card (G →+ QZ) = Nat.card G :=
  card_hom_le.antisymm <| (Nat.card_le_card_of_injective _ evalHom_injective).trans card_hom_le


end QZ

namespace QZDual

variable {N : Type*} [AddCommGroup N] [TopologicalSpace N] [DiscreteTopology N]

end QZDual

end GroundTheory.ProfCoh
