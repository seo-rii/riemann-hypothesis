module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsEtLevZero
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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

@[expose] public section

noncomputable section

namespace GlobalTheory.UPel.HT.EtLev.Cmp

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.EtLev

variable {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {b : Base D R} {N : ℕ}
  {k : Type} [Field k] [IsAlgClosed k] {s : Sp k ⟶ Sp R} {o : Obj b N s} {w0 : Ideal (𝓞 D.F)} {r : ℕ}

theorem cancel_pt {X : Over (Sp k)} {f g : 𝟙_ (Over (Sp k)) ⟶ X}
    (h : toUnit (Over.mk (𝟙 (Sp k))) ≫ f = toUnit (Over.mk (𝟙 (Sp k))) ≫ g) : f = g := by
  have hi : (Over.mkIdTerminal (X := Sp k)).from (𝟙_ (Over (Sp k))) ≫ toUnit (Over.mk (𝟙 (Sp k))) = 𝟙 _ :=
    toUnit_unique _ _
  calc f = ((Over.mkIdTerminal (X := Sp k)).from (𝟙_ (Over (Sp k))) ≫ toUnit (Over.mk (𝟙 (Sp k)))) ≫ f := by
        rw [hi, Category.id_comp]
    _ = g := by rw [Category.assoc, h, ← Category.assoc, hi, Category.id_comp]

section lev
variable {lv : D.La → (𝟙_ (Over (Sp k)) ⟶ o.A)}

theorem pt_add (h : IsEtLev o w0 r lv) (x y : D.La) :
    toUnit (Over.mk (𝟙 (Sp k))) ≫ lv (x + y) =
      (toUnit (Over.mk (𝟙 (Sp k))) ≫ lv x) * (toUnit (Over.mk (𝟙 (Sp k))) ≫ lv y) := by
  rw [h.1, MonObj.comp_mul]

theorem pt_mem (h : IsEtLev o w0 r lv) {x : D.La} (hx : x ∈ wSub D w0 r) :
    toUnit (Over.mk (𝟙 (Sp k))) ≫ lv x = 1 := by
  rw [h.2.2.1 x hx, MonObj.comp_one]

theorem pt_smul (h : IsEtLev o w0 r lv) (a : D.O) (x : D.La) :
    toUnit (Over.mk (𝟙 (Sp k))) ≫ lv (a • x) = (toUnit (Over.mk (𝟙 (Sp k))) ≫ lv x) ≫ o.act.act a := by
  rw [h.2.1, Category.assoc]

theorem pt_inj (h : IsEtLev o w0 r lv) {x y : D.La}
    (hxy : toUnit (Over.mk (𝟙 (Sp k))) ≫ lv x = toUnit (Over.mk (𝟙 (Sp k))) ≫ lv y) : x - y ∈ wSub D w0 r := by
  apply (h.2.2.2 k (𝟙 (Sp k))).1
  have h0 : toUnit (Over.mk (𝟙 (Sp k))) ≫ lv 0 = 1 := pt_mem h (Submodule.zero_mem _)
  calc toUnit (Over.mk (𝟙 (Sp k))) ≫ lv (x - y)
      = (toUnit (Over.mk (𝟙 (Sp k))) ≫ lv (x - y)) * (toUnit (Over.mk (𝟙 (Sp k))) ≫ lv (y + -y)) := by
        rw [add_neg_cancel, h0, _root_.mul_one]
    _ = (toUnit (Over.mk (𝟙 (Sp k))) ≫ lv (x - y + y)) * (toUnit (Over.mk (𝟙 (Sp k))) ≫ lv (-y)) := by
        rw [pt_add h, pt_add h, _root_.mul_assoc]
    _ = (toUnit (Over.mk (𝟙 (Sp k))) ≫ lv (y + -y)) := by
        rw [sub_add_cancel, hxy, pt_add h]
    _ = 1 := by rw [add_neg_cancel, h0]

theorem pt_killed (h : IsEtLev o w0 r lv) (y : D.La) :
    ∀ c ∈ w0 ^ r, (toUnit (Over.mk (𝟙 (Sp k))) ≫ lv y) ≫ o.act.act (algebraMap (𝓞 D.F) D.O c) = 1 := by
  intro c hc
  rw [← pt_smul h]
  exact pt_mem h (Submodule.subset_span ⟨c, hc, y, rfl⟩)

end lev

theorem exists_levGrp {l₁ l₂ : D.La → (𝟙_ (Over (Sp k)) ⟶ o.A)} (h₁ : IsEtLev o w0 r l₁)
    (h₂ : IsEtLev o w0 r l₂) : ∃ g : LevGrp D w0 r, ∀ y, l₁ y = l₂ (liftAct g y) := by
  have hz : ∀ y, ∃ z, toUnit (Over.mk (𝟙 (Sp k))) ≫ l₂ z = toUnit (Over.mk (𝟙 (Sp k))) ≫ l₁ y :=
    fun y => (h₂.2.2.2 k (𝟙 (Sp k))).2 _ (pt_killed h₁ y)
  choose z hz using hz
  let ψ : D.La →ₗ[D.O] D.La ⧸ wSub D w0 r :=
    { toFun := fun y => Submodule.Quotient.mk (z y)
      map_add' := fun x y => by
        rw [← Submodule.Quotient.mk_add, Submodule.Quotient.eq]
        apply pt_inj h₂
        rw [hz, pt_add h₁, pt_add h₂, hz, hz]
      map_smul' := fun a y => by
        rw [RingHom.id_apply, ← Submodule.Quotient.mk_smul, Submodule.Quotient.eq]
        apply pt_inj h₂
        rw [hz, pt_smul h₁, pt_smul h₂, hz] }
  have hker : wSub D w0 r ≤ LinearMap.ker ψ := fun y hy => by
    rw [LinearMap.mem_ker]
    show Submodule.Quotient.mk (z y) = 0
    rw [Submodule.Quotient.mk_eq_zero]
    have := pt_inj h₂ (x := z y) (y := 0) (by rw [hz, pt_mem h₁ hy, pt_mem h₂ (Submodule.zero_mem _)])
    simpa using this
  let F := (wSub D w0 r).liftQ ψ hker
  have hF : ∀ y, F (Submodule.Quotient.mk y) = Submodule.Quotient.mk (z y) := fun y => rfl
  have inj : Function.Injective F := by
    rw [injective_iff_map_eq_zero]
    intro q hq
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    rw [hF, Submodule.Quotient.mk_eq_zero] at hq
    rw [Submodule.Quotient.mk_eq_zero]
    apply (h₁.2.2.2 k (𝟙 (Sp k))).1
    rw [← hz, pt_mem h₂ hq]
  have surj : Function.Surjective F := by
    intro q
    obtain ⟨w, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    obtain ⟨y, hy⟩ := (h₁.2.2.2 k (𝟙 (Sp k))).2 _ (pt_killed h₂ w)
    refine ⟨Submodule.Quotient.mk y, ?_⟩
    rw [hF, Submodule.Quotient.eq]
    apply pt_inj h₂
    rw [hz, hy]
  refine ⟨LinearEquiv.ofBijective F ⟨inj, surj⟩, fun y => ?_⟩
  rw [h₂.congr_mk (x := liftAct _ y) (y := z y) (by rw [mk_liftAct]; rfl)]
  exact cancel_pt (hz y).symm

end GlobalTheory.UPel.HT.EtLev.Cmp
