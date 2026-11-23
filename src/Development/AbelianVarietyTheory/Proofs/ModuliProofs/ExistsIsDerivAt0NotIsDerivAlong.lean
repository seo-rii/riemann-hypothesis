module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
public import Development.AbelianVarietyTheory.BlockTheory.CMModuli.PeriodMapPresentation
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.ExistsEquivOfSumEq
import Mathlib.Algebra.AffineMonoid.Basic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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
import Mathlib.RingTheory.Coalgebra.CoassocSimps
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

noncomputable section

namespace GlobalTheory.PeriodCompare

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding IsTypeFn IsThetaFrame
open GlobalTheory.IndefiniteRowSideFullHecke.PeriodMapPresentation hiding IsTypeFn IsThetaFrame
open scoped TensorProduct Topology

section Period

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem isTypeFn_iff (D : Datum H) {g : ℕ} (ty : Fin g → (E →+* ℂ)) :
    Tor.IsTypeFn H D.p D.q ty ↔ IndefiniteRowSideFullHecke.PeriodMapPresentation.IsTypeFn D ty := by
  refine forall_congr' fun τ => ?_
  unfold sigMult
  by_cases h : τ (H.rt : E) = H.rt0 <;> simp [h]

theorem isTypeFn_of_sum (D : Datum H) {g : ℕ} (ty : Fin g → (E →+* ℂ))
    (h : ∀ a : 𝓞 E, ∑ i, ty i (a : E) = sigTrace D a) : IndefiniteRowSideFullHecke.PeriodMapPresentation.IsTypeFn D ty := by
  classical
  let κ := Σ τ : E →+* ℂ, Fin (sigMult D τ)
  let ε := Fintype.equivFin κ
  have h0 : IndefiniteRowSideFullHecke.PeriodMapPresentation.IsTypeFn D (fun k => (ε.symm k).1) := fun τ => by
    rw [Nat.card_congr (ε.symm.subtypeEquiv (q := fun x : κ => x.1 = τ) fun _ => Iff.rfl),
      Nat.card_congr (Equiv.sigmaSubtype τ)]
    simp
  obtain ⟨e, he⟩ := PeriodNonempty.exists_equiv_of_sum_eq ty (fun k => (ε.symm k).1) fun a => by
    rw [h, PeriodNonempty.sum_type H ((isTypeFn_iff D _).2 h0)]
    rfl
  intro τ
  rw [← h0 τ]
  exact Nat.card_congr (e.subtypeEquiv fun i => by rw [← he i])

theorem finiteDimensional (D : Datum H) : Module.Finite ℤ D.La ∧ Module.Free ℤ D.La := by
  haveI := D.fin
  haveI := D.proj
  haveI : Module.Finite ℤ D.La := Module.Finite.trans (𝓞 E) D.La
  haveI : Module.Flat ℤ D.La := Module.Flat.trans ℤ (𝓞 E) D.La
  exact ⟨inferInstance, inferInstance⟩

theorem trace_eq_of_pos {W : Type} [AddCommGroup W] [Module ℝ W] [FiniteDimensional ℝ W]
    (B : LinearMap.BilinForm ℝ W) (J J' A : W →ₗ[ℝ] W) (hJ : ∀ x, J (J x) = -x) (hJ' : ∀ x, J' (J' x) = -x)
    (hp : ∀ x, x ≠ 0 → 0 < B (J x) x) (hp' : ∀ x, x ≠ 0 → 0 < B (J' x) x)
    (hA : J ∘ₗ A = A ∘ₗ J) (hA' : J' ∘ₗ A = A ∘ₗ J') :
    LinearMap.trace ℝ W (J ∘ₗ A) = LinearMap.trace ℝ W (J' ∘ₗ A) := by
  have hinj : Function.Injective (J + J') := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    by_contra h0
    have h1 := hp x h0
    have h2 := hp' x h0
    have h3 : B ((J + J') x) x = 0 := by rw [hx]; simp
    simp only [LinearMap.add_apply, map_add (f := _)] at h3
    linarith
  let T := LinearEquiv.ofInjectiveEndo _ hinj
  have hT : ∀ x, T x = J x + J' x := fun _ => rfl
  have hA1 : ∀ x, J (A x) = A (J x) := fun x => LinearMap.congr_fun hA x
  have hA2 : ∀ x, J' (A x) = A (J' x) := fun x => LinearMap.congr_fun hA' x
  rw [← LinearMap.trace_conj' (J ∘ₗ A) T]
  congr 1
  refine LinearMap.ext fun y => ?_
  obtain ⟨x, rfl⟩ := T.surjective y
  rw [LinearEquiv.conj_apply_apply, T.symm_apply_apply, hT, hT]
  simp only [LinearMap.comp_apply, map_add (f := _), ← hA1, ← hA2, hJ, hJ']
  abel

theorem mem_domain (D : Datum H) {J : ℝ ⊗[ℤ] D.La →ₗ[ℝ] ℝ ⊗[ℤ] D.La} (h1 : ∀ x, J (J x) = -x)
    (h2 : ∀ a : 𝓞 E, J ∘ₗ actR D a = actR D a ∘ₗ J)
    (h3 : ∀ x y, D.EF.baseChange ℝ (J x) (J y) = D.EF.baseChange ℝ x y)
    (h4 : ∀ x, x ≠ 0 → 0 < D.EF.baseChange ℝ (J x) x) : J ∈ domain D := by
  obtain ⟨_, _⟩ := finiteDimensional D
  obtain ⟨J', k1, k2, -, k4, k5⟩ := domain_nonempty D
  refine ⟨h1, h2, h3, h4, fun a => ?_⟩
  rw [trace_eq_of_pos _ J J' _ h1 k1 h4 k4 (h2 a) (k2 a), k5]

theorem trace_of_presents {D : Datum H} {g : ℕ} {ty : Fin g → (E →+* ℂ)} {P : D.La →+ (Fin g → ℂ)}
    {J : ℝ ⊗[ℤ] D.La →ₗ[ℝ] ℝ ⊗[ℤ] D.La} (h : Presents D ty P J) (a : 𝓞 E) :
    ((LinearMap.trace ℝ _ (actR D a) : ℝ) : ℂ) / 2 -
      Complex.I * ((LinearMap.trace ℝ _ (J ∘ₗ actR D a) : ℝ) : ℂ) / 2 = ∑ i, ty i (a : E) := by
  obtain ⟨_, _⟩ := finiteDimensional D
  obtain ⟨φ, -, h2, h3⟩ := h
  let f : Module.End ℂ (Fin g → ℂ) := Matrix.toLin' (Matrix.diagonal fun i => ty i (a : E))
  have hf : ∀ z, f z = tyAct ty a z := fun z => by
    funext i; simp [f, tyAct, Matrix.mulVec_diagonal]
  have ht : LinearMap.trace ℂ _ f = ∑ i, ty i (a : E) := by simp [f]
  have e1 : φ.conj (actR D a) = f.restrictScalars ℝ := by
    refine LinearMap.ext fun y => ?_
    rw [LinearEquiv.conj_apply_apply, h3, φ.apply_symm_apply]
    exact (hf y).symm
  have e2 : φ.conj (J ∘ₗ actR D a) = (Complex.I • f).restrictScalars ℝ := by
    refine LinearMap.ext fun y => ?_
    rw [LinearEquiv.conj_apply_apply, LinearMap.comp_apply, h2, h3, φ.apply_symm_apply, ← hf]
    rfl
  rw [← LinearMap.trace_conj' _ φ, ← LinearMap.trace_conj' (J ∘ₗ actR D a) φ, e1, e2, PeriodNonempty.trace_real,
    PeriodNonempty.trace_real, map_smul, ht]
  generalize ∑ i, ty i (a : E) = t
  apply Complex.ext
  · simp
  · simp; ring

def imForm {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) : LinearMap.BilinForm ℝ (Fin g → ℂ) :=
  LinearMap.mk₂ ℝ (fun z w => (hermForm Hm z w).im)
    (fun a b c => by simp [hermForm, add_dotProduct])
    (fun r a b => by simp [hermForm, smul_dotProduct])
    (fun a b c => by simp [hermForm, Matrix.mulVec_add, dotProduct_add])
    (fun r a b => by
      simp only [hermForm, star_smul, star_trivial, Matrix.mulVec_smul, dotProduct_smul]
      simp)

theorem exists_presents {D : Datum H} {g : ℕ} {ty : Fin g → (E →+* ℂ)} {P : D.La →+ (Fin g → ℂ)}
    (h : IsPeriod D ty P) : ∃ J ∈ domain D, Presents D ty P J := by
  obtain ⟨_, _⟩ := finiteDimensional D
  obtain ⟨hlin, hinj, hdisc, hspan, Hm, -, hpos, hE⟩ := h
  let ψ : ℝ ⊗[ℤ] D.La →ₗ[ℝ] (Fin g → ℂ) := P.toIntLinearMap.liftBaseChange ℝ
  have hψ : ∀ (r : ℝ) x, ψ (r ⊗ₜ x) = r • P x := fun r x => by simp [ψ]
  have hsurj : Function.Surjective ψ := by
    rw [← LinearMap.range_eq_top, eq_top_iff, ← hspan, Submodule.span_le]
    rintro _ ⟨x, rfl⟩
    exact ⟨1 ⊗ₜ x, by simp [hψ]⟩
  have hrk : Module.finrank ℝ (ℝ ⊗[ℤ] D.La) = Module.finrank ℝ (Fin g → ℂ) := by
    haveI : DiscreteTopology (LinearMap.range P.toIntLinearMap) := hdisc
    haveI : IsZLattice ℝ (LinearMap.range P.toIntLinearMap) := ⟨hspan⟩
    rw [Module.finrank_baseChange, (LinearEquiv.ofInjective P.toIntLinearMap hinj).finrank_eq, ZLattice.rank ℝ]
  let φ := LinearEquiv.ofBijective ψ ⟨(LinearMap.injective_iff_surjective_of_finrank_eq_finrank hrk).2 hsurj, hsurj⟩
  have hφ : ∀ (r : ℝ) x, φ (r ⊗ₜ x) = r • P x := hψ
  let J : ℝ ⊗[ℤ] D.La →ₗ[ℝ] ℝ ⊗[ℤ] D.La :=
    φ.symm.conj ((Complex.I • (LinearMap.id : Module.End ℂ (Fin g → ℂ))).restrictScalars ℝ)
  have hJ : ∀ v, φ (J v) = Complex.I • φ v := fun v => by simp [J, LinearEquiv.conj_apply_apply]
  have hact : ∀ (a : 𝓞 E) v, φ (actR D a v) = tyAct ty a (φ v) := fun a v => by
    induction v using TensorProduct.induction_on with
    | zero => funext i; simp [tyAct]
    | add u v hu hv => funext i; simp [tyAct, hu, hv, mul_add]
    | tmul r x =>
      funext i
      have : actR D a (r ⊗ₜ x) = r ⊗ₜ (a • x) := rfl
      simp [this, hφ, tyAct, hlin, mul_left_comm]
  have hB : ∀ x y, D.EF.baseChange ℝ x y = imForm Hm (φ x) (φ y) := fun x y => by
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add x x' h h' => simp only [map_add (f := _), LinearMap.add_apply, h, h']
    | tmul r x =>
      induction y using TensorProduct.induction_on with
      | zero => simp
      | add y y' h h' => simp only [map_add (f := _), h, h']
      | tmul r' y =>
        have : imForm Hm (P x) (P y) = D.EF x y := hE x y
        simp only [hφ, map_smul, LinearMap.smul_apply, this, LinearMap.BilinForm.baseChange_tmul, smul_eq_mul,
          zsmul_eq_mul]
        ring
  refine ⟨J, mem_domain D (fun x => φ.injective ?_) (fun a => LinearMap.ext fun v => φ.injective ?_)
    (fun x y => ?_) (fun x hx => ?_), φ, fun x => by simp [hφ], hJ, hact⟩
  · rw [hJ, hJ, smul_smul, Complex.I_mul_I, map_neg, neg_smul, one_smul]
  · simp only [LinearMap.comp_apply, hJ, hact]
    funext i; simp [tyAct, mul_left_comm]
  · rw [hB, hB, hJ, hJ]
    change (hermForm _ _ _).im = (hermForm _ _ _).im
    simp [hermForm, star_smul, Matrix.mulVec_smul, Matrix.mulVec_neg, ← mul_assoc]
  · rw [hB, hJ]
    have := hpos (φ x) (by simpa using hx)
    change 0 < (hermForm _ _ _).im
    simpa [hermForm, smul_dotProduct] using this

theorem isPeriod_of_presents {D : Datum H} {g : ℕ} {ty : Fin g → (E →+* ℂ)} {P : D.La →+ (Fin g → ℂ)}
    {J : ℝ ⊗[ℤ] D.La →ₗ[ℝ] ℝ ⊗[ℤ] D.La} (hJ : J ∈ domain D) (h : Presents D ty P J) : IsPeriod D ty P := by
  classical
  obtain ⟨_, _⟩ := finiteDimensional D
  obtain ⟨-, -, hinv, hpos, -⟩ := hJ
  obtain ⟨e, hP, heJ, heρ⟩ := h
  let b := Module.Free.chooseBasis ℤ D.La
  let c := (b.baseChange ℝ).map e
  have hc : ∀ i, c i = P (b i) := fun i => by simp [c, hP]
  have hrange : P.range = (Submodule.span ℤ (Set.range c)).toAddSubgroup := by
    have h1 : Set.range c = P.toIntLinearMap '' Set.range b := by
      rw [← Set.range_comp]; congr 1; funext i; exact hc i
    rw [h1, ← Submodule.map_span, b.span_eq]
    ext z; simp
  refine ⟨fun a x i => ?_, ?_, ?_, ?_, ?_⟩
  · rw [← hP, ← hP]
    exact congrFun (heρ a (1 ⊗ₜ x)) i
  · rw [injective_iff_map_eq_zero]
    intro x hx
    rw [← hP, e.map_eq_zero_iff] at hx
    apply b.ext_elem
    intro i
    have := congrArg (fun v => (b.baseChange ℝ).repr v i) hx
    simpa using this
  · rw [hrange]; infer_instance
  · rw [eq_top_iff, ← c.span_eq]
    apply Submodule.span_mono
    rintro _ ⟨i, rfl⟩
    exact ⟨b i, (hc i).symm⟩
  · have halt0 : ∀ x y, D.EF x y = -D.EF y x := fun x y => by
      have := D.alt (x + y)
      simp only [map_add (f := _), LinearMap.add_apply, D.alt] at this
      linarith
    have halt : ∀ x y, D.EF.baseChange ℝ x y = -D.EF.baseChange ℝ y x := fun x y => by
      induction x using TensorProduct.induction_on with
      | zero => simp
      | add x x' h h' => simp only [map_add (f := _), LinearMap.add_apply, h, h']; ring
      | tmul r x =>
        induction y using TensorProduct.induction_on with
        | zero => simp
        | add y y' h h' => simp only [map_add (f := _), LinearMap.add_apply, h, h']; ring
        | tmul r' y => simp [halt0 x y, mul_comm]
    have hs : ∀ z, e.symm (Complex.I • z) = J (e.symm z) := fun z => by
      rw [e.symm_apply_eq, heJ, e.apply_symm_apply]
    obtain ⟨Hm, h1, h2, h3⟩ := PeriodNonempty.exists_herm
      ((D.EF.baseChange ℝ).comp e.symm.toLinearMap e.symm.toLinearMap)
      (fun x y => halt _ _) (fun x y => by simp [hs, hinv])
      (fun x hx => by simpa [hs] using hpos (e.symm x) (by simpa using hx))
    refine ⟨Hm, h1, h2, fun x y => ?_⟩
    rw [h3]
    simp [← hP]

theorem isTypeFn_of_isPeriod {D : Datum H} {g : ℕ} {ty : Fin g → (E →+* ℂ)} {P : D.La →+ (Fin g → ℂ)}
    (h : IsPeriod D ty P) : Tor.IsTypeFn H D.p D.q ty := by
  obtain ⟨J, hJ, hP⟩ := exists_presents h
  exact (isTypeFn_iff D ty).2 (isTypeFn_of_sum D ty fun a => (trace_of_presents hP a).symm.trans (hJ.2.2.2.2 a))

end Period

section Hol

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] {X : Scheme.{0}}


end Hol

section Theta

variable {S : Scheme.{0}} {G : Over S} [GrpObj G] {g m : ℕ}

end Theta

section Family

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H} {Xo : Moduli D l}
  {σ : KA l →+* ℂ} {g : ℕ} {ty : Fin g → (E →+* ℂ)} (Fu : FamilyUnif Xo σ ty) (i : Fin Fu.n)

end Family

end GlobalTheory.PeriodCompare
