module

public import Formalism.LocalToGlobal.Divisibility.RowSideTie
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SpanRangeMulVec
public import Formalism.LocalToGlobal.IndefiniteReal.ConcretePkgSpec
public import Formalism.LocalToGlobal.IndefiniteReal.CxLemmas
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH NumberField IsDedekindDomain Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.DivisionValues
open Formalism.IndefR.Cx
open scoped InnerProductSpace Matrix

namespace GlobalTheory.Mem.LiftTheta

section Core

variable {K : Type} [Field K] [NumberField K] {σ : K →+* ℂ} {N H : Type} [AddCommGroup N] [Module ℂ N] [AddCommGroup H] [Module ℂ H]

omit [NumberField K] in
theorem semi_expand {d : ℕ} (w : (Fin d → K) →ₛₗ[σ] H) (y : Fin d → K) : w y = ∑ k, σ (y k) • w (Pi.single k 1) := by
  have hz : y = ∑ k, y k • (Pi.single k 1 : Fin d → K) := by
    ext i; simp [Pi.single_apply]
  conv_lhs => rw [hz]

  simp only [map_sum, map_smulₛₗ]

omit [NumberField K] in
theorem semi_injective {d : ℕ} (w : (Fin d → K) →ₛₗ[σ] H) (hli : LinearIndependent ℂ fun k => w (Pi.single k 1)) :
    Function.Injective w := by
  rw [injective_iff_map_eq_zero]
  intro y hy
  rw [semi_expand] at hy
  funext k
  exact (map_eq_zero σ).1 (Fintype.linearIndependent_iff.1 hli _ hy k)


theorem oLatTie_of_closure {O : Type} [CommRing O] {φ : O →+* ℂ} (hφ : ∀ a, ∃ b : 𝓞 K, φ a = σ (b : K))
    (M : Rows.OLat O φ N) {d : ℕ} (e : N →ₗ[ℂ] H) (he : Function.Injective e) (j : (Fin d → K) →ₛₗ[σ] N)
    (hj : Function.Injective j) (L : Submodule (𝓞 K) (Fin d → K)) (S : Set H) (hS : ∀ y, y ∈ S ↔ ∃ x ∈ L, e (j x) = y)
    (h : AddSubgroup.closure {y | ∃ a : 𝓞 K, ∃ x ∈ e '' M.carrier, y = σ (a : K) • x} =
      AddSubgroup.closure {y | ∃ a : 𝓞 K, ∃ x ∈ S, y = σ (a : K) • x}) :
    OLatTie σ M j L := by
  classical
  have hR : ∀ y, y ∈ AddSubgroup.closure {y | ∃ a : 𝓞 K, ∃ x ∈ S, y = σ (a : K) • x} ↔ ∃ x ∈ L, e (j x) = y := by
    intro y
    refine ⟨fun hy => ?_, fun hy => AddSubgroup.subset_closure ⟨1, y, (hS y).2 hy, by simp⟩⟩
    induction hy using AddSubgroup.closure_induction with
    | mem y hy =>
      obtain ⟨a, u, hu, rfl⟩ := hy
      obtain ⟨x, hx, rfl⟩ := (hS u).1 hu
      refine ⟨a • x, L.smul_mem a hx, ?_⟩
      rw [← algebraMap_smul K a x, map_smulₛₗ, map_smul]
    | zero => exact ⟨0, L.zero_mem, by simp⟩
    | add _ _ _ _ h1 h2 =>
      obtain ⟨x, hx, rfl⟩ := h1
      obtain ⟨x', hx', rfl⟩ := h2
      exact ⟨x + x', L.add_mem hx hx', by simp⟩
    | neg _ _ h1 =>
      obtain ⟨x, hx, rfl⟩ := h1
      exact ⟨-x, L.neg_mem hx, by simp⟩
  have hgen : ∀ v ∈ M.gen, v ∈ M.carrier := by
    intro v hv
    refine ⟨fun u => if u = v then 1 else 0, ?_⟩
    rw [Finset.sum_eq_single v]
    · simp
    · intro u _ hu
      simp [hu]
    · intro h; exact absurd hv h
  have hL : ∀ y, y ∈ AddSubgroup.closure {y | ∃ a : 𝓞 K, ∃ x ∈ e '' M.carrier, y = σ (a : K) • x} ↔
      ∃ c : N → 𝓞 K, y = e (∑ v ∈ M.gen, σ (c v : K) • v) := by
    intro y
    constructor
    · intro hy
      induction hy using AddSubgroup.closure_induction with
      | mem y hy =>
        obtain ⟨a, _, ⟨_, ⟨c, rfl⟩, rfl⟩, rfl⟩ := hy
        choose b hb using hφ
        refine ⟨fun v => a * b (c v), ?_⟩
        rw [← map_smul, Finset.smul_sum]
        simp [hb, mul_smul]
      | zero => exact ⟨0, by simp⟩
      | add _ _ _ _ h1 h2 =>
        obtain ⟨c, rfl⟩ := h1
        obtain ⟨c', rfl⟩ := h2
        refine ⟨c + c', ?_⟩
        rw [← map_add (f := _), ← Finset.sum_add_distrib]
        simp [add_smul]
      | neg _ _ h1 =>
        obtain ⟨c, rfl⟩ := h1
        refine ⟨-c, ?_⟩
        rw [← map_neg, ← Finset.sum_neg_distrib]
        simp
    · rintro ⟨c, rfl⟩

      rw [map_sum]
      refine AddSubgroup.sum_mem _ fun v hv => AddSubgroup.subset_closure ⟨c v, e v, ⟨v, hgen v hv, rfl⟩, map_smul _ _ _⟩
  refine ⟨fun v hv => ?_, fun x => ⟨fun hx => ?_, ?_⟩⟩
  · have h1 : e v ∈ AddSubgroup.closure {y | ∃ a : 𝓞 K, ∃ x ∈ e '' M.carrier, y = σ (a : K) • x} :=
      AddSubgroup.subset_closure ⟨1, e v, ⟨v, hgen v hv, rfl⟩, by simp⟩
    rw [h, hR] at h1
    obtain ⟨x, -, hx⟩ := h1
    exact ⟨x, he hx⟩
  · have h1 := (hR _).2 ⟨x, hx, rfl⟩
    rw [← h, hL] at h1
    obtain ⟨c, hc⟩ := h1
    exact ⟨c, he hc⟩
  · rintro ⟨c, hc⟩
    have h1 := (hL (e (j x))).2 ⟨c, congrArg e hc⟩
    rw [h, hR] at h1
    obtain ⟨x', hx', hxx⟩ := h1
    rwa [← hj (he hxx)]

omit [NumberField K] in
theorem lin_cpt {d : ℕ} (w : (Fin d → K) →ₛₗ[σ] H) (y : Fin d → K) :
    lin (fun k => w (Pi.single k 1)) (cpt σ y) = w y := (semi_expand w y).symm

end Core

section Lift

variable {K : Type} [Field K] [NumberField K] [StarRing K] {Bs : DefBase K} {A : DefAmb Bs} (X : CxData A)
  {fc : DefSub A → DefFace Bs} (cr : Crd A fc) (b : Bool)

theorem liftMatrix_computes_lift_rational (h5 : X.H5 cr b) (hr : X.RATth cr b) (j : Bs.J) (t : Bs.Tup) (z : Fin ((lv (fc X.zs) b).dZ j t) → K) :
    X.w0C b j (cpt Bs.v0.embedding (X.liftMat cr b j t *ᵥ z)) = X.θ' j t (X.jL j t (cr.toL X.zs b j t z)) :=
  (X.key_lift cr b h5 hr j t z).trans (lin_cpt (((X.θ' j t).comp (X.jL j t)).comp (cr.toL X.zs b j t)) z)

end Lift

section Main

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

variable (R : RealDat D A Ks) (F : Face D A)

def goodForm (b : Bool) (i : Fin D.R.m) :
    (Fin (Module.finrank D.what₂.LL (R.WL F b i)) → D.what₂.LL) →ₛₗ[D.what₂.embLL] (R.HW i (sg0 D A)).H where
  toFun y := (R.FW i).j (sg0 D A) (∑ k, y k • R.bL F b i k)
  map_add' x y := by simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib, map_add (f := _)]
  map_smul' a y := by
    have h : sg0 D A a = D.what₂.embLL a := by rw [sg0, sgAt_mk _ R.hv0]
    simp only [Pi.smul_apply, smul_eq_mul, mul_smul, ← Finset.smul_sum, map_smulₛₗ, h]

theorem goodForm_apply (b : Bool) (i : Fin D.R.m) (y : Fin (Module.finrank D.what₂.LL (R.WL F b i)) → D.what₂.LL) :
    goodForm R F b i y = (R.FW i).j (sg0 D A) (∑ k, y k • R.bL F b i k) := rfl

theorem goodForm_single (b : Bool) (i : Fin D.R.m) (k : Fin (Module.finrank D.what₂.LL (R.WL F b i))) :
    goodForm R F b i (Pi.single k 1) = (R.FW i).j (sg0 D A) (R.bL F b i k) := by
  rw [goodForm_apply]
  congr 1
  simp [Pi.single_apply]

theorem goodForm_li (hU : R.LUnif) (b : Bool) (i : Fin D.R.m) :
    LinearIndependent ℂ fun k => goodForm R F b i (Pi.single k 1) := by
  simp only [goodForm_single]
  exact (hU i _).1 _ _
    ((Module.finBasis D.what₂.LL (R.WL F b i)).linearIndependent.map' (R.WL F b i).subtype (Submodule.ker_subtype _))

theorem sqrt_ne (b : Bool) : ((Real.sqrt (RealDat.nP F b) : ℝ) : ℂ) ≠ 0 := by
  have := Real.sqrt_pos.2 (RealDat.nP_pos (F := F) b)
  exact_mod_cast this.ne'

theorem smul_bC (b : Bool) (i : Fin D.R.m) (k : Fin (Module.finrank D.what₂.LL (R.WL F b i))) :
    ((Real.sqrt (RealDat.nP F b) : ℝ) : ℂ) • R.bC F b i (sg0 D A) k = goodForm R F b i (Pi.single k 1) := by
  rw [goodForm_single, RealDat.bC, smul_smul, Complex.ofReal_inv, mul_inv_cancel₀ (sqrt_ne F b), one_smul]

theorem goodForm_span (b : Bool) (i : Fin D.R.m) :
    Submodule.span ℂ (Set.range fun k => goodForm R F b i (Pi.single k 1)) = R.WS F b i (sg0 D A) := by
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨k, rfl⟩
    rw [SetLike.mem_coe]
    beta_reduce
    rw [← smul_bC]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)
  · rw [RealDat.WS, Submodule.span_le]
    rintro _ ⟨k, rfl⟩
    rw [SetLike.mem_coe, ← Submodule.smul_mem_iff _ (sqrt_ne F b), smul_bC]
    exact Submodule.subset_span ⟨k, rfl⟩

theorem mem_image_iff (b : Bool) (i : Fin D.R.m) (y : (R.HW i (sg0 D A)).H) :
    y ∈ (R.FW i).j (sg0 D A) '' ((R.FW i).Mj (F.lvl b).P (F.lvl b).ψ⁻¹ (fun g => (idemOf A.X).coeff g) : Set _) ↔
      ∃ x ∈ (R.toCx F).M b i, goodForm R F b i x = y := by
  constructor
  · rintro ⟨f, hf, rfl⟩
    have hW : f ∈ R.WL F b i := (R.FW i).Mj_sub_Wgood _ _ _ hf
    have hs : ∑ k, (Module.finBasis D.what₂.LL (R.WL F b i)).repr ⟨f, hW⟩ k • R.bL F b i k = f := by
      have h := congrArg (R.WL F b i).subtype ((Module.finBasis D.what₂.LL (R.WL F b i)).sum_repr ⟨f, hW⟩)

      rw [map_sum] at h
      exact h
    refine ⟨fun k => (Module.finBasis D.what₂.LL (R.WL F b i)).repr ⟨f, hW⟩ k, ((R.FW i).mem_Mcoord _ _ _ _ _).2 ?_, ?_⟩
    · rw [hs]; exact hf
    · exact congrArg ((R.FW i).j (sg0 D A)) hs
  · rintro ⟨x, hx, rfl⟩
    exact ⟨_, ((R.FW i).mem_Mcoord _ _ _ _ _).1 hx, rfl⟩

theorem liftWeight_complexPoint_eq_twist (b : Bool) (i : Fin D.R.m) (y : Fin (Module.finrank D.what₂.LL (R.WL F b i)) → D.what₂.LL) :
    (R.toCx F).w0C b i (cpt A.v0.embedding y) = Tw.mk (twAt D.what₂.embLL A.v0) (goodForm R F b i y) := by
  have h1 : (R.toCx F).w0C b i = lin fun k => Tw.semi _ R.emb0 (goodForm R F b i) (Pi.single k 1) := by
    rw [← lin_basis ((R.toCx F).w0C b i)]
    congr 1
    funext k
    exact (congrArg ((R.toCx F).eW b i) (lin_single _ k)).trans (smul_bC R F b i k)
  rw [h1]
  exact lin_cpt (Tw.semi _ R.emb0 (goodForm R F b i)) y

theorem levelFormCoordinateMap_levelZero {s : ℕ} (hOk : A.fam.Ok s) (Zs : DefSub A.fam.amb) (i : Fin D.R.m) (t : T)
    (z : Fin ((A.fam.L i t).dZ (A.fam.lvlA F.P0 F.ψ0) (Zs.Zl i t)) → D.what₂.LL) :
    LiftForms.lvlForm (A.fam.L i t).S (A.fam.L i t).r (A.fam.lvlA F.P0 F.ψ0).P (A.fam.lvlA F.P0 F.ψ0).ψ
      (lZ0 D A F.P0 F.ψ0 Zs i t *ᵥ z) = F.cr.toL Zs false i t z :=
  LiftForms.lvlForm_lE (v0 := A.v0) (s := s) ⟨hOk.conj, hOk.irr, hOk.lifts i t⟩ z


end Main

end GlobalTheory.Mem.LiftTheta

end
