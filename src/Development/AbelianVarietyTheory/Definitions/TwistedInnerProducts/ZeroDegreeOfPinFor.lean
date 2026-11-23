module

public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.HeckePin
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.RationalHeckeScalars
public import Formalism.LocalToGlobal.IndefiniteReal.ConcretePkgSpec
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFamilyIffRationalHecke
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
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
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
import Mathlib.Topology.Sheaves.Init
import Formalism.LocalToGlobal.IndefiniteReal.ExistsChosenExtremalVector

@[expose] public section

set_option autoImplicit false

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH NumberField IsDedekindDomain Formalism.L2 Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Cx Formalism.IndefR.FWT Formalism.IndefR.NX Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ExportPin.Model

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type}
  {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
  (Rl : RealDat3 D A3 Ks) (cG : Formalism.L2.DIV.G0 Rl.Pg D.R.r ≃* G0g D.nd) (S : RatDat D.ntw) (Y : NExpRealS Rl cG S)



def PinFor (hk : ∀ i j b, ℕ → PlE D.host → Module.End (FractionRing (D.ntw.O i)) (D.nexp.Fm i j b)) : Prop :=
  ∀ (hL : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j)) (hs : ∀ j, 1 ≤ j → j ≤ D.R.m → HeckeStabR S j (hL j)),
    Reads Rl cG S Y hL → ∃ u : ∀ i : D.ntw.Tw, Bool → PlE D.host → (D.ntw.O i)ˣ,
      ∀ i j b (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) (k : ℕ) (P : PlE D.host) (x : D.nexp.Fm i j b), P ∉ D.ntw.S0 i →
        Formalism.BasicNotions.IsSplitPl D.host P → k ≤ D.R.r →
        Y.eF i j b h1 h2 (hk i j b k P x) =
          (algebraMap (D.ntw.O i) (FractionRing (D.ntw.O i)) (u i b P)) ^ k •
            hkFR S i j b (hL j) (hs j h1 h2) k P (Y.eF i j b h1 h2 x)

def Covered : Prop :=
  ∀ (i : D.ntw.Tw) (P : PlE D.host), P ∉ D.ntw.S0 i → Formalism.BasicNotions.IsSplitPl D.host P →
    Formalism.IndefR.Bridge.SplitOff P (Rl.Sb : Set (Formalism.L2.DIV.Pl D.host.E))

theorem covered_of_allPlaces (hL : Rl.toRealDat.toLevCh.Is A3.A.μ0) (hA : Rl.AllPlaces) : Covered Rl := by
  intro i P hP hs
  have hA' : Rl.Sb = Rl.Pg := hA
  have key : ∀ Q ∈ Rl.Sb, ∃ k, ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ Q.asIdeal := by
    intro Q hQ
    rw [hA'] at hQ
    obtain ⟨k, hk⟩ := (hL.Pg Q).1 hQ
    have h1 := Rl.C.P.pb_over k
    have h2 : Q.under (𝓞 D.host.K) = Rl.C.P.pb k := hk
    rw [← h2] at h1
    have h3 : algebraMap (𝓞 D.host.K) (𝓞 D.host.E) ((D.host.g k : ℕ) : 𝓞 D.host.K) ∈ Q.asIdeal := h1
    exact ⟨k, by rwa [map_natCast] at h3⟩
  refine ⟨(GlobalTheory.HeckeTieCompare.isSplitPl_iff P).1 hs, fun h => ?_, fun Q hQ h => ?_⟩
  · obtain ⟨k, hk⟩ := key P h
    exact hP (D.ntw.placesOver_subset_exceptional i k hk)
  · obtain ⟨k, hk⟩ := key Q hQ
    rw [h, Formalism.L2.Col.conjIdeal_asIdeal, Formalism.L2.Col.mem_conjP, map_natCast] at hk
    exact hP (D.ntw.placesOver_subset_exceptional i k hk)

theorem j_injective (hU : Rl.toRealDat.LUnif) (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ) :
    Function.Injective ((Rl.FW i).j σ) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  by_contra h0
  have := (hU i σ).1 1 (fun _ => x) (by rw [linearIndependent_unique_iff]; exact h0)
  rw [linearIndependent_unique_iff] at this
  exact this hx






theorem hkFR_of_smul (i : D.ntw.Tw) (j : ℕ) (b : Bool) {f : ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j)}
    (hs : HeckeStabR S j f) (k : ℕ) (P : PlE D.host) :
    (f k P = 0 → hkFR S i j b f hs k P = 0) ∧ (f k P = 1 → hkFR S i j b f hs k P = 1) := by
  constructor
  · intro h
    unfold hkFR
    have : ((f k P).restrictScalars S.Ks).restrict (p := (S.A j).WK) (q := (S.A j).WK) (fun x hx => hs k P x hx) = 0 := by
      ext x
      exact congrArg (fun t : Module.End D.what₂.LL (S.WL j) => t x) h
    rw [this]
    exact map_zero (Module.End.baseChangeHom S.Ks (KB S i b) (FmK S j))
  · intro h
    unfold hkFR
    have : ((f k P).restrictScalars S.Ks).restrict (p := (S.A j).WK) (q := (S.A j).WK) (fun x hx => hs k P x hx) = 1 := by
      ext x
      exact congrArg (fun t : Module.End D.what₂.LL (S.WL j) => t x) h
    rw [this]
    exact map_one (Module.End.baseChangeHom S.Ks (KB S i b) (FmK S j))


theorem exists_reads
    (h : ∀ (i : Fin D.R.m) (P : PlE D.host), Formalism.IndefR.Bridge.SplitOff P (Rl.Sb : Set (Formalism.L2.DIV.Pl D.host.E)) →
      ∀ k : ℕ, k ≤ D.R.r → GlobalTheory.IndefiniteRowSideFullHecke.RationalHeckeScalars.RationalHeckeAt Rl.toRealDat i P k) :
    ∃ (f : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j))
      (_ : ∀ j, 1 ≤ j → j ≤ D.R.m → HeckeStabR S j (f j)), Reads Rl cG S Y f := by
  have h' : ∀ (i : Fin D.R.m) (k : ℕ) (P : PlE D.host), ∃ t : Module.End D.what₂.LL (Fin (Rl.nW i) → D.what₂.LL),
      (∀ x ∈ (Rl.FW i).WK, t x ∈ (Rl.FW i).WK) ∧
      (Formalism.IndefR.Bridge.SplitOff P (Rl.Sb : Set (Formalism.L2.DIV.Pl D.host.E)) → k ≤ D.R.r →
        ∀ Rc, GlobalTheory.IndefiniteRowSideFullHecke.RationalHeckeScalars.IsCosetSys Rl.toRealDat i P k Rc → GlobalTheory.IndefiniteRowSideFullHecke.RationalHeckeScalars.ReadAs Rl.toRealDat i P k Rc t) := by
    intro i k P
    by_cases hc : Formalism.IndefR.Bridge.SplitOff P (Rl.Sb : Set (Formalism.L2.DIV.Pl D.host.E)) ∧ k ≤ D.R.r
    · obtain ⟨t, t1, t2⟩ := h i P hc.1 k hc.2
      exact ⟨t, t2, fun _ _ => t1⟩
    · exact ⟨1, fun x hx => hx, fun h1 h2 => absurd ⟨h1, h2⟩ hc⟩
  choose t t1 t2 using h'
  let f : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j) := fun j =>
    match j with
    | 0 => fun _ _ => 0
    | n + 1 => fun k P =>
        if hn : n < D.R.m then ((Y.fi ⟨n, hn⟩).e).symm.conj (t ⟨n, hn⟩ k P) else 0
  have hf (i : Fin D.R.m) (k : ℕ) (P : PlE D.host) :
      (Y.fi i).e.conj (f ((i : ℕ) + 1) k P) = t i k P := by
    simp only [f, dite_eq_left i.2]
    exact (Y.fi i).e.conj.apply_symm_apply (t i k P)
  have e : ∀ (i : Fin D.R.m) k P x, (Y.fi i).e (f ((i : ℕ) + 1) k P x) = t i k P ((Y.fi i).e x) := fun i k P x => by
    rw [← hf i k P, LinearEquiv.conj_apply_apply, LinearEquiv.symm_apply_apply]
  refine ⟨f, fun j h1 h2 k P x hx => ?_, fun i k P _ ho hk α R ha hR x => ?_⟩
  · obtain ⟨n, rfl⟩ : ∃ n, j = n + 1 := ⟨j - 1, by omega⟩
    let i : Fin D.R.m := ⟨n, h2⟩
    refine ((Y.fi i).wk _).2 ?_
    rw [e i]
    exact t1 i k P _ (((Y.fi i).wk _).1 hx)
  · have hscalar :
        (((Rl.C.mu0 i).val P : ℂˣ) : ℂ)⁻¹ ^ k *
            (((Nat.card (kP P) : ℕ) : ℂ) ^ (k * (D.R.nV / 2)))⁻¹ =
          GlobalTheory.IndefiniteRowSideFullHecke.RationalHeckeScalars.heckeScalar Rl.toRealDat i P k := by
      rw [GlobalTheory.IndefiniteRowSideFullHecke.RationalHeckeScalars.heckeScalar,
        zpow_neg, zpow_neg, zpow_natCast, zpow_natCast, inv_pow]
    rw [e, hscalar]
    exact t2 i k P ho hk R ⟨α, ha, hR⟩ _


end GlobalTheory.ExportPin.Model
