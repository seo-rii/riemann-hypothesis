module

public import GroundTheory.GlobalFields.ComplexMultiplication.IdeleAction
public import GroundTheory.GlobalFields.Adele.Approximation
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
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Global

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum WithZero FractionalIdeal
open scoped NumberField.AdeleRing nonZeroDivisors

noncomputable section

variable {K : Type*} [Field K] [NumberField K]

theorem exists_sub_mem_localIdeal {I : FractionalIdeal (𝓞 K)⁰ K} (hI : I ≠ 0)
    (a : FiniteAdeleRing (𝓞 K) K) :
    ∃ k : K, ∀ v : HeightOneSpectrum (𝓞 K), a v - (k : v.adicCompletion K) ∈ localIdeal I v := by
  obtain ⟨d, hdI, hd0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (coeToSubmodule_ne_bot.2 hI)
  obtain ⟨k', hk'⟩ := exists_sub_mem_integralFiniteAdeles
    (algebraMap K (FiniteAdeleRing (𝓞 K) K) d⁻¹ * a)
  refine ⟨d * k', fun v ↦ ?_⟩
  have ht : ((d⁻¹ : K) : v.adicCompletion K) * a v - (k' : v.adicCompletion K) ∈
      v.adicCompletionIntegers K :=
    (mem_integralFiniteAdeles.1 hk') v
  have h1 : (d : v.adicCompletion K) * ((d⁻¹ : K) : v.adicCompletion K) = 1 := by
    rw [← adicCompletion.coe_mul, mul_inv_cancel₀ hd0, adicCompletion.coe_one]
  have h : a v - ((d * k' : K) : v.adicCompletion K) =
      (⟨_, ht⟩ : v.adicCompletionIntegers K) • (d : v.adicCompletion K) := by
    change _ = (((d⁻¹ : K) : v.adicCompletion K) * a v - (k' : v.adicCompletion K)) *
      (d : v.adicCompletion K)
    rw [adicCompletion.coe_mul]
    linear_combination -(a v) * h1
  rw [h]
  exact Submodule.smul_mem _ _ (coe_mem_localIdeal v hdI)

def dfinsuppOfFinite {ι : Type*} {β : ι → Type*} [∀ i, Zero (β i)] (f : ∀ i, β i)
    (hf : {i | f i ≠ 0}.Finite) : Π₀ i, β i :=
  ⟨f, Trunc.mk ⟨hf.toFinset.val, fun i ↦ by
    by_cases h : f i = 0
    · exact Or.inr h
    · left
      rw [Finset.mem_val]
      exact hf.mem_toFinset.2 h⟩⟩

instance (v : HeightOneSpectrum (𝓞 K)) :
    IsScalarTower (𝓞 K) (v.adicCompletionIntegers K) (v.adicCompletion K) :=
  adicCompletion.instIsScalarTower' (𝓞 K) K v

abbrev LocalQuotient (I : FractionalIdeal (𝓞 K)⁰ K) (v : HeightOneSpectrum (𝓞 K)) :=
  v.adicCompletion K ⧸ localIdeal I v

def toLocalQuotients {I : FractionalIdeal (𝓞 K)⁰ K} (hI : I ≠ 0) :
    K →ₗ[𝓞 K] DirectSum (HeightOneSpectrum (𝓞 K)) (LocalQuotient I) where
  toFun x := dfinsuppOfFinite (fun v ↦ Submodule.Quotient.mk (x : v.adicCompletion K))
    (Filter.eventually_cofinite.1 ((eventually_coe_mem_localIdeal hI x).mono fun v hv ↦
      (Submodule.Quotient.mk_eq_zero _).2 hv))
  map_add' x y := by
    refine DFinsupp.ext fun v ↦ ?_
    rw [DirectSum.add_apply]
    change Submodule.Quotient.mk ((x + y : K) : v.adicCompletion K) =
      Submodule.Quotient.mk (x : v.adicCompletion K) + Submodule.Quotient.mk (y : v.adicCompletion K)
    rw [adicCompletion.coe_add, Submodule.Quotient.mk_add]
  map_smul' r x := by
    refine DFinsupp.ext fun v ↦ ?_
    rw [RingHom.id_apply, DirectSum.smul_apply]
    change Submodule.Quotient.mk ((r • x : K) : v.adicCompletion K) =
      r • Submodule.Quotient.mk (p := localIdeal I v) (x : v.adicCompletion K)
    rw [← Submodule.Quotient.mk_smul, Algebra.smul_def, Algebra.smul_def (A := v.adicCompletion K),
      adicCompletion.coe_mul]
    rfl

theorem toLocalQuotients_apply {I : FractionalIdeal (𝓞 K)⁰ K} (hI : I ≠ 0) (x : K)
    (v : HeightOneSpectrum (𝓞 K)) :
    toLocalQuotients hI x v = Submodule.Quotient.mk (x : v.adicCompletion K) :=
  rfl

theorem toLocalQuotients_eq_zero_iff {I : FractionalIdeal (𝓞 K)⁰ K} (hI : I ≠ 0) {x : K} :
    toLocalQuotients hI x = 0 ↔ x ∈ I := by
  rw [mem_iff_forall_mem_localIdeal hI, DFinsupp.ext_iff]
  simp only [toLocalQuotients_apply, DFinsupp.coe_zero, Pi.zero_apply,
    Submodule.Quotient.mk_eq_zero]

theorem toLocalQuotients_surjective {I : FractionalIdeal (𝓞 K)⁰ K} (hI : I ≠ 0) :
    Function.Surjective (toLocalQuotients hI) := by
  classical
  intro f
  choose y hy using fun v ↦ Submodule.Quotient.mk_surjective _ (f v)
  let z : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K := fun v ↦ if f v = 0 then 0 else y v
  have hz : ∀ v, Submodule.Quotient.mk (p := localIdeal I v) (z v) = f v := by
    intro v
    by_cases h : f v = 0
    · simp only [z, h, if_true, Submodule.Quotient.mk_zero]
    · simp only [z, h, if_false, hy]
  have hfin : {v | f v ≠ 0}.Finite :=
    f.support.finite_toSet.subset fun v hv ↦ DFinsupp.mem_support_iff.2 hv
  let a : FiniteAdeleRing (𝓞 K) K := ⟨z, Filter.eventually_cofinite.2 (hfin.subset fun v hv h ↦
    hv (by simp only [z, h, if_true]; exact (v.adicCompletionIntegers K).zero_mem))⟩
  obtain ⟨k, hk⟩ := exists_sub_mem_localIdeal hI a
  refine ⟨k, DFinsupp.ext fun v ↦ ?_⟩
  rw [toLocalQuotients_apply, ← hz v]
  exact ((Submodule.Quotient.eq _).2 (hk v)).symm

def quotientToLocalQuotients {I : FractionalIdeal (𝓞 K)⁰ K} (hI : I ≠ 0) :
    (K ⧸ (I : Submodule (𝓞 K) K)) →ₗ[𝓞 K] DirectSum (HeightOneSpectrum (𝓞 K)) (LocalQuotient I) where
  toFun q := Quotient.liftOn' q (toLocalQuotients hI) fun a b h ↦ by
    rw [Submodule.quotientRel_def] at h
    have h0 := (toLocalQuotients_eq_zero_iff hI).2 h
    calc toLocalQuotients hI a = toLocalQuotients hI (b + (a - b)) :=
          congrArg (toLocalQuotients hI) (by abel)
      _ = toLocalQuotients hI b + toLocalQuotients hI (a - b) := map_add _ _ _
      _ = toLocalQuotients hI b := by rw [h0, add_zero]
  map_add' := by
    rintro ⟨a⟩ ⟨b⟩
    exact map_add (toLocalQuotients hI) a b
  map_smul' := by
    rintro r ⟨a⟩
    exact map_smul (toLocalQuotients hI) r a

def quotientEquivLocalQuotients {I : FractionalIdeal (𝓞 K)⁰ K} (hI : I ≠ 0) :
    (K ⧸ (I : Submodule (𝓞 K) K)) ≃ₗ[𝓞 K] DirectSum (HeightOneSpectrum (𝓞 K)) (LocalQuotient I) :=
  LinearEquiv.ofBijective (quotientToLocalQuotients hI) ⟨by
      rw [injective_iff_map_eq_zero]
      rintro ⟨a⟩ h
      have h' : toLocalQuotients hI a = 0 := h
      exact (Submodule.Quotient.mk_eq_zero _).2 ((toLocalQuotients_eq_zero_iff hI).1 h'), by
      intro y
      obtain ⟨x, rfl⟩ := toLocalQuotients_surjective hI y
      exact ⟨Submodule.Quotient.mk x, rfl⟩⟩

@[simp]
theorem quotientEquivLocalQuotients_mk {I : FractionalIdeal (𝓞 K)⁰ K} (hI : I ≠ 0) (x : K) :
    quotientEquivLocalQuotients hI (Submodule.Quotient.mk x) = toLocalQuotients hI x :=
  rfl

namespace IdeleGroup

local notation "𝓘" => (FractionalIdeal (𝓞 K)⁰ K)ˣ

def localMul (s : IdeleGroup K) (I : 𝓘) (v : HeightOneSpectrum (𝓞 K)) :
    LocalQuotient (I : FractionalIdeal (𝓞 K)⁰ K) v ≃ₗ[𝓞 K]
      LocalQuotient ((s • I : 𝓘) : FractionalIdeal (𝓞 K)⁰ K) v :=
  (Submodule.Quotient.equiv (localIdeal (I : FractionalIdeal (𝓞 K)⁰ K) v)
    (localIdeal ((s • I : 𝓘) : FractionalIdeal (𝓞 K)⁰ K) v)
    ((finiteProj v s).mulLeftLinearEquiv (v.adicCompletionIntegers K) (v.adicCompletion K))
    (by
      rw [localIdeal_smul, Units.toLinearMap_mulLeftLinearEquiv, coe_finiteProj])).restrictScalars
    (𝓞 K)

theorem localMul_mk (s : IdeleGroup K) (I : 𝓘) (v : HeightOneSpectrum (𝓞 K))
    (y : v.adicCompletion K) :
    localMul s I v (Submodule.Quotient.mk y) =
      Submodule.Quotient.mk ((finiteProj v s : v.adicCompletion K) * y) :=
  rfl

def smulQuotient (s : IdeleGroup K) (I : 𝓘) :
    (K ⧸ ((I : FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K)) ≃ₗ[𝓞 K]
      K ⧸ (((s • I : 𝓘) : FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K) :=
  (quotientEquivLocalQuotients I.ne_zero).trans
    ((DFinsupp.mapRange.linearEquiv (localMul s I)).trans
      (quotientEquivLocalQuotients (s • I).ne_zero).symm)

theorem quotientEquivLocalQuotients_smulQuotient (s : IdeleGroup K) (I : 𝓘)
    (q : K ⧸ ((I : FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K)) :
    quotientEquivLocalQuotients (s • I).ne_zero (smulQuotient s I q) =
      DFinsupp.mapRange.linearEquiv (localMul s I) (quotientEquivLocalQuotients I.ne_zero q) := by
  rw [smulQuotient, LinearEquiv.trans_apply, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply]

theorem smulQuotient_mk_eq_mk_iff (s : IdeleGroup K) (I : 𝓘) (x y : K) :
    smulQuotient s I (Submodule.Quotient.mk x) = Submodule.Quotient.mk y ↔
      ∀ v : HeightOneSpectrum (𝓞 K), (finiteProj v s : v.adicCompletion K) * (x : v.adicCompletion K) -
        (y : v.adicCompletion K) ∈ localIdeal ((s • I : 𝓘) : FractionalIdeal (𝓞 K)⁰ K) v := by
  rw [← (quotientEquivLocalQuotients (s • I).ne_zero).injective.eq_iff,
    quotientEquivLocalQuotients_smulQuotient, quotientEquivLocalQuotients_mk,
    quotientEquivLocalQuotients_mk, DFinsupp.ext_iff]
  refine forall_congr' fun v ↦ ?_
  rw [DFinsupp.mapRange.linearEquiv_apply, DFinsupp.mapRange_apply, toLocalQuotients_apply,
    toLocalQuotients_apply, localMul_mk, Submodule.Quotient.eq]

end IdeleGroup

end

end GroundTheory.Global
