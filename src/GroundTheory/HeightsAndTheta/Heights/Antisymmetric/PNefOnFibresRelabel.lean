module

public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.RingTheory.Length
public import Mathlib.RingTheory.Localization.AtPrime.Basic
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import Lean.Elab.MutualDef
public import Mathlib.RingTheory.Ideal.MinimalPrime.Localization
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.IsSemipositiveOn

@[expose] public section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial

section RingEquivTransport

variable {A A' : Type*} [CommRing A] [CommRing A'] (σ : A ≃+* A')

theorem mem_map_ringEquiv_iff (I : Ideal A) (x : A) : σ x ∈ I.map σ ↔ x ∈ I := by
  rw [← Ideal.mem_comap, Ideal.comap_map_of_bijective σ σ.bijective]

theorem isPrime_map_ringEquiv_iff (V : Ideal A) : (V.map σ).IsPrime ↔ V.IsPrime := by
  constructor
  · intro hV
    rw [← Ideal.comap_map_of_bijective σ σ.bijective (I := V)]
    exact Ideal.comap_isPrime σ (V.map σ)
  · intro hV
    exact Ideal.map_isPrime_of_equiv σ

theorem map_ringEquiv_injective : Function.Injective (Ideal.map σ : Ideal A → Ideal A') :=
  fun I J hIJ => by
    rw [← Ideal.comap_map_of_bijective σ σ.bijective (I := I), hIJ,
      Ideal.comap_map_of_bijective σ σ.bijective]

theorem ringKrullDim_quotient_map (V : Ideal A) :
    ringKrullDim (A' ⧸ V.map σ) = ringKrullDim (A ⧸ V) :=
  (ringKrullDim_eq_of_ringEquiv (Ideal.quotientEquiv V (V.map σ) σ rfl)).symm

theorem length_int_quotient_map (I : Ideal A) :
    Module.length ℤ (A' ⧸ I.map σ) = Module.length ℤ (A ⧸ I) :=
  ((Ideal.quotientEquiv I (I.map σ) σ rfl).toAddEquiv.toIntLinearEquiv.length_eq).symm

theorem minimalPrimes_map_ringEquiv (I : Ideal A) :
    (I.map σ).minimalPrimes = Ideal.map σ '' I.minimalPrimes := by
  have := Ideal.minimalPrimes_map_of_surjective (f := (σ : A →+* A')) σ.surjective I
  rw [RingHom.ker_coe_equiv, sup_bot_eq] at this
  exact this

theorem map_mem_primeCompl (V : Ideal A) [V.IsPrime] [(V.map σ).IsPrime] (s : V.primeCompl) :
    σ s ∈ (V.map σ).primeCompl :=
  Ideal.mem_primeCompl_iff.2 fun hs => Ideal.mem_primeCompl_iff.1 s.2 ((mem_map_ringEquiv_iff σ V s).1 hs)

theorem primeCompl_map_ringEquiv (V : Ideal A) [V.IsPrime] [(V.map σ).IsPrime] :
    V.primeCompl.map σ.toMonoidHom = (V.map σ).primeCompl := by
  ext x
  rw [Submonoid.mem_map]
  constructor
  · rintro ⟨s, hs, rfl⟩
    exact map_mem_primeCompl σ V ⟨s, hs⟩
  · intro hx
    refine ⟨σ.symm x, Ideal.mem_primeCompl_iff.2 fun h' => Ideal.mem_primeCompl_iff.1 hx ?_, by simp⟩
    simpa using (mem_map_ringEquiv_iff σ V (σ.symm x)).2 h'

def locRingEquiv (V : Ideal A) [V.IsPrime] [(V.map σ).IsPrime] :
    Localization.AtPrime V ≃+* Localization.AtPrime (V.map σ) :=
  IsLocalization.ringEquivOfRingEquiv (Localization.AtPrime V) (Localization.AtPrime (V.map σ)) σ
    (primeCompl_map_ringEquiv σ V)

theorem locRingEquiv_mk (V : Ideal A) [V.IsPrime] [(V.map σ).IsPrime] (a : A) (t : V.primeCompl) :
    locRingEquiv σ V (Localization.mk a t) = Localization.mk (σ a) ⟨σ t, map_mem_primeCompl σ V t⟩ := by
  rw [Localization.mk_eq_mk'_apply, Localization.mk_eq_mk'_apply, locRingEquiv,
    IsLocalization.ringEquivOfRingEquiv_mk']

def quotEquivMap (J : Ideal A) : A ⧸ J ≃+* A' ⧸ J.map σ :=
  Ideal.quotientEquiv J (J.map σ) σ rfl

theorem quotEquivMap_smul (J : Ideal A) (a : A) (m : A ⧸ J) :
    quotEquivMap σ J (a • m) = σ a • quotEquivMap σ J m := by
  rw [Algebra.smul_def, Algebra.smul_def, map_mul]
  rfl

section LocLength

variable (J V : Ideal A) [V.IsPrime] [(V.map σ).IsPrime]

def locQuotMap :
    LocalizedModule V.primeCompl (A ⧸ J) → LocalizedModule (V.map σ).primeCompl (A' ⧸ J.map σ) :=
  fun x => x.liftOn (fun p => LocalizedModule.mk (quotEquivMap σ J p.1)
      ⟨σ p.2, map_mem_primeCompl σ V p.2⟩) (by
    rintro ⟨m, s⟩ ⟨m', s'⟩ ⟨u, hu⟩
    rw [LocalizedModule.mk_eq]
    refine ⟨⟨σ u, map_mem_primeCompl σ V u⟩, ?_⟩
    have := congrArg (quotEquivMap σ J) hu
    simpa only [Submonoid.smul_def, quotEquivMap_smul] using this)

theorem locQuotMap_mk (m : A ⧸ J) (s : V.primeCompl) :
    locQuotMap σ J V (LocalizedModule.mk m s) =
      LocalizedModule.mk (quotEquivMap σ J m) ⟨σ s, map_mem_primeCompl σ V s⟩ := by
  rw [locQuotMap, LocalizedModule.liftOn_mk]

def locQuotSemilinear :
    LocalizedModule V.primeCompl (A ⧸ J) →ₛₗ[(locRingEquiv σ V : Localization.AtPrime V →+*
      Localization.AtPrime (V.map σ))] LocalizedModule (V.map σ).primeCompl (A' ⧸ J.map σ) where
  toFun := locQuotMap σ J V
  map_add' x y := by
    induction x using LocalizedModule.induction_on with | h m s => ?_
    induction y using LocalizedModule.induction_on with | h m' s' => ?_
    rw [LocalizedModule.mk_add_mk, locQuotMap_mk, locQuotMap_mk, locQuotMap_mk,
      LocalizedModule.mk_add_mk]
    simp only [Submonoid.smul_def, map_add (f := _), quotEquivMap_smul]
    congr 1
    ext
    simp
  map_smul' r x := by
    induction r using Localization.induction_on with | H p => ?_
    obtain ⟨a, t⟩ := p
    induction x using LocalizedModule.induction_on with | h m s => ?_
    show locQuotMap σ J V _ = (locRingEquiv σ V (Localization.mk a t)) • locQuotMap σ J V _
    rw [LocalizedModule.mk_smul_mk, locQuotMap_mk, locQuotMap_mk, locRingEquiv_mk,
      LocalizedModule.mk_smul_mk, quotEquivMap_smul]
    congr 1
    ext
    simp

theorem locQuotSemilinear_apply (x : LocalizedModule V.primeCompl (A ⧸ J)) :
    locQuotSemilinear σ J V x = locQuotMap σ J V x := rfl

theorem locQuotSemilinear_injective : Function.Injective (locQuotSemilinear σ J V) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  induction x using LocalizedModule.induction_on with | h m s => ?_
  rw [locQuotSemilinear_apply, locQuotMap_mk, ← LocalizedModule.zero_mk 1, LocalizedModule.mk_eq] at hx
  obtain ⟨u, hu⟩ := hx
  rw [smul_zero, smul_zero, one_smul, Submonoid.smul_def] at hu
  have hu' : σ.symm u ∈ V.primeCompl := Ideal.mem_primeCompl_iff.2 fun h' =>
    Ideal.mem_primeCompl_iff.1 u.2 (by simpa using (mem_map_ringEquiv_iff σ V _).2 h')
  rw [← LocalizedModule.zero_mk 1, LocalizedModule.mk_eq]
  refine ⟨⟨σ.symm u, hu'⟩, ?_⟩
  rw [smul_zero, smul_zero, one_smul, Submonoid.smul_def]
  apply (quotEquivMap σ J).injective
  rw [quotEquivMap_smul, map_zero, RingEquiv.apply_symm_apply]
  exact hu

theorem locQuotSemilinear_surjective : Function.Surjective (locQuotSemilinear σ J V) := by
  intro x
  induction x using LocalizedModule.induction_on with | h m s => ?_
  have hs : σ.symm s ∈ V.primeCompl := Ideal.mem_primeCompl_iff.2 fun h' =>
    Ideal.mem_primeCompl_iff.1 s.2 (by simpa using (mem_map_ringEquiv_iff σ V _).2 h')
  refine ⟨LocalizedModule.mk ((quotEquivMap σ J).symm m) ⟨σ.symm s, hs⟩, ?_⟩
  rw [locQuotSemilinear_apply, locQuotMap_mk, RingEquiv.apply_symm_apply]
  congr 1
  ext
  simp

theorem length_localizedModule_quotient_map :
    Module.length (Localization.AtPrime (V.map σ))
        (LocalizedModule (V.map σ).primeCompl (A' ⧸ J.map σ)) =
      Module.length (Localization.AtPrime V) (LocalizedModule V.primeCompl (A ⧸ J)) := by
  have : RingHomSurjective (locRingEquiv σ V : Localization.AtPrime V →+*
      Localization.AtPrime (V.map σ)) := ⟨(locRingEquiv σ V).surjective⟩
  apply WithBot.coe_injective
  rw [Module.coe_length, Module.coe_length]
  exact (Order.krullDim_eq_of_orderIso (Submodule.orderIsoMapComapOfBijective
    (locQuotSemilinear σ J V) ⟨locQuotSemilinear_injective σ J V,
      locQuotSemilinear_surjective σ J V⟩)).symm

end LocLength

end RingEquivTransport

section Relabel

set_option linter.unusedSectionVars false

variable {K K' : Type} [Fintype K] [Fintype K'] {ι : K → Type} {ι' : K' → Type}
  [∀ k, Fintype (ι k)] [∀ k, Fintype (ι' k)] (ε : K ≃ K') (h : ∀ k, ι k = ι' (ε k))

end Relabel

end GroundTheory.Heights₂.Heights
