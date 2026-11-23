module

public import Development.WeilBound.CoreStatements.CrystallinePeriodRings.ExistsMapEqOfPowMul
public import Development.WeilBound.CoreStatements.CrystallinePeriodRings.FrobAinfMapFrobenius
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

namespace PositivityTheory.LocInh

open GroundTheory.PAdicHodge Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc

variable {l : ℕ} [Fact l.Prime]

theorem galT_coeff (g : GQ l) (x : OCb l) (n : ℕ) (y : OC l)
    (h : PreTilt.coeff n x = Ideal.Quotient.mk (Ideal.span {((l : ℕ) : OC l)}) y) :
    ∃ y' : OC l, (y' : ℂ_[l]) = actC l g (y : ℂ_[l]) ∧
      PreTilt.coeff n (galT g x) = Ideal.Quotient.mk (Ideal.span {((l : ℕ) : OC l)}) y' := by
  refine ⟨(Per6.intEquiv l).symm (integerMap (galCp (Per6.toBot g) : ℂ_[l] →+* ℂ_[l])
    (AInf.norm_galCp_toRingHom (Per6.toBot g)) (Per6.intEquiv l y)), rfl, ?_⟩
  have h1 := frob_coeff_tiltMap x n y h
  have h2 : PreTilt.coeff n (galT g x) = (Per6.modPEquiv l).symm
      (modPMap (galCp (Per6.toBot g) : ℂ_[l] →+* ℂ_[l]) (AInf.norm_galCp_toRingHom (Per6.toBot g))
        (PreTilt.coeff n (Per6.tiltMap l x))) := rfl
  rw [h2, h1, modPMap_mk]
  rfl

theorem galT_ext {g : GQ l} {x z : OCb l}
    (h : ∀ (n : ℕ) (y : OC l),
      PreTilt.coeff n x = Ideal.Quotient.mk (Ideal.span {((l : ℕ) : OC l)}) y →
      ∃ y' : OC l, (y' : ℂ_[l]) = actC l g (y : ℂ_[l]) ∧
        PreTilt.coeff n z = Ideal.Quotient.mk (Ideal.span {((l : ℕ) : OC l)}) y') :
    galT g x = z := by
  refine Perfection.ext fun n => ?_
  obtain ⟨y, hy⟩ := Ideal.Quotient.mk_surjective (PreTilt.coeff n x)
  obtain ⟨y₁, h₁, e₁⟩ := galT_coeff g x n y hy.symm
  obtain ⟨y₂, h₂, e₂⟩ := h n y hy.symm
  have : y₁ = y₂ := Subtype.ext (h₁.trans h₂.symm)
  exact e₁.trans (this ▸ e₂.symm)

theorem ιCD_aB (a : Ainf l) :
    ιCD l (Per6.aB l a) = algebraMap (Per6.BdRp l) (Per6.BdR l) (Per6.aD l a) := by
  rw [frob_aB_apply, ιCD_cB, cD_apply, ACris.iota_algebraMap]
  rfl

theorem wittTo_injective : Function.Injective (wittToBDeRhamPlus ↥(normInteger ℂ_[l]) l) := by
  rw [injective_iff_map_eq_zero]
  intro w hw
  obtain ⟨ξ, hξ, h1⟩ := IsPerfectoidField.exists_mem_ker_fontaineTheta_isUnit_coeff_one ℂ_[l] l
  have hker := IsPerfectoidField.ker_fontaineTheta_eq_span hξ h1
  have hH := IsPerfectoidField.isHausdorff_span_of_isUnit_coeff_one hξ h1
  refine hH.haus w fun n => ?_
  rw [SModEq.zero, smul_eq_mul, Ideal.mul_top, ← hker, ACris.ker_eq_span_xiGen,
    Ideal.span_singleton_pow, ← ACris.algebraMap_dvd_iff, map_pow,
    ← toBDeRhamPlus_mem_span_pow_iff ACris.ker_eq_span_xiGen]
  have : toBDeRhamPlus ↥(normInteger ℂ_[l]) l (algebraMap _ _ w) = 0 := hw
  rw [this]
  exact Submodule.zero_mem _

theorem ainfMap_injective : Function.Injective (Per6.ainfMap l) :=
  WittVector.map_injective _ (tiltEquiv l).injective

theorem ainfMap_surjective : Function.Surjective (Per6.ainfMap l) :=
  WittVector.map_surjective _ (tiltEquiv l).surjective

theorem aB_injective : Function.Injective (Per6.aB l) := by
  intro a b h
  have h1 := congrArg (ιCD l) h
  rw [ιCD_aB, ιCD_aB] at h1
  exact ainfMap_injective (wittTo_injective
    (IsPerfectoidField.algebraMap_bDeRham_injective (K := ℂ_[l]) (p := l) h1))

theorem aB_act (g : GQ l) (a : Ainf l) :
    Per6.aB l (WittVector.map (galT g) a) = Per6.σB g (Per6.aB l a) := by
  have h : Per6.ainfMap l (WittVector.map (galT g) a) = Per6.toBot g • Per6.ainfMap l a := by
    refine WittVector.ext fun n => ?_
    rw [AInf.gal_smul_coeff]
    exact tiltMap_tiltInv l _
  rw [frob_aB_apply, frob_aB_apply, σB_cB, h, ← ACris.gal_smul_algebraMap, ACris.gal_smul_def]

theorem tiltMap_εO : Per6.tiltMap l (εO l) = epsilon l := tiltMap_tiltInv l _

theorem fil_nat (b : Per6.BdRp l) (n : ℕ) :
    algebraMap (Per6.BdRp l) (Per6.BdR l) b ∈ Per6.FilD l n ↔ b ∈ RingHom.ker (Per6.θD l) ^ n := by
  rw [Per6.θD, ← IsPerfectoidField.maximalIdeal_bDeRhamPlus]
  exact IsPerfectoidField.algebraMap_mem_fil_iff b n

theorem θD_aD (a : Ainf l) : Per6.θD l (Per6.aD l a) =
    ((WittVector.fontaineTheta ↥(normInteger ℂ_[l]) l (Per6.ainfMap l a) : normInteger ℂ_[l]) : ℂ_[l]) :=
  IsPerfectoidField.thetaBDeRhamPlusField_wittToBDeRhamPlus l _

theorem ainf_zA (z : ℤ_[l]) :
    Per6.ainfMap l (Per6.zA l z) = IsPerfectoidField.padicIntToWitt l z := by
  ext n
  simp only [Per6.ainfMap, Per6.zA, IsPerfectoidField.padicIntToWitt, RingHom.comp_apply,
    WittVector.map_coeff]
  exact (RingHom.congr_fun (RingHom.ext_zmod ((Per6.tiltMap l).comp (ZMod.castHom (dvd_refl l) _))
    (ZMod.castHom (dvd_refl l) _)) _)

theorem qB_coe (z : ℤ_[l]) : qB l (z : ℚ_[l]) = Per6.zB l z := by
  rw [frob_qB_coe, Per6.zB, RingHom.comp_apply, frob_aB_apply, ainf_zA]

theorem oD_coe (z : ℤ_[l]) : oD l (algebraMap ℚ_[l] (Om l) (z : ℚ_[l])) = Per6.zD l z := by
  rw [← ιCD_qB, qB_coe, Per6.zB, RingHom.comp_apply, ιCD_aB]
  rfl

theorem isCrisDR_iff (f : Per6.Bcris l →+* Per6.BdR l) : Per6.IsCrisDR l f ↔ f = ιCD l := by
  constructor
  · intro h
    exact bcris_hom_ext fun x => (h x).trans ((ιCD_cB x).trans (cD_apply x)).symm
  · rintro rfl x
    exact (ιCD_cB x).trans (cD_apply x)

theorem isLog_iff (ε : OCb l) (y : Per6.BdRp l) : Per6.IsLog l ε y ↔
    ∃ h : PreTilt.untilt (Per6.tiltMap l ε) = 1, y = fontaineT (Per6.tiltMap l ε) h := by
  have e : Per6.aD l (WittVector.teichmuller l ε) - 1 = muBdR l (Per6.tiltMap l ε) := by
    rw [muBdR_eq, ← frob_ainfMap_teich]
    rfl
  have hm : RingHom.ker (Per6.θD l) = IsLocalRing.maximalIdeal (Per6.BdRp l) :=
    (IsPerfectoidField.maximalIdeal_bDeRhamPlus (K := ℂ_[l]) (p := l)).symm
  unfold Per6.IsLog
  rw [e]
  constructor
  · intro h
    have h1 := h 1
    have h2 := h 2
    simp only [Finset.Ico_self, Finset.sum_empty, sub_zero, pow_one] at h1
    have h3 : y - muBdR l (Per6.tiltMap l ε) ∈ RingHom.ker (Per6.θD l) := by
      have h4 := Ideal.pow_le_self two_ne_zero h2
      simpa using h4
    have h5 : Per6.θD l (muBdR l (Per6.tiltMap l ε)) = 0 := by
      rw [RingHom.mem_ker] at h1 h3
      rw [map_sub, h1, zero_sub, neg_eq_zero] at h3
      exact h3
    have hε : PreTilt.untilt (Per6.tiltMap l ε) = 1 := by
      rw [← e, map_sub, map_one, θD_aD, frob_ainfMap_teich, WittVector.fontaineTheta_teichmuller,
        sub_eq_zero] at h5
      exact Subtype.ext h5
    refine ⟨hε, sub_eq_zero.1 (IsPerfectoidField.eq_zero_of_forall_mem_maximalIdeal_pow fun n => ?_)⟩
    have h6 := h n
    rw [hm] at h6
    have h7 := sub_mem h6 (fontaineT_sub_sum_mem hε n)
    rwa [sub_sub_sub_cancel_right] at h7
  · rintro ⟨hε, rfl⟩ n
    rw [hm]
    exact fontaineT_sub_sum_mem hε n

end PositivityTheory.LocInh
