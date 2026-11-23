module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.IsCharZeroPt
public import Mathlib.NumberTheory.Padics.Complex
public import Mathlib.NumberTheory.Padics.PadicIntegers
public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.CzBasic
public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.FreeEtaleSheafZmodExistsHomSendingGenerator
import Mathlib.Algebra.Module.StablyFree.Basic
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
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.DirichletPrimeToLPartMulLPowerPart

@[expose] public section

open Matrix IsLocalRing ReciprocityTheory.Gal UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Alg UpperTheory.V.UnitaryThreeInertia

private theorem norm_two_eq_one {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [CharZero O]
    [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] (h : IsUnit (2 : O)) : ‖(2 : PadicAlgCl l)‖ = 1 := by
  have h2 : IsUnit (2 : ℤ_[l]) := by
    by_contra hn
    have hl : (l : ℤ) ∣ 2 := by
      rw [PadicInt.isUnit_iff] at hn
      have hlt : ‖((2 : ℤ) : ℤ_[l])‖ < 1 := lt_of_le_of_ne (PadicInt.norm_le_one _) (by simpa using hn)
      exact PadicInt.norm_int_lt_one_iff_dvd 2 |>.1 hlt
    have hinj : Function.Injective (algebraMap ℤ_[l] O) := by
      rw [injective_iff_map_eq_zero]
      intro x hx
      by_contra hx0
      have e := PadicInt.unitCoeff_spec hx0
      rw [e, map_mul, map_pow, map_natCast] at hx
      rcases mul_eq_zero.1 hx with h1 | h1
      · exact ((Units.isUnit _).map (algebraMap ℤ_[l] O)).ne_zero h1
      · exact pow_ne_zero _ (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero) h1
    haveI : FaithfulSMul ℤ_[l] O := (faithfulSMul_iff_algebraMap_injective _ _).2 hinj
    exact hn (isUnit_of_map_unit (algebraMap ℤ_[l] O) 2 (by rwa [map_ofNat]))
  have h3 : ‖(2 : ℚ_[l])‖ = 1 := by
    have := PadicInt.isUnit_iff.1 h2
    rw [PadicInt.norm_def] at this
    exact_mod_cast this
  rw [← map_ofNat (algebraMap ℚ_[l] (PadicAlgCl l)) 2, norm_algebraMap', h3]

theorem UpperTheory.V.UnitaryThreeInertia.conj_of_matIso :
    ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (maximalIdeal O) O] [CharZero O] [Finite (ResidueField O)]
      [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] [Algebra O (PadicAlgCl l)] [IsScalarTower ℤ_[l] O (PadicAlgCl l)] [FaithfulSMul O (PadicAlgCl l)]
      {G Γ ι : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
      [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ] [T2Space Γ] [TotallyDisconnectedSpace Γ] [Finite ι] (F : Frame O G Γ ι), F.Ok →
    ∀ g₁, F.Marked g₁ → ∀ (r : Γ →* GG (m := 3) (R := PadicAlgCl l)), F.IsCharZeroPt g₁ r →
      ∀ r' : Γ →* GG (m := 3) (R := PadicAlgCl l), F.IsCharZeroPt g₁ r' → TypeI F.η r →
        MatIso F.η.ker (mats r) (mats r') → ∃ t, r' = conjBy (tor (PadicAlgCl l) t) r := by
  intro l _ O _ _ _ _ _ _ _ _ _ _ _ G Γ ι _ _ _ _ _ _ _ _ _ _ _ _ _ F hF g₁ hg r hr r' hr' hI hiso
  obtain ⟨m, n, -, hz, hz1, -⟩ := isCharZeroPt_basic F hF g₁ hg r hr
  obtain ⟨m', n', -, hz', hz1', -⟩ := isCharZeroPt_basic F hF g₁ hg r' hr'
  refine conjBy_tor_of_iso F.η r r' F.c g₁ two_ne_zero m m' hF.ηc hg.1 n n' ?_ ?_ ?_ (Or.inl hI) hiso
  · rw [← norm_ne_zero_iff, hz1]; exact one_ne_zero
  · rw [← norm_ne_zero_iff, hz1']; exact one_ne_zero
  · intro e
    have h2 := norm_two_eq_one (l := l) hF.two
    have hle := IsUltrametricDist.norm_add_le_max
      (zeta F.c g₁ r - zeta F.c g₁ (F.rz (PadicAlgCl l)))
      (-(zeta F.c g₁ r' - zeta F.c g₁ (F.rz (PadicAlgCl l))))
    rw [norm_neg] at hle
    have hlt := lt_of_le_of_lt hle (max_lt hz hz')
    have e2 : zeta F.c g₁ r - zeta F.c g₁ (F.rz (PadicAlgCl l)) +
        -(zeta F.c g₁ r' - zeta F.c g₁ (F.rz (PadicAlgCl l))) = 2 * zeta F.c g₁ r := by
      rw [e]; ring
    rw [e2, norm_mul, h2, hz1, mul_one] at hlt
    exact lt_irrefl _ hlt
