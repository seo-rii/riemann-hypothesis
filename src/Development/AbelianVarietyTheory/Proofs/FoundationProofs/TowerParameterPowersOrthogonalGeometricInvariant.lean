module

public import Development.AbelianVarietyTheory.Definitions.Foundations.NotCoboundaryConstantOne
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CompletedLaurentIsDVRStatement
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DivMemSubalgebraOfValuationLeOneOfUniformizerStatement
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsFinitePidSubalgebraDivPadicIntStatement
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsGaloisInvariantValuationIntegersEqIntegral
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsGeneratorValuationPrimeDvdPowSubOfFinitePaStatement
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsPowDivPrimeZpowIntegralClosureUnit
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeometricFixedMemClosureFiniteAlgZpStatement
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ResidueTowerPowersLinearIndependent
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.TowerParameterNotPowModMaximalIdealAdjoinAlgebra
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.UnramifiedIntegersAdicCompleteStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open GlobalTheory.K5

namespace GlobalTheory.K5.Orth

variable {p : ℕ} [hp : Fact p.Prime] {Ω : Type} [Field Ω] [Algebra (O0 p) Ω]

theorem p_ne_zero' (h : IsClo p Ω) : (p : Ω) ≠ 0 := by
  have := GlobalTheory.K5.Basic.charZero_of_isClo h
  exact_mod_cast hp.out.ne_zero

theorem not_isInt_inv_p (h : IsClo p Ω) : ¬ IsInt (p := p) ((p : Ω)⁻¹) := by
  intro hi
  apply GlobalTheory.K5.Basic.not_cong_one_zero h 1 one_ne_zero
  refine ⟨(p : Ω)⁻¹, hi, ?_⟩
  rw [pow_one, sub_zero, mul_inv_cancel₀ (p_ne_zero' h)]

theorem isInt_natPow_p (k : ℕ) : IsInt (p := p) ((p : Ω) ^ k) := by
  have := GlobalTheory.K5.Basic.isInt_intCast (p := p) (Ω := Ω) ((p : ℤ) ^ k)
  simpa using this

theorem isInt_div (h : IsClo p Ω) {x y : Ω} (hy : y ≠ 0) {a a' : ℤ} {b b' : ℕ} (hb : 0 < b)
    (hb' : 0 < b') (h1 : IsInt (p := p) (x ^ b / (p : Ω) ^ a))
    (h2 : IsInt (p := p) ((p : Ω) ^ a' / y ^ b'))
    (hle : (a' : ℚ) / b' ≤ a / b) : IsInt (p := p) (x / y) := by
  have hp0 := p_ne_zero' h
  have he : 0 ≤ a * b' - a' * b := by
    have hb0 : (0 : ℚ) < b := by exact_mod_cast hb
    have hb0' : (0 : ℚ) < b' := by exact_mod_cast hb'
    rw [div_le_div_iff₀ hb0' hb0] at hle
    have : (a' * b : ℚ) ≤ a * b' := hle
    exact_mod_cast (sub_nonneg.2 this)
  obtain ⟨e, he'⟩ := Int.eq_ofNat_of_zero_le he
  have key : (x / y) ^ (b * b') = (x ^ b / (p : Ω) ^ a) ^ b' * ((p : Ω) ^ a' / y ^ b') ^ b *
      (p : Ω) ^ e := by
    have hpe : (p : Ω) ^ e = ((p : Ω) ^ a) ^ b' / ((p : Ω) ^ a') ^ b := by
      rw [← zpow_natCast, ← he', zpow_sub₀ hp0, zpow_mul, zpow_mul, zpow_natCast, zpow_natCast]
    rw [hpe]
    have hP : (p : Ω) ^ a ≠ 0 := zpow_ne_zero _ hp0
    have hP' : (p : Ω) ^ a' ≠ 0 := zpow_ne_zero _ hp0
    generalize (p : Ω) ^ a = P at *
    generalize (p : Ω) ^ a' = P' at *
    have e1 : (y ^ b') ^ b = y ^ (b * b') := by rw [← pow_mul, mul_comm]
    have e2 : (x ^ b) ^ b' = x ^ (b * b') := by rw [← pow_mul]
    simp only [div_pow, e1, e2]
    have h3 : (P ^ b') ≠ 0 := pow_ne_zero _ hP
    have h4 : (P' ^ b) ≠ 0 := pow_ne_zero _ hP'
    have h5 : y ^ (b * b') ≠ 0 := pow_ne_zero _ hy
    rw [div_mul_div_comm, div_mul_div_comm, div_eq_div_iff h5 (mul_ne_zero (mul_ne_zero h3 h5) h4)]
    ring
  have hi : IsInt (p := p) ((x / y) ^ (b * b')) := by
    rw [key]
    exact ((h1.pow b').mul (h2.pow b)).mul (isInt_natPow_p e)
  exact IsIntegral.of_pow (Nat.mul_pos hb hb') hi

end GlobalTheory.K5.Orth

namespace GlobalTheory.K5.Orth

variable {p : ℕ} [hp : Fact p.Prime] {Ω : Type} [Field Ω] [Algebra (O0 p) Ω]

theorem normalize (h : IsClo p Ω)
    (hV : ∀ x : Ω, x ≠ 0 → ∃ (a : ℤ) (b : ℕ), 0 < b ∧ IsInt (p := p) (x ^ b / (p : Ω) ^ a) ∧
      IsInt (p := p) ((p : Ω) ^ a / x ^ b))
    (n : ℕ) (c : ℕ → Ω) (hc : ∃ j < n, ¬ IsInt (p := p) (c j)) :
    ∃ l : Ω, IsAlgZp (p := p) l ∧ (∃ m : ℕ, 0 < m ∧ IsInt (p := p) (l ^ m / (p : Ω))) ∧
      (∀ j < n, IsInt (p := p) (l * c j)) ∧
      ∃ j < n, ¬ ∃ m : ℕ, 0 < m ∧ IsInt (p := p) ((l * c j) ^ m / (p : Ω)) := by
  classical
  have hp0 := p_ne_zero' h
  choose A B hB h1 h2 using hV
  let w : Ω → ℚ := fun x => if hx : x = 0 then 0 else (A x hx : ℚ) / B x hx
  obtain ⟨j1, hj1, hnj1⟩ := hc
  have hc1 : c j1 ≠ 0 := fun e => hnj1 (e ▸ isIntegral_zero)
  obtain ⟨j0, hj0, hmin⟩ := Finset.exists_min_image ((Finset.range n).filter (fun j => c j ≠ 0))
    (fun j => w (c j)) ⟨j1, by simp [hj1, hc1]⟩
  simp only [Finset.mem_filter, Finset.mem_range] at hj0 hmin
  obtain ⟨hj0n, hx0⟩ := hj0
  have hdiv : ∀ j < n, c j ≠ 0 → IsInt (p := p) (c j / c j0) := by
    intro j hj hcj
    refine isInt_div h hx0 (hB _ hcj) (hB _ hx0) (h1 _ hcj) (h2 _ hx0) ?_
    have := hmin j ⟨hj, hcj⟩
    simpa [w, hcj, hx0] using this
  have hb := hB _ hx0
  have hu := h1 _ hx0
  have hu' := h2 _ hx0
  generalize A (c j0) hx0 = a at hu hu'
  generalize B (c j0) hx0 = b at hb hu hu'
  have hxInt_of : IsInt (p := p) (c j0) → ∀ j < n, IsInt (p := p) (c j) := by
    intro hxi j hj
    by_cases hcj : c j = 0
    · rw [hcj]; exact isIntegral_zero
    · have := (hdiv j hj hcj).mul hxi
      rwa [div_mul_cancel₀ _ hx0] at this
  have ha : a < 0 := by
    by_contra hneg
    push Not at hneg
    obtain ⟨k, hk⟩ := Int.eq_ofNat_of_zero_le hneg
    apply hnj1
    apply hxInt_of _ j1 hj1
    have e : c j0 ^ b = (c j0 ^ b / (p : Ω) ^ a) * (p : Ω) ^ k := by
      rw [hk, zpow_natCast, div_mul_cancel₀ _ (pow_ne_zero _ hp0)]
    exact IsIntegral.of_pow hb (e ▸ hu.mul (isInt_natPow_p k))
  obtain ⟨k, hk⟩ := Int.eq_ofNat_of_zero_le (neg_nonneg.2 ha.le)
  have := h.clo
  obtain ⟨l, hl⟩ := IsAlgClosed.exists_pow_nat_eq ((p : Ω) ^ k) hb
  have hk1 : 1 ≤ k := by omega
  have hpa : (p : Ω) ^ a = ((p : Ω) ^ k)⁻¹ := by
    rw [← zpow_natCast, ← hk, zpow_neg, inv_inv]
  have hlx : (l * c j0) ^ b = c j0 ^ b / (p : Ω) ^ a := by
    rw [mul_pow, hl, hpa, div_inv_eq_mul, mul_comm]
  have hlxi : IsInt (p := p) (l * c j0) := IsIntegral.of_pow hb (hlx ▸ hu)
  refine ⟨l, ?_, ⟨b, hb, ?_⟩, ?_, j0, hj0n, ?_⟩
  · refine ⟨Polynomial.X ^ b - Polynomial.C ((p : ℤ_[p]) ^ k), Polynomial.X_pow_sub_C_ne_zero hb _, ?_⟩
    simp [hl]
  · rw [hl]
    have e : (p : Ω) ^ k / p = (p : Ω) ^ (k - 1) := by
      rw [div_eq_iff hp0, ← pow_succ, Nat.sub_add_cancel hk1]
    rw [e]
    exact isInt_natPow_p _
  · intro j hj
    by_cases hcj : c j = 0
    · rw [hcj, mul_zero]; exact isIntegral_zero
    · have e : (c j / c j0) * (l * c j0) = l * c j := by
        rw [mul_comm l (c j0), ← mul_assoc, div_mul_cancel₀ _ hx0, mul_comm]
      exact e ▸ (hdiv j hj hcj).mul hlxi
  · rintro ⟨m, hm, hsm⟩
    apply not_isInt_inv_p h
    have hz : l * c j0 ≠ 0 := by
      intro e0
      rw [e0, zero_pow hb.ne', eq_comm, div_eq_zero_iff] at hlx
      rcases hlx with h0 | h0
      · exact hx0 (pow_eq_zero_iff hb.ne' |>.1 h0)
      · exact zpow_ne_zero _ hp0 h0
    have hinv : (p : Ω) ^ a / c j0 ^ b = ((l * c j0) ^ b)⁻¹ := by rw [hlx, inv_div]
    rw [hinv] at hu'
    obtain ⟨b1, rfl⟩ : ∃ b1, b = b1 + 1 := ⟨b - 1, by omega⟩
    have e : ((p : Ω))⁻¹ = ((l * c j0) ^ m / p) ^ (b1 + 1) * (((l * c j0) ^ (b1 + 1))⁻¹) ^ m *
        (p : Ω) ^ b1 := by
      generalize l * c j0 = z at hz
      rw [div_pow, ← pow_mul, inv_pow, ← pow_mul, mul_comm (b1 + 1) m, pow_succ (p : Ω) b1]
      have hzz : z ^ (m * (b1 + 1)) ≠ 0 := pow_ne_zero _ hz
      have hpp : (p : Ω) ^ b1 ≠ 0 := pow_ne_zero _ hp0
      rw [div_mul_eq_mul_div, mul_inv_cancel₀ hzz, div_mul_eq_mul_div, one_mul, mul_comm _ (p : Ω),
        eq_div_iff (mul_ne_zero hp0 hpp), inv_mul_cancel_left₀ hp0]
    rw [e]
    exact ((hsm.pow _).mul (hu'.pow m)).mul (isInt_natPow_p b1)

end GlobalTheory.K5.Orth

namespace GlobalTheory.K5.Orth

theorem orth : ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], IsClo p Ω →
    ∀ (T : Tower p Ω) (N : ℕ) (c : ℕ → Ω), (∀ j, ∀ g ∈ Ggeo (p := p) Ω, g (c j) = c j) →
    IsInt (p := p) (∑ j ∈ Finset.range (p ^ N), c j * T.qq N ^ j) → ∀ j < p ^ N, IsInt (p := p) (c j) := by
  intro p hp Ω _ _ h T N c hfix hint
  classical
  by_contra hne
  push Not at hne
  have hp0 := p_ne_zero' h
  have := Basic.charZero_of_isClo h
  have hV : ∀ x : Ω, x ≠ 0 → ∃ (a : ℤ) (b : ℕ), 0 < b ∧
      IsInt (p := p) (x ^ b / (p : Ω) ^ a) ∧ IsInt (p := p) ((p : Ω) ^ a / x ^ b) := by
    intro x hx
    obtain ⟨_, _, hirr⟩ := completed_laurent_isDVR p
    have : IsAdicComplete (IsLocalRing.maximalIdeal (O0 p)) (O0 p) := by
      rw [hirr.maximalIdeal_eq]
      exact GlobalTheory.T.unramified_integers_adic_complete p
    have : FaithfulSMul (O0 p) Ω := (faithfulSMul_iff_algebraMap_injective _ _).2 h.inj
    let _ : Algebra (FractionRing (O0 p)) Ω := FractionRing.liftAlgebra (O0 p) Ω
    have : IsScalarTower (O0 p) (FractionRing (O0 p)) Ω :=
      FractionRing.isScalarTower_liftAlgebra (O0 p) Ω
    have : Algebra.IsAlgebraic (O0 p) Ω := h.alg
    have : Algebra.IsAlgebraic (FractionRing (O0 p)) Ω :=
      Algebra.IsAlgebraic.extendScalars (IsFractionRing.injective (O0 p) (FractionRing (O0 p)))
    simpa only [IsInt, map_natCast] using
      exists_pow_div_zpow_isIntegral (O0 p) (FractionRing (O0 p)) Ω (p : O0 p) hirr x hx
  obtain ⟨l, hlalg, ⟨m0, hm0, hlsm⟩, hlint, j0, hj0, hj0ns⟩ := normalize h hV (p ^ N) c hne
  choose S hSalg hSmem using fun j => GlobalTheory.T.geometric_fixed_mem_closure_finite_algZp p Ω h (c j) (hfix j)
  let S' : Finset Ω := insert l ((Finset.range (p ^ N)).biUnion S)
  have hS'alg : ∀ s ∈ S', IsAlgZp (p := p) s := by
    intro s hs
    rcases Finset.mem_insert.1 hs with rfl | hs
    · exact hlalg
    · obtain ⟨j, -, hj⟩ := Finset.mem_biUnion.1 hs
      exact hSalg j s hj
  set E := Subfield.closure (Set.range (algebraMap (O0 p) Ω) ∪ (S' : Set Ω)) with hE
  have hrange : Set.range (algebraMap (O0 p) Ω) ⊆ (E : Set Ω) :=
    fun x hx => Subfield.subset_closure (Or.inl hx)
  have hlE : l ∈ E := Subfield.subset_closure (Or.inr (Finset.mem_insert_self _ _))
  have hcE : ∀ j < p ^ N, c j ∈ E := by
    intro j hj
    refine Subfield.closure_mono ?_ (hSmem j)
    apply Set.union_subset_union_right
    intro s hs
    exact Finset.mem_insert_of_mem (Finset.mem_biUnion.2 ⟨j, Finset.mem_range.2 hj, hs⟩)
  have hsum : (∑ j ∈ Finset.range (p ^ N), (l * c j) * T.qq N ^ j) =
      l * ∑ j ∈ Finset.range (p ^ N), c j * T.qq N ^ j := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  have hsmall : ∃ m : ℕ, 0 < m ∧
      IsInt (p := p) ((∑ j ∈ Finset.range (p ^ N), (l * c j) * T.qq N ^ j) ^ m / (p : Ω)) := by
    refine ⟨m0, hm0, ?_⟩
    rw [hsum, mul_pow, mul_div_right_comm]
    exact hlsm.mul (hint.pow m0)
  obtain ⟨v, hv, _, hvp0, hvp1⟩ := exists_valuation_isInt p Ω h
  have hq : ∀ y ∈ E, IsInt (p := p) y →
      ¬ ∃ m : ℕ, 0 < m ∧ IsInt (p := p) ((y ^ p - algebraMap (O0 p) Ω (qO p)) ^ m / (p : Ω)) := by
    intro y hy hyint
    rintro ⟨m, _, hmint⟩
    obtain ⟨_, _, hirr⟩ := completed_laurent_isDVR p
    have huni := hirr.maximalIdeal_eq
    have hmax : (Ideal.span {(p : O0 p)}).IsMaximal := by
      rw [← huni]
      exact IsLocalRing.maximalIdeal.isMaximal _
    let : Algebra ℤ_[p] Ω := ((algebraMap (O0 p) Ω).comp (algebraMap ℤ_[p] (O0 p))).toAlgebra
    have : IsScalarTower ℤ_[p] (O0 p) Ω := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
    have hinj : Function.Injective (algebraMap ℤ_[p] Ω) := by
      rw [injective_iff_map_eq_zero]
      intro x hx
      by_contra hx0
      have e := PadicInt.unitCoeff_spec hx0
      rw [e, map_mul, map_pow, map_natCast] at hx
      rcases mul_eq_zero.1 hx with h | h
      · exact ((Units.isUnit _).map (algebraMap ℤ_[p] Ω)).ne_zero h
      · exact pow_ne_zero _ (Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero) h
    have hvint : ∀ x : Ω, IsIntegral ℤ_[p] x → v x ≤ 1 := fun x hx =>
      (hv x).2 (IsIntegral.tower_top (A := O0 p) hx)
    have hSalgZp : ∀ s ∈ S', IsAlgebraic ℤ_[p] s := by
      intro s hs
      obtain ⟨P, hP0, hP⟩ := hS'alg s hs
      exact ⟨P, hP0, by rwa [Polynomial.aeval_map_algebraMap] at hP⟩
    obtain ⟨R, hRfin, hRpid, hRS⟩ :=
      GlobalTheory.T.exists_finite_pid_subalgebra_padicInt_contains_fractions p Ω hinj S' hSalgZp
    obtain ⟨π, hπR, hπ0, hvπ, hpπ, f, hf, hstep⟩ :=
      GlobalTheory.T.exists_uniformizer_valuation_lt_one_frobenius_congr p Ω hinj v hvint hvp1 R hRfin hRpid
    have hfg : (Subalgebra.toSubmodule R).FG := Module.Finite.iff_fg.1 hRfin
    obtain ⟨T, hT⟩ := Subalgebra.fg_of_fg_toSubmodule hfg
    have hRB : ∀ x ∈ R, x ∈ Algebra.adjoin (O0 p) (T : Set Ω) := by
      intro x hx
      have hle : Algebra.adjoin ℤ_[p] (T : Set Ω) ≤
          (Algebra.adjoin (O0 p) (T : Set Ω)).restrictScalars ℤ_[p] :=
        Algebra.adjoin_le (fun t ht => (Subalgebra.mem_restrictScalars _).2 (Algebra.subset_adjoin ht))
      rw [hT] at hle
      exact (Subalgebra.mem_restrictScalars _).1 (hle hx)
    have hTR : ∀ t ∈ T, t ∈ R := fun t ht => hT ▸ Algebra.subset_adjoin (Finset.mem_coe.2 ht)
    have hTint : ∀ t ∈ T, IsIntegral (O0 p) t := fun t ht =>
      (IsIntegral.of_mem_of_fg R hfg t (hTR t ht)).tower_top
    obtain ⟨hdiv, hres⟩ := NotPow.residue_core p (O0 p) Ω hmax v hv T hTint π (hRB _ hπR) hπ0 hvπ
      (hRB _ hpπ) f hf (fun t ht => hRB _ (hstep t (hTR t ht)))
    have hBint : ∀ x ∈ Algebra.adjoin (O0 p) (T : Set Ω), v x ≤ 1 := fun x hx =>
      (hv x).2 (Algebra.adjoin_le (S := integralClosure (O0 p) Ω) (fun t ht => hTint t ht) hx)
    have hclosed := GlobalTheory.T.div_mem_subalgebra_of_valuation_le_one_of_uniformizer
      (O0 p) Ω v hv _ hBint π (hRB _ hπR) hπ0 hvπ hdiv
    have hsub : Subfield.closure (Set.range (algebraMap (O0 p) Ω) ∪ (S' : Set Ω)) ≤
        Subfield.closure (Algebra.adjoin (O0 p) (T : Set Ω) : Set Ω) := by
      rw [Subfield.closure_le]
      rintro x (⟨c, rfl⟩ | hx)
      · exact Subfield.subset_closure (Subalgebra.algebraMap_mem _ c)
      · obtain ⟨a, ha, b, hb, rfl⟩ := hRS x hx
        exact div_mem (Subfield.subset_closure (hRB _ ha)) (Subfield.subset_closure (hRB _ hb))
    obtain ⟨a, ha, b, hb, hab⟩ := Subfield.mem_closure_iff.1 (hsub hy)
    have hcl : ∀ z ∈ Subring.closure (Algebra.adjoin (O0 p) (T : Set Ω) : Set Ω),
        z ∈ Algebra.adjoin (O0 p) (T : Set Ω) := fun z hz =>
      (Subring.closure_le (t := (Algebra.adjoin (O0 p) (T : Set Ω)).toSubring)).2 (fun _ h => h) hz
    have hyv : v y ≤ 1 := (hv y).2 hyint
    have hyB : y ∈ Algebra.adjoin (O0 p) (T : Set Ω) := by
      rw [← hab]
      exact hclosed a (hcl a ha) b (hcl b hb) (by rw [hab]; exact hyv)
    have hvq : v (y ^ p - algebraMap (O0 p) Ω (qO p)) < 1 := by
      have h1 := (hv _).2 hmint
      rw [map_div₀, map_pow] at h1
      have h2 : v (y ^ p - algebraMap (O0 p) Ω (qO p)) ^ m < 1 :=
        lt_of_le_of_lt ((div_le_one₀ hvp0).1 h1) hvp1
      by_contra hc
      push Not at hc
      exact absurd h2 (not_lt.2 (one_le_pow₀ hc))
    obtain ⟨b, hb⟩ := hres y hyB (qO p) hvq
    have hbv : v (algebraMap (O0 p) Ω b) ≤ 1 := (hv _).2 isIntegral_algebraMap
    have hvb : v (algebraMap (O0 p) Ω (b ^ p - qO p)) < 1 := by
      have e : algebraMap (O0 p) Ω (b ^ p - qO p) = (y ^ p - algebraMap (O0 p) Ω (qO p)) -
          (y ^ p - (algebraMap (O0 p) Ω b) ^ p) := by
        rw [map_sub, map_pow]
        ring
      have hg : v (y ^ p - (algebraMap (O0 p) Ω b) ^ p) < 1 := by
        rw [← geom_sum₂_mul, map_mul]
        have hs : v (∑ i ∈ Finset.range p, y ^ i * (algebraMap (O0 p) Ω b) ^ (p - 1 - i)) ≤ 1 := by
          apply v.map_sum_le
          intro i _
          rw [map_mul, map_pow, map_pow]
          exact mul_le_one' (pow_le_one' hyv _) (pow_le_one' hbv _)
        calc _ ≤ 1 * v (y - algebraMap (O0 p) Ω b) := mul_le_mul_of_nonneg_right hs zero_le
          _ < 1 := by rw [one_mul]; exact hb
      rw [e]
      exact lt_of_le_of_lt (v.map_sub _ _) (max_lt hvq hg)
    apply NotPow.q_not_pow_mod p b
    by_contra hnd
    have hu : IsUnit (b ^ p - qO p) := by
      by_contra hnu
      apply hnd
      have hmem : b ^ p - qO p ∈ IsLocalRing.maximalIdeal (O0 p) :=
        (IsLocalRing.mem_maximalIdeal _).2 hnu
      rw [huni] at hmem
      exact Ideal.mem_span_singleton.1 hmem
    obtain ⟨u, hu⟩ := hu
    have h1 : v (algebraMap (O0 p) Ω (u : O0 p)) * v (algebraMap (O0 p) Ω (↑u⁻¹ : O0 p)) = 1 := by
      rw [← map_mul, ← map_mul, Units.mul_inv, map_one, map_one]
    have h2 : v (algebraMap (O0 p) Ω (↑u⁻¹ : O0 p)) ≤ 1 := (hv _).2 isIntegral_algebraMap
    rw [← hu] at hvb
    have h4 : v (algebraMap (O0 p) Ω (u : O0 p)) * v (algebraMap (O0 p) Ω (↑u⁻¹ : O0 p)) < 1 :=
      calc _ ≤ v (algebraMap (O0 p) Ω (u : O0 p)) * 1 := mul_le_mul_of_nonneg_left h2 zero_le
        _ < 1 := by rw [mul_one]; exact hvb
    rw [h1] at h4
    exact lt_irrefl _ h4
  have mem_rad_iff (x : integralClosure (O0 p) Ω) :
      x ∈ (Ideal.span {(p : integralClosure (O0 p) Ω)}).radical ↔
        ∃ m : ℕ, 0 < m ∧ IsInt (p := p) ((x : Ω) ^ m / (p : Ω)) := by
    constructor
    · rintro ⟨n, hn⟩
      obtain ⟨z, hz⟩ := Ideal.mem_span_singleton'.1 hn
      refine ⟨n + 1, n.succ_pos, ?_⟩
      have h1 : (z : Ω) * p = (x : Ω) ^ n := by exact_mod_cast congrArg Subtype.val hz
      have h2 : (x : Ω) ^ (n + 1) / p = ((z * x : integralClosure (O0 p) Ω) : Ω) := by
        rw [pow_succ, ← h1]; push_cast; field_simp
      rw [h2]
      exact (z * x).2
    · rintro ⟨m, -, hm⟩
      refine ⟨m, Ideal.mem_span_singleton'.2 ⟨⟨_, hm⟩, Subtype.ext ?_⟩⟩
      push_cast
      field_simp
  have isInt_inv (x : Ω)
      (hx : ¬ ∃ m : ℕ, 0 < m ∧ IsInt (p := p) (x ^ m / (p : Ω))) :
      IsInt (p := p) x⁻¹ := by
    apply (hv _).1
    rw [map_inv₀]
    by_contra! hxv
    have hvx : 0 < v x := by
      by_contra hn
      have hz : v x = 0 := le_antisymm (le_of_not_gt hn) zero_le
      simp [hz] at hxv
    obtain ⟨m, hm⟩ := NNReal.exists_pow_lt_of_lt_one hvp0 ((one_lt_inv₀ hvx).mp hxv)
    have hm0 : m ≠ 0 := by
      rintro rfl
      exact (not_lt_of_ge hvp1.le) (by simpa using hm)
    refine hx ⟨m, Nat.pos_of_ne_zero hm0, (hv _).1 ?_⟩
    rw [map_div₀, map_pow, div_le_one₀ hvp0]
    exact hm.le
  set M := (Ideal.span {(p : integralClosure (O0 p) Ω)}).radical with hM
  have hmem : ∀ x : integralClosure (O0 p) Ω, Ideal.Quotient.mk M x = 0 ↔
      ∃ m : ℕ, 0 < m ∧ IsInt (p := p) ((x : Ω) ^ m / (p : Ω)) := fun x => by
    rw [Ideal.Quotient.eq_zero_iff_mem, hM, mem_rad_iff]
  have : M.IsMaximal := ResidueIndep.rad_isMaximal h
  let : Field (integralClosure (O0 p) Ω ⧸ M) := Ideal.Quotient.field M
  have : CharP (integralClosure (O0 p) Ω ⧸ M) p := by
    rw [CharP.charP_iff_prime_eq_zero hp.out, ← map_natCast (Ideal.Quotient.mk M),
      Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.le_radical (Ideal.mem_span_singleton_self _)
  let K : Subfield (integralClosure (O0 p) Ω ⧸ M) :=
    { (E.toSubring.comap (integralClosure (O0 p) Ω).val.toRingHom).map (Ideal.Quotient.mk M) with
      inv_mem' := by
        rintro _ ⟨y, hy, rfl⟩
        by_cases h0 : Ideal.Quotient.mk M y = 0
        · exact ⟨0, E.zero_mem, by rw [h0, inv_zero, map_zero]⟩
        · have h1 : (y : Ω) ≠ 0 := by
            intro hy0
            have : y = 0 := Subtype.ext hy0
            exact h0 (by rw [this, map_zero])
          have h2 := isInt_inv (y : Ω) (fun hh => h0 ((hmem y).2 hh))
          refine ⟨⟨_, h2⟩, E.inv_mem hy, ?_⟩
          refine eq_inv_of_mul_eq_one_left ?_
          rw [← map_mul, ← map_one (Ideal.Quotient.mk M)]
          congr 1
          exact Subtype.ext (inv_mul_cancel₀ h1) }
  have hqi : IsIntegral (O0 p) (T.qq N) :=
    IsIntegral.of_pow (pow_pos hp.out.pos N) (by rw [Basic.qq_pow]; exact isIntegral_algebraMap)
  let t : integralClosure (O0 p) Ω := ⟨_, hqi⟩
  have ht : ((t ^ p ^ N : integralClosure (O0 p) Ω) : Ω) = algebraMap (O0 p) Ω (qO p) := by
    rw [← Basic.qq_pow T N]; rfl
  let d' : ℕ → integralClosure (O0 p) Ω :=
    fun j => if hj : j < p ^ N then ⟨l * c j, hlint j hj⟩ else 0
  have hd' : ∀ j < p ^ N, (d' j : Ω) = l * c j := fun j hj => by simp only [d', dite_eq_left hj]
  have key := ResidueIndep.field_indep p K N (Ideal.Quotient.mk M t)
    ⟨t ^ p ^ N, by
      show ((t ^ p ^ N : integralClosure (O0 p) Ω) : Ω) ∈ E
      rw [ht]; exact hrange ⟨_, rfl⟩, map_pow _ _ _⟩
    (by
      rintro _ ⟨y, hy, rfl⟩ hb
      refine hq y hy y.2 ?_
      rw [← ht]
      have hz : Ideal.Quotient.mk M (y ^ p - t ^ p ^ N) = 0 := by
        rw [RingHom.map_sub, RingHom.map_pow, RingHom.map_pow, hb, sub_self]
      have := (hmem (y ^ p - t ^ p ^ N)).1 hz
      exact this)
    (fun j => Ideal.Quotient.mk M (d' j))
    (fun j hj => ⟨d' j, by
      show (d' j : Ω) ∈ E
      rw [hd' j hj]; exact E.mul_mem hlE (hcE j hj), rfl⟩)
    (by
      have e : ((∑ j ∈ Finset.range (p ^ N), d' j * t ^ j : integralClosure (O0 p) Ω) : Ω) =
          ∑ j ∈ Finset.range (p ^ N), l * c j * T.qq N ^ j := by
        push_cast
        exact Finset.sum_congr rfl fun j hj => by rw [hd' j (Finset.mem_range.1 hj)]
      have := (hmem _).2 (e ▸ hsmall)
      set_option synthInstance.maxHeartbeats 100000 in
        simpa only [map_sum, map_mul, map_pow] using this)
  apply hj0ns
  rw [← hd' j0 hj0]
  exact (hmem _).1 (key j0 hj0)

end GlobalTheory.K5.Orth
