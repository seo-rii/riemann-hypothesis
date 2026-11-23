module

public import Formalism.FlagUnipotentLattices.CardSubmodulesAndLinearEquivBounds

@[expose] public section

open Module Matrix Formalism.HermitianLatticeCounting.LatticeSumBounds
open scoped BigOperators ComplexConjugate

namespace Formalism.HermitianLatticeCounting.P

theorem hyperbolicRatioSqLe : ChShSq := by
  intro sh ch hsh hch hc
  constructor
  · intro h1
    rw [div_pow, div_le_iff₀ (by positivity)]
    linarith [sq_nonneg (ch - 1), mul_le_mul h1 h1 zero_le_one hsh.le]
  · intro h1
    linarith [sq_nonneg (ch - 1), mul_pos hsh (sub_pos.mpr h1)]

theorem prodMaxLeProdMaxDiv : PThreshold := by
  intro ι _ x H hH hx
  have hH0 : 0 < H := by linarith
  rw [← Finset.card_univ, ← Finset.prod_const, ← Finset.prod_mul_distrib]
  apply Finset.prod_le_prod₀
  · intro v _; exact zero_le_one.trans (le_max_left _ _)
  · intro v _
    have e : H * (x v / H) = x v := by field_simp
    rw [mul_max_of_nonneg _ _ hH0.le, mul_one, e]
    exact max_le_max hH le_rfl

private theorem one_le_finset_prod_of_forall_one_le {ι : Type*} (s : Finset ι) (y : ι → ℝ) (h : ∀ v ∈ s, 1 ≤ y v) :
    1 ≤ ∏ v ∈ s, y v := by
  calc (1:ℝ) = ∏ v ∈ s, (1:ℝ) := by simp
    _ ≤ ∏ v ∈ s, y v := Finset.prod_le_prod₀ (fun _ _ => zero_le_one) h

theorem traceLowerBound : TraceLower := by
  intro ι _ a ha hprod
  rcases Nat.eq_zero_or_pos (Fintype.card ι) with hn | hn
  · rw [hn, Nat.cast_zero]; exact Finset.sum_nonneg (fun v _ => ha v)
  · have hn' : (0:ℝ) < Fintype.card ι := by exact_mod_cast hn
    have amgm := Real.geom_mean_le_arith_mean Finset.univ (fun _ => (1:ℝ)) a
      (fun _ _ => zero_le_one) (by simpa using hn') (fun v _ => ha v)
    simp only [Real.rpow_one, one_mul, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
      mul_one] at amgm
    have h1 : 1 ≤ (∏ v, a v) ^ ((Fintype.card ι : ℝ))⁻¹ :=
      Real.one_le_rpow hprod (by positivity)
    have := h1.trans amgm
    rwa [le_div_iff₀ hn', one_mul] at this

lemma one_le_finset_prod_real_of_forall_one_le {ι : Type*} (s : Finset ι) (y : ι → ℝ) (h : ∀ v ∈ s, 1 ≤ y v) :
    1 ≤ ∏ v ∈ s, y v := one_le_finset_prod_of_forall_one_le s y h

private theorem finset_prod_real_mono_of_subset_of_one_le {ι : Type*} (s t : Finset ι) (hst : s ⊆ t) (y : ι → ℝ)
    (h : ∀ v ∈ t, 1 ≤ y v) : ∏ v ∈ s, y v ≤ ∏ v ∈ t, y v := by
  classical
  rw [← Finset.prod_sdiff hst]
  have h1 : 1 ≤ ∏ v ∈ t \ s, y v :=
    one_le_finset_prod_of_forall_one_le _ _ (fun v hv => h v (Finset.mem_sdiff.mp hv).1)
  have h2 : 0 ≤ ∏ v ∈ s, y v :=
    Finset.prod_nonneg (fun v hv => zero_le_one.trans (h v (hst hv)))
  exact le_mul_of_one_le_left h2 h1

lemma finset_prod_le_prod_of_subset_of_one_le {ι : Type*} (s t : Finset ι) (hst : s ⊆ t) (y : ι → ℝ)
    (h : ∀ v ∈ t, 1 ≤ y v) : ∏ v ∈ s, y v ≤ ∏ v ∈ t, y v := finset_prod_real_mono_of_subset_of_one_le s t hst y h

private theorem finset_prod_max_one_nonneg {ι : Type*} (s : Finset ι) (y : ι → ℝ) :
    0 ≤ ∏ v ∈ s, max 1 (y v) :=
  Finset.prod_nonneg (fun _ _ => zero_le_one.trans (le_max_left _ _))

private theorem max_self_inv_le_max_one_mul_max_one_inv {x : ℝ} (hx : 0 < x) :
    max x (1 / x) ≤ max 1 x * max 1 (1 / x) := by
  have h0 : 0 ≤ max 1 (1 / x) := zero_le_one.trans (le_max_left _ _)
  apply max_le
  · calc x ≤ max 1 x := le_max_right _ _
      _ = max 1 x * 1 := (mul_one _).symm
      _ ≤ max 1 x * max 1 (1 / x) := mul_le_mul_of_nonneg_left (le_max_left _ _)
          (zero_le_one.trans (le_max_left _ _))
  · exact (le_max_right 1 (1 / x)).trans (le_mul_of_one_le_left h0 (le_max_left _ _))

theorem prodMaxInvLeSq : LemmaP := by
  intro ι _ x Sg hx hprod
  have hA : ∏ v, max 1 (1 / x v) ≤ ∏ v, max 1 (x v) := by
    have e : ∏ v, max 1 (x v) = (∏ v, x v) * ∏ v, max 1 (1 / x v) := by
      rw [← Finset.prod_mul_distrib]
      apply Finset.prod_congr rfl
      intro v _
      rw [mul_max_of_nonneg _ _ (hx v).le, mul_one, mul_one_div_cancel (hx v).ne']
      exact max_comm _ _
    rw [e]
    exact le_mul_of_one_le_left (finset_prod_max_one_nonneg _ _) hprod
  have hB : ∏ v ∈ Sg, max 1 (1 / x v) ≤ ∏ v, max 1 (1 / x v) :=
    finset_prod_real_mono_of_subset_of_one_le _ _ (Finset.subset_univ _) _ (fun v _ => le_max_left _ _)
  refine ⟨?_, hB.trans hA⟩
  calc ∏ v ∈ Sg, max (x v) (1 / x v) ≤ ∏ v ∈ Sg, (max 1 (x v) * max 1 (1 / x v)) :=
        Finset.prod_le_prod₀ (fun v _ => (hx v).le.trans (le_max_left _ _))
          (fun v _ => max_self_inv_le_max_one_mul_max_one_inv (hx v))
    _ = (∏ v ∈ Sg, max 1 (x v)) * ∏ v ∈ Sg, max 1 (1 / x v) := Finset.prod_mul_distrib
    _ ≤ (∏ v, max 1 (x v)) * ∏ v, max 1 (x v) :=
        mul_le_mul (finset_prod_real_mono_of_subset_of_one_le _ _ (Finset.subset_univ _) _ (fun v _ => le_max_left _ _))
          (hB.trans hA) (finset_prod_max_one_nonneg _ _) (finset_prod_max_one_nonneg _ _)
    _ = (∏ v, max 1 (x v)) ^ 2 := (sq _).symm

theorem hyperbolicRatioLe : ChShBound := by
  intro sh ch hsh hch hc
  have hch2 : ch ≤ sh + 1 := by nlinarith
  rcases le_or_gt 1 sh with h1 | h1
  · calc (1 + ch) / sh ≤ 3 := by rw [div_le_iff₀ hsh]; linarith
      _ ≤ 3 * max 1 (1 / sh) := by have := le_max_left 1 (1 / sh); linarith
  · have hc2 : ch ≤ 2 := by linarith
    calc (1 + ch) / sh ≤ 3 / sh := div_le_div_of_nonneg_right (by linarith) hsh.le
      _ = 3 * (1 / sh) := by ring
      _ ≤ 3 * max 1 (1 / sh) := by have := le_max_right 1 (1 / sh); linarith

theorem hyperbolicPairRatioLe : ChShPair := by
  intro sh₁ ch₁ sh₂ ch₂ h1 hc1 e1 h2 hc2 e2
  have key : ∀ sh ch : ℝ, 0 < sh → 0 ≤ ch → ch ^ 2 = sh ^ 2 + 1 → ch * min 1 sh ≤ 2 * sh := by
    intro sh ch hs hc e
    rcases le_or_gt 1 sh with h | h
    · rw [min_eq_left h, mul_one]; nlinarith
    · rw [min_eq_right h.le]
      have hc2 : ch ≤ 2 := by nlinarith
      exact mul_le_mul_of_nonneg_right hc2 hs.le
  have m1 : 0 < min 1 sh₁ := lt_min one_pos h1
  have m2 : 0 < min 1 sh₂ := lt_min one_pos h2
  have k1 := key sh₁ ch₁ h1 hc1 e1
  have k2 := key sh₂ ch₂ h2 hc2 e2
  have l1 : min 1 sh₁ ≤ sh₁ := min_le_right _ _
  have l2 : min 1 sh₂ ≤ sh₂ := min_le_right _ _
  rw [div_le_iff₀ (mul_pos h1 h2), div_mul_eq_mul_div, le_div_iff₀ (mul_pos m1 m2)]
  linarith [mul_le_mul_of_nonneg_right k1 m2.le, mul_le_mul_of_nonneg_right k2 m1.le,
    mul_le_mul_of_nonneg_left l2 h1.le, mul_le_mul_of_nonneg_left l1 h2.le]

theorem invSqrtPowLeExp : GainSqrt := by
  intro k f b g hk hb hg
  have hk1 : (1:ℝ) ≤ k := by exact_mod_cast hk
  have hkpos : (0:ℝ) < k := by linarith
  have hk4pos : (0:ℝ) < (k:ℝ) ^ 4 := pow_pos hkpos 4
  have h8 : ((k:ℝ) ^ 4) ^ 2 ≤ g := by
    calc ((k:ℝ) ^ 4) ^ 2 = (k:ℝ) ^ 8 := by ring
      _ ≤ ((k:ℝ) * b) ^ 8 := pow_le_pow_left₀ hkpos.le (by nlinarith) 8
      _ ≤ g := hg
  have hk4 : (k:ℝ) ^ 4 ≤ Real.sqrt g := by
    calc (k:ℝ) ^ 4 = Real.sqrt (((k:ℝ) ^ 4) ^ 2) := (Real.sqrt_sq hk4pos.le).symm
      _ ≤ Real.sqrt g := Real.sqrt_le_sqrt h8
  have hinv : (Real.sqrt g)⁻¹ ≤ ((k:ℝ) ^ 4)⁻¹ := inv_anti₀ hk4pos hk4
  have e4 : Real.exp (4 * Real.log k) = (k:ℝ) ^ 4 := by
    rw [show (4:ℝ) * Real.log k = Real.log ((k:ℝ) ^ 4) by rw [Real.log_pow]; norm_num,
      Real.exp_log hk4pos]
  have heq : Real.exp (-4 * ((k:ℝ) * f * Real.log k)) = (((k:ℝ) ^ 4)⁻¹) ^ (k * f) := by
    rw [show -4 * ((k:ℝ) * f * Real.log k) = ((k * f : ℕ) : ℝ) * (-(4 * Real.log k)) by
      push_cast; try ring, Real.exp_nat_mul, Real.exp_neg, e4]
  rw [heq]
  exact pow_le_pow_left₀ (by positivity) hinv _

theorem minBoundSecondZero : MinIIZero := by
  intro k r CT G T T' g v t loss JHS dim hr hk hG hT hT' hg hv ht hloss hdim hCT hkt hVF
  have hk1 : (1:ℝ) ≤ k := by exact_mod_cast hk
  have hk0 : (0:ℝ) < k := by linarith
  have hg0 : 0 < g := by linarith
  have hg' : g ≠ 0 := hg0.ne'
  have hgp : 0 < g ^ (2 * r + 2) := pow_pos hg0 _
  have hkk : (k:ℝ) ≤ (k:ℝ) ^ (3 * r) := by
    calc (k:ℝ) = (k:ℝ) ^ 1 := (pow_one _).symm
      _ ≤ (k:ℝ) ^ (3 * r) := pow_le_pow_right₀ hk1 (by omega)
  have h1 : (k:ℝ) ^ (3 * r) * g ^ (2 * r + 2) ≤ T' * t := by
    calc (k:ℝ) ^ (3 * r) * g ^ (2 * r + 2)
          ≤ (g⁻¹ ^ (2 * r + 2) * T' * t) * g ^ (2 * r + 2) :=
          mul_le_mul_of_nonneg_right hkt hgp.le
      _ = T' * t := by
          rw [show g⁻¹ ^ (2 * r + 2) * T' * t * g ^ (2 * r + 2) =
            (g ^ (2 * r + 2))⁻¹ * g ^ (2 * r + 2) * (T' * t) by ring, inv_mul_cancel₀ hgp.ne', one_mul]
  have hkey : (k:ℝ) * g ^ (2 * r + 2) ≤ T' * t :=
    (mul_le_mul_of_nonneg_right hkk hgp.le).trans h1
  have hCT' : T' ≤ CT * T := by rwa [div_le_iff₀ hT] at hCT
  have htT : 0 < t * T := mul_pos ht hT
  have hbase : (t * T)⁻¹ ≤ CT / (k * g ^ (2 * r + 2)) := by
    rw [le_div_iff₀ (mul_pos hk0 hgp)]
    calc (t * T)⁻¹ * (k * g ^ (2 * r + 2)) ≤ (t * T)⁻¹ * (CT * T * t) :=
          mul_le_mul_of_nonneg_left (by linarith [mul_nonneg ((sub_pos.2 ht).le) (sub_nonneg.2 hCT')]) (inv_nonneg.mpr htT.le)
      _ = CT := by
          rw [show CT * T * t = (t * T) * CT by ring, ← mul_assoc, inv_mul_cancel₀ htT.ne',
            one_mul]
  have hTi : 0 ≤ T⁻¹ ^ k := by positivity
  calc Formalism.HermitianLatticeCounting.LatticeSumBounds.nv k r G T g v * JHS ^ 2 * T⁻¹ ^ k / dim
        = (Formalism.HermitianLatticeCounting.LatticeSumBounds.nv k r G T g v * JHS ^ 2 / dim) * T⁻¹ ^ k := by ring
    _ ≤ (loss * t⁻¹ ^ k) * T⁻¹ ^ k := mul_le_mul_of_nonneg_right hVF hTi
    _ = loss * ((t * T)⁻¹) ^ k := by ring
    _ ≤ loss * (CT / (k * g ^ (2 * r + 2))) ^ k :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hbase k) hloss

theorem massRatioIdentity : XiIdentity := by
  intro mass mj k s hmj hm2 hrec hs hk
  have step : ∀ a n, 2 ≤ a → mass (a + n) = mass a * ∏ i ∈ Finset.Ioc a (a + n), mj i := by
    intro a n ha
    induction n with
    | zero => simp
    | succ n ih =>
      rw [← add_assoc, Finset.prod_Ioc_succ_top (show a ≤ a + n by omega),
        hrec (a + n + 1) (by omega), Nat.add_sub_cancel, ih]
      ring
  have pos : ∀ n, 2 ≤ n → 0 < mass n := by
    intro n hn
    obtain ⟨d, rfl⟩ : ∃ d, n = 2 + d := ⟨n - 2, by omega⟩
    rw [step 2 d le_rfl]
    exact mul_pos hm2 (Finset.prod_pos (fun i _ => hmj i))
  have h1 : mass s = mass 2 * ∏ i ∈ Finset.Ioc 2 s, mj i := by
    obtain ⟨d, rfl⟩ : ∃ d, s = 2 + d := ⟨s - 2, by omega⟩
    exact step 2 d le_rfl
  have h2 : mass k = mass (k - s) * ∏ i ∈ Finset.Ioc (k - s) k, mj i := by
    have := step (k - s) s (by omega)
    rwa [Nat.sub_add_cancel (by omega)] at this
  have hks := pos (k - s) (by omega)
  have hP : 0 < ∏ i ∈ Finset.Ioc (k - s) k, mj i := Finset.prod_pos (fun i _ => hmj i)
  rw [h2, h1, div_eq_div_iff (mul_pos hks hP).ne' hP.ne']
  ring

theorem piPowDivFactorialLt : PiPowFactorial := by
  intro k hk
  have hπ := Real.pi_lt_d2
  have hπ0 := Real.pi_pos
  obtain ⟨n, rfl⟩ : ∃ n, k = n + 2 := ⟨k - 2, by omega⟩
  rw [show n + 2 - 1 = n + 1 by omega, show n + 2 - 2 = n by omega]
  have key : ∀ m : ℕ, (3.15:ℝ) ^ (m + 3 + 1) ≤ 17 * ((m + 3).factorial : ℝ) := by
    intro m
    induction m with
    | zero => norm_num [Nat.factorial]
    | succ m ih =>
      rw [show m + 1 + 3 = (m + 3) + 1 by ring, Nat.factorial_succ, pow_succ]
      push_cast at ih ⊢
      have hf : (0:ℝ) ≤ ((m + 3).factorial : ℝ) := Nat.cast_nonneg _
      linarith [mul_nonneg (Nat.cast_nonneg m : (0:ℝ) ≤ m) hf]
  have bound : (3.15:ℝ) ^ (n + 1) ≤ 17 * (n.factorial : ℝ) := by
    rcases (show n = 1 ∨ n = 2 ∨ 3 ≤ n by omega) with h | h | h
    · subst h; norm_num [Nat.factorial]
    · subst h; norm_num [Nat.factorial]
    · obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
      exact key m
  have hlt : Real.pi ^ (n + 1) < (3.15:ℝ) ^ (n + 1) :=
    pow_lt_pow_left₀ hπ hπ0.le (Nat.succ_ne_zero n)
  rw [div_lt_iff₀ (Nat.cast_pos.mpr (Nat.factorial_pos n))]
  linarith

theorem invFactorialLeStirling : StirlingInv := by
  intro k hk
  have hk0 : (0:ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hst := Stirling.sqrt_pi_le_stirlingSeq (show k ≠ 0 by omega)
  unfold Stirling.stirlingSeq at hst
  have hπ := Real.pi_pos
  have ha0 : 0 < (Real.exp 1 / k) ^ k := by positivity
  have hka : ((k:ℝ) / Real.exp 1) ^ k = ((Real.exp 1 / k) ^ k)⁻¹ := by
    rw [← inv_pow, inv_div]
  rw [hka] at hst
  have hs0 : 0 < Real.sqrt (2 * k) * ((Real.exp 1 / k) ^ k)⁻¹ := by positivity
  rw [le_div_iff₀ hs0] at hst
  have hF : ((k - 1).factorial : ℝ) = (k.factorial : ℝ) / k := by
    obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
    rw [Nat.add_sub_cancel, Nat.factorial_succ, Nat.cast_mul,
      mul_div_cancel_left₀ _ (by positivity : ((m + 1 : ℕ) : ℝ) ≠ 0)]
  rw [hF, one_div, inv_div, div_le_iff₀ (Nat.cast_pos.mpr (Nat.factorial_pos k))]
  have hsq : Real.sqrt (k / (2 * Real.pi)) * (Real.sqrt Real.pi * Real.sqrt (2 * k)) = k := by
    rw [← Real.sqrt_mul hπ.le, ← Real.sqrt_mul (by positivity)]
    rw [show (k:ℝ) / (2 * Real.pi) * (Real.pi * (2 * k)) = (k:ℝ) ^ 2 by
      rw [div_mul_eq_mul_div, div_eq_iff (by positivity)]; ring]
    exact Real.sqrt_sq hk0.le
  calc (k:ℝ) = Real.sqrt (k / (2 * Real.pi)) * (Real.sqrt Real.pi * Real.sqrt (2 * k)) := hsq.symm
    _ = ((Real.exp 1 / k) ^ k * ((Real.exp 1 / k) ^ k)⁻¹) *
          (Real.sqrt (k / (2 * Real.pi)) * (Real.sqrt Real.pi * Real.sqrt (2 * k))) := by
        rw [mul_inv_cancel₀ ha0.ne', one_mul]
    _ = (Real.exp 1 / k) ^ k * Real.sqrt (k / (2 * Real.pi)) *
          (Real.sqrt Real.pi * (Real.sqrt (2 * k) * ((Real.exp 1 / k) ^ k)⁻¹)) := by ring
    _ ≤ (Real.exp 1 / k) ^ k * Real.sqrt (k / (2 * Real.pi)) * (k.factorial : ℝ) :=
        mul_le_mul_of_nonneg_left hst (by positivity)

lemma gainBase_pow (k r : ℕ) (C ν t g : ℝ) (hk : 1 ≤ k) (hC : 0 < C) :
    (xv k r C ν t g) ^ k =
      ν ^ k * t ^ k * (g⁻¹ ^ (2 * r + 2)) ^ k * (C / k) ^ (2 * r * (k - 2 - r)) := by
  have hk0 : (0:ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  unfold Formalism.HermitianLatticeCounting.LatticeSumBounds.xv Formalism.HermitianLatticeCounting.LatticeSumBounds.expo
  rw [mul_pow, mul_pow, mul_pow,
    ← Real.rpow_natCast ((C / (k:ℝ)) ^ (((2 * r * (k - 2 - r) : ℕ) : ℝ) / (k:ℝ))) k,
    ← Real.rpow_mul (by positivity), div_mul_cancel₀ _ hk0.ne', Real.rpow_natCast]

lemma volumeFactor_eq (k r : ℕ) (G T g v : ℝ) :
    nv k r G T g v =
      (Real.exp 1 * Real.pi / (k * v)) ^ k * (G / T) ^ k * (g⁻¹ ^ (2 * r + 2)) ^ k := by
  unfold Formalism.HermitianLatticeCounting.LatticeSumBounds.nv
  rw [← mul_pow, ← mul_pow]
  congr 1
  ring

lemma volumeFactor_mul_sq_div_le (k r : ℕ) (C G T g v Dr loss' JHS Jop dim : ℝ) (hk : 1 ≤ k)
    (hC : 0 < C) (hG : 0 < G) (hT : 0 < T) (hg : 0 < g) (hv : 0 < v) (hDr : 0 < Dr)
    (hdim : 0 < dim) (hJop : 0 ≤ Jop)
    (hABS : Jop ≤ loss' * (C / (k * v)) ^ (r * (k - 2 - r)) * Dr⁻¹ ^ (k - 2 - r))
    (hrank : JHS ^ 2 ≤ dim * Jop ^ 2) :
    nv k r G T g v * JHS ^ 2 / dim ≤
      (Real.exp 1 * Real.pi / (k * v)) ^ k * (G / T) ^ k * (g⁻¹ ^ (2 * r + 2)) ^ k *
        (loss' ^ 2 * (C / (k * v)) ^ (2 * r * (k - 2 - r)) *
          Dr⁻¹ ^ (2 * (k - 2 - r))) := by
  have hVF : 0 ≤ (Real.exp 1 * Real.pi / (k * v)) ^ k * (G / T) ^ k * (g⁻¹ ^ (2 * r + 2)) ^ k := by
    positivity
  have h1 : JHS ^ 2 / dim ≤ Jop ^ 2 := by rw [div_le_iff₀ hdim]; linarith
  have h2 : Jop ^ 2 ≤ (loss' * (C / (k * v)) ^ (r * (k - 2 - r)) * Dr⁻¹ ^ (k - 2 - r)) ^ 2 :=
    pow_le_pow_left₀ hJop hABS 2
  have h3 : (loss' * (C / (k * v)) ^ (r * (k - 2 - r)) * Dr⁻¹ ^ (k - 2 - r)) ^ 2 =
      loss' ^ 2 * (C / (k * v)) ^ (2 * r * (k - 2 - r)) * Dr⁻¹ ^ (2 * (k - 2 - r)) := by ring
  rw [volumeFactor_eq k r G T g v]
  calc _ = (Real.exp 1 * Real.pi / (k * v)) ^ k * (G / T) ^ k * (g⁻¹ ^ (2 * r + 2)) ^ k *
        (JHS ^ 2 / dim) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (h1.trans (h2.trans h3.le)) hVF

theorem minBoundFirst' : MinI' := by
  intro k r C G T g v t Dr loss loss' JHS Jop dim hk hC hG hT hg hv ht hDr hl' hdim hJop hJHS
    hAV hloss hVF hABS hrank
  have hk1 : 1 ≤ k := by omega
  have hkR : (0:ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hlossp : 0 < loss := lt_of_lt_of_le (pow_pos hDr _) hloss
  have hmain := volumeFactor_mul_sq_div_le k r C G T g v Dr loss' JHS Jop dim hk1 hC hG hT hg hv
    hDr hdim hJop hABS hrank
  rcases le_total 1 (Formalism.HermitianLatticeCounting.LatticeSumBounds.xv k r C (G / (T * Dr ^ 2)) t g) with h | h
  · rw [min_eq_left h, one_pow, mul_one]
    calc _ ≤ loss * t⁻¹ ^ k := hVF
      _ = loss * 1 * t⁻¹ ^ k := by ring
      _ ≤ loss * loss' ^ 2 * t⁻¹ ^ k :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (one_le_pow₀ hl') hlossp.le)
            (by positivity)
  · rw [min_eq_right h, gainBase_pow k r C (G / (T * Dr ^ 2)) t g hk1 hC]
    have eG : (G / (T * Dr ^ 2)) ^ k = (G / T) ^ k * Dr⁻¹ ^ (2 * k) := by
      rw [pow_mul Dr⁻¹ 2 k, ← mul_pow]; congr 1; ring
    have et : t⁻¹ ^ k * t ^ k = 1 := by rw [← mul_pow, inv_mul_cancel₀ ht.ne', one_pow]
    rw [eG]
    set s := k - 2 - r with hs
    have hks : 2 * k = 2 * s + (2 * r + 4) := by omega
    have eCv : (C / (k * v)) ^ (2 * r * s) = (C / k) ^ (2 * r * s) * v⁻¹ ^ (2 * r * s) := by
      rw [← mul_pow]; congr 1; ring
    have hone : Dr ^ (2 * r + 4) * Dr⁻¹ ^ (2 * r + 4) = 1 := by
      rw [← mul_pow, mul_inv_cancel₀ hDr.ne', one_pow]
    have eDi : Dr⁻¹ ^ (2 * s) = Dr ^ (2 * r + 4) * Dr⁻¹ ^ (2 * k) := by
      rw [hks, pow_add]
      linear_combination (-(Dr⁻¹ ^ (2 * s))) * hone
    have hZ : 0 ≤ (G / T) ^ k * (g⁻¹ ^ (2 * r + 2)) ^ k * loss' ^ 2 * (C / k) ^ (2 * r * s) *
        Dr⁻¹ ^ (2 * k) := by positivity
    have hAVD : (Real.exp 1 * Real.pi / (k * v)) ^ k * v⁻¹ ^ (2 * r * s) * Dr ^ (2 * r + 4) ≤
        loss := by
      calc _ ≤ 1 * Dr ^ (2 * r + 4) := mul_le_mul_of_nonneg_right hAV (by positivity)
        _ ≤ loss := by rw [one_mul]; exact hloss
    calc _ ≤ _ := hmain
      _ = ((Real.exp 1 * Real.pi / (k * v)) ^ k * v⁻¹ ^ (2 * r * s) * Dr ^ (2 * r + 4)) *
          ((G / T) ^ k * (g⁻¹ ^ (2 * r + 2)) ^ k * loss' ^ 2 * (C / k) ^ (2 * r * s) *
            Dr⁻¹ ^ (2 * k)) := by rw [eCv, eDi]; ring
      _ ≤ loss * ((G / T) ^ k * (g⁻¹ ^ (2 * r + 2)) ^ k * loss' ^ 2 * (C / k) ^ (2 * r * s) *
            Dr⁻¹ ^ (2 * k)) := mul_le_mul_of_nonneg_right hAVD hZ
      _ = loss * loss' ^ 2 * t⁻¹ ^ k * ((G / T) ^ k * Dr⁻¹ ^ (2 * k) * t ^ k *
            (g⁻¹ ^ (2 * r + 2)) ^ k * (C / k) ^ (2 * r * s)) := by
          linear_combination (-(loss * (G / T) ^ k * (g⁻¹ ^ (2 * r + 2)) ^ k * loss' ^ 2 *
            (C / k) ^ (2 * r * s) * Dr⁻¹ ^ (2 * k))) * et

theorem minBoundSecond' : MinII' := by
  intro k r C CT G T T' g v t Dr sh ch loss loss' JHS Jop dim hr hk hC hG hT hT' hg hv ht hDr hl'
    hdim hJop hJHS hAV hloss hsh hch hc hGeq hCT hkt hVF hABS hrank
  have hkR : (0:ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hg0 : 0 < g := by linarith
  have hlossp : 0 < loss := lt_of_lt_of_le (pow_pos hDr _) hloss
  have hCTp : 0 < CT := lt_of_lt_of_le (div_pos hT' hT) hCT
  have heπ : 1 ≤ Real.exp 1 * Real.pi := by
    have := Real.add_one_le_exp 1
    have := Real.pi_gt_three
    nlinarith
  have hratio := hyperbolicRatioSqLe sh ch hsh hch hc
  rcases le_or_gt 1 sh with h1 | h1
  · have hz := minBoundSecondZero k r CT G T T' g v t loss JHS dim hr (by omega) hG hT hT' hg hv ht
      hlossp.le hdim hCT hkt hVF
    have h6 : ((1 + ch) / sh) ^ (2 * k) ≤ 6 ^ k := by
      rw [pow_mul]; exact pow_le_pow_left₀ (by positivity) (hratio.1 h1) k
    calc _ = (Formalism.HermitianLatticeCounting.LatticeSumBounds.nv k r G T g v * JHS ^ 2 * T⁻¹ ^ k / dim) * ((1 + ch) / sh) ^ (2 * k) := by
          ring
      _ ≤ (loss * (CT / (k * g ^ (2 * r + 2))) ^ k) * 6 ^ k :=
          mul_le_mul hz h6 (by positivity) (by positivity)
      _ = loss * (6 * CT / (k * g ^ (2 * r + 2))) ^ k := by ring
      _ ≤ loss * loss' ^ 2 * (6 * Real.exp 1 * Real.pi * CT / (k * g ^ (2 * r + 2))) ^ k := by
          apply mul_le_mul (le_mul_of_one_le_right hlossp.le (one_le_pow₀ hl')) _ (by positivity)
            (by positivity)
          apply pow_le_pow_left₀ (by positivity)
          apply div_le_div_of_nonneg_right _ (by positivity)
          linarith [mul_nonneg ((sub_pos.2 hCTp).le) (sub_nonneg.2 heπ)]
  · have h6 : (1 + ch) ^ 2 ≤ 6 := hratio.2 h1
    obtain ⟨q, hq⟩ : ∃ q, q = 1 + ch := ⟨_, rfl⟩
    rw [← hq] at h6 ⊢
    have hmain := volumeFactor_mul_sq_div_le k r C G T g v Dr loss' JHS Jop dim (by omega) hC hG hT
      hg0 hv hDr hdim hJop hABS hrank
    set s := k - 2 - r with hs
    have hks : 2 * k = 2 * s + (2 * r + 4) := by omega
    have hDD : Dr⁻¹ ^ (2 * s) * Dr ^ (2 * k) = Dr ^ (2 * r + 4) := by
      have hone : Dr⁻¹ ^ (2 * s) * Dr ^ (2 * s) = 1 := by
        rw [← mul_pow, inv_mul_cancel₀ hDr.ne', one_pow]
      rw [hks, pow_add, ← mul_assoc, hone, one_mul]
    have hW : 0 ≤ (q / sh) ^ (2 * k) * T⁻¹ ^ k :=
      mul_nonneg (by rw [pow_mul]; exact pow_nonneg (sq_nonneg _) k) (by positivity)
    have hT0 : T ≠ 0 := hT.ne'
    have hsh0 : sh ≠ 0 := hsh.ne'
    have hv0 : v ≠ 0 := hv.ne'
    have hk0 : (k:ℝ) ≠ 0 := hkR.ne'
    have hg00 : g ≠ 0 := hg0.ne'
    have hDr0 : Dr ≠ 0 := hDr.ne'
    calc _ = (Formalism.HermitianLatticeCounting.LatticeSumBounds.nv k r G T g v * JHS ^ 2 / dim) * ((q / sh) ^ (2 * k) * T⁻¹ ^ k) := by
          ring
      _ ≤ ((Real.exp 1 * Real.pi / (k * v)) ^ k * (G / T) ^ k * (g⁻¹ ^ (2 * r + 2)) ^ k *
            (loss' ^ 2 * (C / (k * v)) ^ (2 * r * s) * Dr⁻¹ ^ (2 * s))) *
            ((q / sh) ^ (2 * k) * T⁻¹ ^ k) := mul_le_mul_of_nonneg_right hmain hW
      _ = (Real.exp 1 * Real.pi / k) ^ k * (g⁻¹ ^ (2 * r + 2)) ^ k * loss' ^ 2 *
            (v⁻¹ ^ k * (C / (k * v)) ^ (2 * r * s)) * (q ^ 2) ^ k * (T' / T) ^ k *
            (Dr⁻¹ ^ (2 * s) * Dr ^ (2 * k)) := by
          have hTk : T ^ k * T⁻¹ ^ k = 1 := by rw [← mul_pow, mul_inv_cancel₀ hT0, one_pow]
          have hsk : sh ^ (2 * k) * sh⁻¹ ^ (2 * k) = 1 := by
            rw [← mul_pow, mul_inv_cancel₀ hsh0, one_pow]
          rw [hGeq]
          linear_combination ((Real.exp 1 * Real.pi / k) ^ k * (g⁻¹ ^ (2 * r + 2)) ^ k * loss' ^ 2 *
            (v⁻¹ ^ k * (C / (k * v)) ^ (2 * r * s)) * (q ^ 2) ^ k * (T' / T) ^ k *
            (Dr⁻¹ ^ (2 * s) * Dr ^ (2 * k)) * (sh ^ (2 * k) * sh⁻¹ ^ (2 * k))) * hTk +
            ((Real.exp 1 * Real.pi / k) ^ k * (g⁻¹ ^ (2 * r + 2)) ^ k * loss' ^ 2 *
            (v⁻¹ ^ k * (C / (k * v)) ^ (2 * r * s)) * (q ^ 2) ^ k * (T' / T) ^ k *
            (Dr⁻¹ ^ (2 * s) * Dr ^ (2 * k))) * hsk
      _ ≤ (Real.exp 1 * Real.pi / k) ^ k * (g⁻¹ ^ (2 * r + 2)) ^ k * loss' ^ 2 * 1 * 6 ^ k *
            CT ^ k * loss := by
          rw [hDD]
          gcongr
          all_goals first | assumption | positivity | skip
      _ = loss * loss' ^ 2 * (6 * Real.exp 1 * Real.pi * CT / (k * g ^ (2 * r + 2))) ^ k := by
          ring

theorem nondegenerateRowBound : NonDegRow := by
  intro k f s g v NT G₁ G₂ Xi W count A₁ A₂ l₁ l₂ τ hk hs hg hv hNT hG₁ hG₂ hXi hW hA₁ hA₂ hτ
    hcount h₁ h₂
  have hkR : (0:ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  unfold Formalism.HermitianLatticeCounting.LatticeSumBounds.nTot at h₁ h₂
  obtain ⟨E, hE⟩ : ∃ E, E = (Real.exp 1 * Real.pi / (k * v)) ^ (k * f) := ⟨_, rfl⟩
  have hE0 : 0 < E := by rw [hE]; positivity
  have hE' : E ≠ 0 := hE0.ne'
  rw [← hE] at h₁ h₂
  obtain ⟨a, ha⟩ : ∃ x, x = Real.sqrt (G₁ / NT) := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ x, x = Real.sqrt (G₂ / NT) := ⟨_, rfl⟩
  have ha0 : 0 ≤ a := by rw [ha]; positivity
  have hb0 : 0 ≤ b := by rw [hb]; positivity
  have ha2 : a ^ 2 = G₁ / NT := by rw [ha, Real.sq_sqrt (by positivity)]
  have hb2 : b ^ 2 = G₂ / NT := by rw [hb, Real.sq_sqrt (by positivity)]
  have hab : Real.sqrt (G₁ * G₂) / NT = a * b := by
    rw [ha, hb, ← Real.sqrt_mul (div_nonneg hG₁.le hNT.le),
      show G₁ / NT * (G₂ / NT) = (G₁ * G₂) / NT ^ 2 by ring,
      Real.sqrt_div (mul_nonneg hG₁.le hG₂.le), Real.sqrt_sq hNT.le]
  obtain ⟨u₁, hu₁⟩ : ∃ x, x = A₁ * a ^ k := ⟨_, rfl⟩
  obtain ⟨u₂, hu₂⟩ : ∃ x, x = A₂ * b ^ k := ⟨_, rfl⟩
  have hu₁0 : 0 ≤ u₁ := by rw [hu₁]; positivity
  have hu₂0 : 0 ≤ u₂ := by rw [hu₂]; positivity
  have hl1 : E * u₁ ^ 2 ≤ l₁ * τ := by
    have e : E * u₁ ^ 2 = E * (G₁ / NT) ^ k * A₁ ^ 2 := by rw [hu₁, ← ha2]; ring
    rw [e]; exact h₁
  have hl2 : E * u₂ ^ 2 ≤ l₂ * τ := by
    have e : E * u₂ ^ 2 = E * (G₂ / NT) ^ k * A₂ ^ 2 := by rw [hu₂, ← hb2]; ring
    rw [e]; exact h₂
  have hkey : E * (u₁ * u₂) ≤ Real.sqrt (l₁ * l₂) * τ := by
    have hprod : (E * (u₁ * u₂)) ^ 2 ≤ (l₁ * τ) * (l₂ * τ) := by
      have e : (E * (u₁ * u₂)) ^ 2 = (E * u₁ ^ 2) * (E * u₂ ^ 2) := by ring
      rw [e]
      exact mul_le_mul hl1 hl2 (by positivity) (le_trans (by positivity) hl1)
    have h0 : 0 ≤ E * (u₁ * u₂) := by positivity
    calc E * (u₁ * u₂) = Real.sqrt ((E * (u₁ * u₂)) ^ 2) := (Real.sqrt_sq h0).symm
      _ ≤ Real.sqrt ((l₁ * τ) * (l₂ * τ)) := Real.sqrt_le_sqrt hprod
      _ = Real.sqrt (l₁ * l₂ * τ ^ 2) := by congr 1; ring
      _ = Real.sqrt (l₁ * l₂) * τ := by rw [Real.sqrt_mul' _ (sq_nonneg τ), Real.sqrt_sq hτ]
  have hid : ((2 / g) ^ ((s - 1) * f) * Real.sqrt (G₁ * G₂) / NT) ^ k * Xi * W * (A₁ * A₂) =
      (2 / g) ^ ((s - 1) * k * f) * Xi * W * (u₁ * u₂) := by
    rw [mul_div_assoc, hab, hu₁, hu₂]; ring
  have hAA : 0 ≤ A₁ * A₂ := mul_nonneg hA₁ hA₂
  calc count * A₁ * A₂ = count * (A₁ * A₂) := by ring
    _ ≤ (((2 / g) ^ ((s - 1) * f) * Real.sqrt (G₁ * G₂) / NT) ^ k * Xi * W) * (A₁ * A₂) :=
        mul_le_mul_of_nonneg_right hcount hAA
    _ = (2 / g) ^ ((s - 1) * k * f) * Xi * W * (u₁ * u₂) := hid
    _ = (2 / g) ^ ((s - 1) * k * f) * Xi * W * E⁻¹ * (E * (u₁ * u₂)) := by
        rw [mul_assoc _ E⁻¹, inv_mul_cancel_left₀ hE']
    _ ≤ (2 / g) ^ ((s - 1) * k * f) * Xi * W * E⁻¹ * (Real.sqrt (l₁ * l₂) * τ) :=
        mul_le_mul_of_nonneg_left hkey (by positivity)
    _ = (2 / g) ^ ((s - 1) * k * f) * (k * v / (Real.exp 1 * Real.pi)) ^ (k * f) *
          Xi * W * Real.sqrt (l₁ * l₂) * τ := by
        rw [hE, ← inv_pow, inv_div]; ring

theorem degenerateRowBound : DegRow := by
  intro k f s g v T NT G₁ G₂ K₁ K₂ Xi W count A₁ A₂ lam₁ lam₂ hk hs hg hv hT hNT hG₁ hG₂ hK₁ hK₂
    hXi hW hA₁ hA₂ hcount h₁ h₂
  have hkR : (0:ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  unfold Formalism.HermitianLatticeCounting.LatticeSumBounds.nTot at h₁ h₂
  obtain ⟨E, hE⟩ : ∃ E, E = (Real.exp 1 * Real.pi / (k * v)) ^ (k * f) := ⟨_, rfl⟩
  have hE0 : 0 < E := by rw [hE]; positivity
  have hE' : E ≠ 0 := hE0.ne'
  rw [← hE] at h₁ h₂
  obtain ⟨a, ha⟩ : ∃ x, x = Real.sqrt (G₁ / NT) := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ x, x = Real.sqrt (G₂ / NT) := ⟨_, rfl⟩
  obtain ⟨c, hc⟩ : ∃ x, x = Real.sqrt T⁻¹ := ⟨_, rfl⟩
  have ha0 : 0 ≤ a := by rw [ha]; positivity
  have hb0 : 0 ≤ b := by rw [hb]; positivity
  have hc0 : 0 ≤ c := by rw [hc]; positivity
  have ha2 : a ^ 2 = G₁ / NT := by rw [ha, Real.sq_sqrt (by positivity)]
  have hb2 : b ^ 2 = G₂ / NT := by rw [hb, Real.sq_sqrt (by positivity)]
  have hc2 : c ^ 2 = T⁻¹ := by rw [hc, Real.sq_sqrt (by positivity)]
  have hab : Real.sqrt (G₁ * G₂) / NT = a * b := by
    rw [ha, hb, ← Real.sqrt_mul (div_nonneg hG₁.le hNT.le),
      show G₁ / NT * (G₂ / NT) = (G₁ * G₂) / NT ^ 2 by ring,
      Real.sqrt_div (mul_nonneg hG₁.le hG₂.le), Real.sqrt_sq hNT.le]
  obtain ⟨u₁, hu₁⟩ : ∃ x, x = A₁ * a ^ k * K₁ ^ k * c ^ (k * f) := ⟨_, rfl⟩
  obtain ⟨u₂, hu₂⟩ : ∃ x, x = A₂ * b ^ k * K₂ ^ k * c ^ (k * f) := ⟨_, rfl⟩
  have hu₁0 : 0 ≤ u₁ := by rw [hu₁]; positivity
  have hu₂0 : 0 ≤ u₂ := by rw [hu₂]; positivity
  have hl1 : E * u₁ ^ 2 ≤ lam₁ := by
    have e : E * u₁ ^ 2 = E * (G₁ / NT) ^ k * A₁ ^ 2 * K₁ ^ (2 * k) * T⁻¹ ^ (k * f) := by
      rw [hu₁, ← ha2, ← hc2]; ring
    rw [e]; exact h₁
  have hl2 : E * u₂ ^ 2 ≤ lam₂ := by
    have e : E * u₂ ^ 2 = E * (G₂ / NT) ^ k * A₂ ^ 2 * K₂ ^ (2 * k) * T⁻¹ ^ (k * f) := by
      rw [hu₂, ← hb2, ← hc2]; ring
    rw [e]; exact h₂
  have hkey : E * (u₁ * u₂) ≤ Real.sqrt (lam₁ * lam₂) := by
    have hprod : (E * (u₁ * u₂)) ^ 2 ≤ lam₁ * lam₂ := by
      have e : (E * (u₁ * u₂)) ^ 2 = (E * u₁ ^ 2) * (E * u₂ ^ 2) := by ring
      rw [e]
      exact mul_le_mul hl1 hl2 (by positivity) (le_trans (by positivity) hl1)
    have h0 : 0 ≤ E * (u₁ * u₂) := by positivity
    calc E * (u₁ * u₂) = Real.sqrt ((E * (u₁ * u₂)) ^ 2) := (Real.sqrt_sq h0).symm
      _ ≤ Real.sqrt (lam₁ * lam₂) := Real.sqrt_le_sqrt hprod
  have hid : ((2 / g) ^ ((s - 2) * f) * Real.sqrt (G₁ * G₂) * T⁻¹ ^ f * K₁ * K₂ / NT) ^ k * Xi * W *
      (A₁ * A₂) = (2 / g) ^ ((s - 2) * k * f) * Xi * W * (u₁ * u₂) := by
    rw [show (2 / g) ^ ((s - 2) * f) * Real.sqrt (G₁ * G₂) * T⁻¹ ^ f * K₁ * K₂ / NT =
        (2 / g) ^ ((s - 2) * f) * (Real.sqrt (G₁ * G₂) / NT) * T⁻¹ ^ f * K₁ * K₂ by ring,
      hab, ← hc2, hu₁, hu₂]
    ring
  have hAA : 0 ≤ A₁ * A₂ := mul_nonneg hA₁ hA₂
  calc count * A₁ * A₂ = count * (A₁ * A₂) := by ring
    _ ≤ (((2 / g) ^ ((s - 2) * f) * Real.sqrt (G₁ * G₂) * T⁻¹ ^ f * K₁ * K₂ / NT) ^ k * Xi * W) *
          (A₁ * A₂) := mul_le_mul_of_nonneg_right hcount hAA
    _ = (2 / g) ^ ((s - 2) * k * f) * Xi * W * (u₁ * u₂) := hid
    _ = (2 / g) ^ ((s - 2) * k * f) * Xi * W * E⁻¹ * (E * (u₁ * u₂)) := by
        rw [mul_assoc _ E⁻¹, inv_mul_cancel_left₀ hE']
    _ ≤ (2 / g) ^ ((s - 2) * k * f) * Xi * W * E⁻¹ * Real.sqrt (lam₁ * lam₂) :=
        mul_le_mul_of_nonneg_left hkey (by positivity)
    _ = (2 / g) ^ ((s - 2) * k * f) * (k * v / (Real.exp 1 * Real.pi)) ^ (k * f) *
          Xi * W * Real.sqrt (lam₁ * lam₂) := by
        rw [hE, ← inv_pow, inv_div]; ring

theorem prodMinLeOfProdRatio : SmallTerm := by
  intro ι _ sh₁ ch₁ sh₂ ch₂ T T' g hT hT' hg h₁ h₂ hprod
  have hmin : ∀ x : ℝ, 0 < x → min (T' * x ^ 2) T' = T' * (min 1 x) ^ 2 := by
    intro x hx
    rcases le_total x 1 with h | h
    · have hx2 : x ^ 2 ≤ 1 := by linarith [mul_nonneg ((sub_pos.2 hx).le) (sub_nonneg.2 h)]
      rw [min_eq_right h, min_eq_left (mul_le_of_le_one_right hT'.le hx2)]
    · have hx2 : 1 ≤ x ^ 2 := by linarith [mul_nonneg ((sub_pos.2 hx).le) (sub_nonneg.2 h)]
      rw [min_eq_left h, min_eq_right (le_mul_of_one_le_right hT'.le hx2), one_pow, mul_one]
  have hm₁ : ∀ v, 0 < min 1 (sh₁ v) := fun v => lt_min one_pos (h₁ v).1
  have hm₂ : ∀ v, 0 < min 1 (sh₂ v) := fun v => lt_min one_pos (h₂ v).1
  have hPm : 0 < ∏ v, (min 1 (sh₁ v) * min 1 (sh₂ v)) :=
    Finset.prod_pos (fun v _ => mul_pos (hm₁ v) (hm₂ v))
  have hbound : Real.sqrt (T * T' / g ^ 2) ^ Fintype.card ι ≤
      4 ^ Fintype.card ι / ∏ v, (min 1 (sh₁ v) * min 1 (sh₂ v)) := by
    refine hprod.trans ?_
    calc ∏ v, (ch₁ v + ch₂ v) / (sh₁ v * sh₂ v)
          ≤ ∏ v, (4 / (min 1 (sh₁ v) * min 1 (sh₂ v))) :=
          Finset.prod_le_prod₀
            (fun v _ => div_nonneg (add_nonneg (h₁ v).2.1 (h₂ v).2.1)
              (mul_pos (h₁ v).1 (h₂ v).1).le)
            (fun v _ => hyperbolicPairRatioLe _ _ _ _ (h₁ v).1 (h₁ v).2.1 (h₁ v).2.2
              (h₂ v).1 (h₂ v).2.1 (h₂ v).2.2)
      _ = 4 ^ Fintype.card ι / ∏ v, (min 1 (sh₁ v) * min 1 (sh₂ v)) := by
          rw [Finset.prod_div_distrib, Finset.prod_const, Finset.card_univ]
  have hsq : Real.sqrt (T * T' / g ^ 2) ^ 2 = T * T' / g ^ 2 := Real.sq_sqrt (by positivity)
  have hk1 : (∏ v, (min 1 (sh₁ v) * min 1 (sh₂ v))) * Real.sqrt (T * T' / g ^ 2) ^ Fintype.card ι ≤
      4 ^ Fintype.card ι := by
    rw [le_div_iff₀ hPm] at hbound; linarith
  have hk2 : (∏ v, (min 1 (sh₁ v) * min 1 (sh₂ v))) ^ 2 * (T * T' / g ^ 2) ^ Fintype.card ι ≤
      16 ^ Fintype.card ι := by
    have h0 : 0 ≤ (∏ v, (min 1 (sh₁ v) * min 1 (sh₂ v))) *
        Real.sqrt (T * T' / g ^ 2) ^ Fintype.card ι := by positivity
    have := pow_le_pow_left₀ h0 hk1 2
    calc (∏ v, (min 1 (sh₁ v) * min 1 (sh₂ v))) ^ 2 * (T * T' / g ^ 2) ^ Fintype.card ι
          = ((∏ v, (min 1 (sh₁ v) * min 1 (sh₂ v))) *
              Real.sqrt (T * T' / g ^ 2) ^ Fintype.card ι) ^ 2 := by
          rw [mul_pow, ← pow_mul, mul_comm (Fintype.card ι) 2, pow_mul, hsq]
      _ ≤ (4 ^ Fintype.card ι) ^ 2 := this
      _ = 16 ^ Fintype.card ι := by
          rw [← pow_mul, mul_comm (Fintype.card ι) 2, pow_mul]; norm_num
  have hsq2 : Real.sqrt (T' / T) ^ 2 = T' / T := Real.sq_sqrt (by positivity)
  have hab : (∏ v, min (T' * sh₁ v ^ 2) T') * (∏ v, min (T' * sh₂ v ^ 2) T') ≤
      ((4 * Real.sqrt (T' / T) * g) ^ Fintype.card ι) ^ 2 := by
    rw [← Finset.prod_mul_distrib]
    have e : ∀ v, min (T' * sh₁ v ^ 2) T' * min (T' * sh₂ v ^ 2) T' =
        T' ^ 2 * (min 1 (sh₁ v) * min 1 (sh₂ v)) ^ 2 := by
      intro v; rw [hmin _ (h₁ v).1, hmin _ (h₂ v).1]; ring
    simp only [e]
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Finset.prod_pow]
    have hc : T * T' / g ^ 2 * (T' / T * g ^ 2) = T' ^ 2 := by
      first | (field_simp; ring) | field_simp
    calc (T' ^ 2) ^ Fintype.card ι * (∏ v, (min 1 (sh₁ v) * min 1 (sh₂ v))) ^ 2
          = ((∏ v, (min 1 (sh₁ v) * min 1 (sh₂ v))) ^ 2 * (T * T' / g ^ 2) ^ Fintype.card ι) *
            (T' / T * g ^ 2) ^ Fintype.card ι := by
          rw [mul_assoc, ← mul_pow, hc]; ring
      _ ≤ 16 ^ Fintype.card ι * (T' / T * g ^ 2) ^ Fintype.card ι :=
          mul_le_mul_of_nonneg_right hk2 (by positivity)
      _ = ((4 * Real.sqrt (T' / T) * g) ^ Fintype.card ι) ^ 2 := by
          rw [← mul_pow, ← pow_mul, mul_comm (Fintype.card ι) 2, pow_mul]
          congr 1
          rw [mul_pow, mul_pow, hsq2]; ring
  by_contra hcon
  push_neg at hcon
  obtain ⟨ha, hb⟩ := hcon
  have hc0 : 0 ≤ (4 * Real.sqrt (T' / T) * g) ^ Fintype.card ι := by positivity
  have := mul_lt_mul'' ha hb hc0 hc0
  linarith

theorem adjugateLastColumnEqCofactor : CofVecAdjugate := by
  intro R _ r Z b
  rw [Matrix.adjugate_fin_succ_eq_det_submatrix, Fin.succAbove_last]
  unfold Formalism.HermitianLatticeCounting.LatticeSumBounds.cofVec
  rw [Fin.val_last, pow_add]
  simp only [Matrix.submatrix_submatrix, Function.comp_id, Function.id_comp]
  ring

theorem expSumLe' : ExpSumLe' := by
  intro A x hA hx
  have h3A : 0 < 3 * A := by linarith
  have hlog : 0 ≤ Real.log (3 * A) := Real.log_nonneg (by linarith)
  have hE : Real.exp (-x / 6) * Real.exp (x / 6) = 1 := by
    rw [← Real.exp_add, show -x / 6 + x / 6 = (0:ℝ) by ring, Real.exp_zero]
  have h3 : 3 * A ≤ Real.exp (x / 6) := by
    calc 3 * A = Real.exp (Real.log (3 * A)) := (Real.exp_log h3A).symm
      _ ≤ Real.exp (x / 6) := Real.exp_le_exp.mpr (by linarith)
  have hpos := Real.exp_pos (-x / 6)
  have hA' : 3 * A * Real.exp (-x / 6) ≤ 1 := by linarith [mul_nonneg (by linarith : (0 : ℝ) ≤ Real.exp (x / 6) - 3 * A) (by linarith : (0 : ℝ) ≤ Real.exp (-x / 6))]
  have hsplit : Real.exp (-x / 2) = Real.exp (-x / 3) * Real.exp (-x / 6) := by
    rw [← Real.exp_add]; congr 1; ring
  have t1 : Real.exp (-4 * x) ≤ Real.exp (-x / 2) := Real.exp_le_exp.mpr (by linarith)
  have t2 : Real.exp (-x) ≤ Real.exp (-x / 2) := Real.exp_le_exp.mpr (by linarith)
  have hp3 := Real.exp_pos (-x / 3)
  have hs : Real.exp (-4 * x) + Real.exp (-x / 2) + Real.exp (-x) ≤ 3 * Real.exp (-x / 2) := by
    linarith
  calc A * (Real.exp (-4 * x) + Real.exp (-x / 2) + Real.exp (-x))
        ≤ A * (3 * Real.exp (-x / 2)) := mul_le_mul_of_nonneg_left hs (by linarith)
    _ = Real.exp (-x / 3) * (3 * A * Real.exp (-x / 6)) := by rw [hsplit]; ring
    _ ≤ Real.exp (-x / 3) * 1 := mul_le_mul_of_nonneg_left hA' hp3.le
    _ = Real.exp (-x / 3) := mul_one _

theorem maxInvSinhSqLe : ShInvPlace := by
  intro sh G T T' Dr hsh hG hDr hTT hGeq
  have hTT0 : 0 < T * T' := by linarith
  have hsh0 : sh ≠ 0 := hsh.ne'
  have hDr0 : Dr ≠ 0 := hDr.ne'
  have hT0 : T * T' ≠ 0 := hTT0.ne'
  apply max_le
  · exact one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hTT (le_max_left _ _))
      (le_max_left _ _)
  · have e : 1 / sh ^ 2 = T * T' * Dr ^ 2 * (1 / G) := by
      rw [hGeq, mul_one_div, div_eq_div_iff (by positivity) (by rw [← hGeq]; exact hG.ne')]
      ring
    rw [e]
    exact mul_le_mul (mul_le_mul_of_nonneg_left (le_max_right _ _) hTT0.le) (le_max_right _ _)
      (by positivity) (by positivity)

theorem prodVolumeFactor : NProduct := by
  intro ι _ k r G vt T g v hk hT hg hvt hprod
  unfold Formalism.HermitianLatticeCounting.LatticeSumBounds.nv
  rw [Finset.prod_pow]
  have e : ∏ w, (Real.exp 1 * Real.pi * G w * g⁻¹ ^ (2 * r + 2) / (T * k * vt w)) =
      (Real.exp 1 * Real.pi * g⁻¹ ^ (2 * r + 2) / (T * k)) ^ Fintype.card ι * (∏ w, G w) /
        ∏ w, vt w := by
    rw [← Finset.card_univ, ← Finset.prod_const, ← Finset.prod_mul_distrib,
      ← Finset.prod_div_distrib]
    apply Finset.prod_congr rfl
    intro w _
    ring
  rw [e, hprod, mul_comm k (Fintype.card ι), pow_mul, ← mul_pow]
  congr 1
  ring

theorem nondegenerateFactorBound : DeNonDegBound := by
  intro f s g G₁ G₂ HH₁ HH₂ hg hG₁ hG₂ h₁ h₂ hH₁ hH₂
  have hH : 1 ≤ HH₁ * HH₂ := one_le_mul_of_one_le_of_one_le hH₁ hH₂
  have hq : (2 / g) ^ ((s - 1) * f) ≤ 1 :=
    pow_le_one₀ (by positivity) (by rw [div_le_one (by linarith)]; exact hg)
  have hsq : Real.sqrt (G₁ * G₂) ≤ HH₁ * HH₂ := by
    calc Real.sqrt (G₁ * G₂) ≤ Real.sqrt (HH₁ * HH₂) :=
          Real.sqrt_le_sqrt (mul_le_mul h₁ h₂ hG₂ (by linarith))
      _ ≤ Real.sqrt ((HH₁ * HH₂) ^ 2) := Real.sqrt_le_sqrt (by linarith [mul_nonneg (sub_nonneg.2 hG₁) (sub_nonneg.2 hH₂), mul_nonneg (sub_nonneg.2 h₁) (sub_nonneg.2 hH₂), mul_nonneg (sub_nonneg.2 hH) (sub_nonneg.2 hH)])
      _ = HH₁ * HH₂ := Real.sqrt_sq (by linarith)
  have h1 : (2 / g) ^ ((s - 1) * f) * Real.sqrt (G₁ * G₂) ≤ HH₁ * HH₂ := by
    calc (2 / g) ^ ((s - 1) * f) * Real.sqrt (G₁ * G₂) ≤ 1 * (HH₁ * HH₂) :=
          mul_le_mul hq hsq (Real.sqrt_nonneg _) zero_le_one
      _ = HH₁ * HH₂ := one_mul _
  refine ⟨h1, h1.trans ?_⟩
  calc HH₁ * HH₂ = (HH₁ * HH₂) ^ 1 := (pow_one _).symm
    _ ≤ (HH₁ * HH₂) ^ 3 := pow_le_pow_right₀ hH (by norm_num)

theorem degenerateFactorBound : DeDegBound := by
  intro f s g T G₁ G₂ K₁ K₂ HH₁ HH₂ hg hT hG₁ hG₂ h₁ h₂ hK₁ hK₂ hk₁ hk₂ h9
  have hH₁ : 0 ≤ HH₁ := hG₁.trans h₁
  have hH₂ : 0 ≤ HH₂ := hG₂.trans h₂
  have hq : (2 / g) ^ ((s - 2) * f) ≤ 1 :=
    pow_le_one₀ (by positivity) (by rw [div_le_one (by linarith)]; exact hg)
  have hTi : T⁻¹ ≤ 1 := by have := inv_anti₀ one_pos hT; simpa using this
  have hTf : T⁻¹ ^ f ≤ 1 := pow_le_one₀ (by positivity) hTi
  have hY0 : 0 ≤ Real.sqrt (G₁ * G₂) * K₁ * K₂ := by positivity
  have hY : Real.sqrt (G₁ * G₂) * K₁ * K₂ ≤ (HH₁ * HH₂) ^ 3 := by
    have hsq : (Real.sqrt (G₁ * G₂) * K₁ * K₂) ^ 2 ≤ ((HH₁ * HH₂) ^ 3) ^ 2 := by
      have e : (Real.sqrt (G₁ * G₂) * K₁ * K₂) ^ 2 = (G₁ * G₂) * (K₁ ^ 2 * K₂ ^ 2) := by
        rw [mul_pow, mul_pow, Real.sq_sqrt (mul_nonneg hG₁ hG₂)]; ring
      rw [e]
      calc (G₁ * G₂) * (K₁ ^ 2 * K₂ ^ 2)
            ≤ (HH₁ * HH₂) * ((9 ^ f * HH₁ ^ 3) * (9 ^ f * HH₂ ^ 3)) :=
            mul_le_mul (mul_le_mul h₁ h₂ hG₂ hH₁) (mul_le_mul hk₁ hk₂ (by positivity) (by positivity))
              (by positivity) (by positivity)
        _ = (9 ^ f) ^ 2 * (HH₁ * HH₂) ^ 4 := by ring
        _ ≤ (HH₁ * HH₂) ^ 2 * (HH₁ * HH₂) ^ 4 :=
            mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) h9 2) (by positivity)
        _ = ((HH₁ * HH₂) ^ 3) ^ 2 := by ring
    calc Real.sqrt (G₁ * G₂) * K₁ * K₂ = Real.sqrt ((Real.sqrt (G₁ * G₂) * K₁ * K₂) ^ 2) :=
          (Real.sqrt_sq hY0).symm
      _ ≤ Real.sqrt (((HH₁ * HH₂) ^ 3) ^ 2) := Real.sqrt_le_sqrt hsq
      _ = (HH₁ * HH₂) ^ 3 := Real.sqrt_sq (by positivity)
  calc (2 / g) ^ ((s - 2) * f) * Real.sqrt (G₁ * G₂) * T⁻¹ ^ f * K₁ * K₂
        = ((2 / g) ^ ((s - 2) * f) * T⁻¹ ^ f) * (Real.sqrt (G₁ * G₂) * K₁ * K₂) := by ring
    _ ≤ (1 * 1) * (HH₁ * HH₂) ^ 3 :=
        mul_le_mul (mul_le_mul hq hTf (by positivity) zero_le_one) hY hY0 (by norm_num)
    _ = (HH₁ * HH₂) ^ 3 := by ring

theorem prodHyperbolicRatioSqLe : DegFactorBound := by
  intro ι _ sh ch G Dr T T' HH hTT hsc hG hDr hGeq hHH1 hHH2 hHH3
  have hTT0 : 0 ≤ T * T' := by linarith
  have hHH0 : 0 ≤ HH := le_trans (pow_nonneg hTT0 _) hHH1
  have hper : ∀ v, ((1 + ch v) / sh v) ^ 2 ≤
      9 * (T * T' * max 1 (Dr v ^ 2) * max 1 (1 / G v)) := by
    intro v
    obtain ⟨hs, hc, he⟩ := hsc v
    have h1 := hyperbolicRatioLe (sh v) (ch v) hs hc he
    have h0 : 0 ≤ (1 + ch v) / sh v := by positivity
    have h2 : ((1 + ch v) / sh v) ^ 2 ≤ (3 * max 1 (1 / sh v)) ^ 2 := pow_le_pow_left₀ h0 h1 2
    have h3 : max 1 (1 / sh v) ^ 2 ≤ max 1 (1 / sh v ^ 2) := by
      rcases le_total (1 / sh v) 1 with h | h
      · rw [max_eq_left h, one_pow]; exact le_max_left _ _
      · rw [max_eq_right h, div_pow, one_pow]; exact le_max_right _ _
    have h4 := maxInvSinhSqLe (sh v) (G v) T T' (Dr v) hs (hG v) (hDr v) hTT (hGeq v)
    calc ((1 + ch v) / sh v) ^ 2 ≤ (3 * max 1 (1 / sh v)) ^ 2 := h2
      _ = 9 * max 1 (1 / sh v) ^ 2 := by ring
      _ ≤ 9 * (T * T' * max 1 (Dr v ^ 2) * max 1 (1 / G v)) := by linarith
  rw [← Finset.prod_pow]
  calc ∏ v, ((1 + ch v) / sh v) ^ 2
        ≤ ∏ v, (9 * (T * T' * max 1 (Dr v ^ 2) * max 1 (1 / G v))) :=
        Finset.prod_le_prod₀ (fun v _ => sq_nonneg _) (fun v _ => hper v)
    _ = 9 ^ Fintype.card ι * ((T * T') ^ Fintype.card ι * (∏ v, max 1 (Dr v ^ 2)) *
          ∏ v, max 1 (1 / G v)) := by
        rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_mul_distrib,
          Finset.prod_const, Finset.prod_const, Finset.card_univ]
    _ ≤ 9 ^ Fintype.card ι * (HH * HH * HH) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact mul_le_mul (mul_le_mul hHH1 hHH2 (finset_prod_max_one_nonneg _ _) hHH0) hHH3
          (finset_prod_max_one_nonneg _ _) (mul_nonneg hHH0 hHH0)
    _ = 9 ^ Fintype.card ι * HH ^ 3 := by ring

lemma summable_one_div_add_one_pow (j : ℕ) (hj : 2 ≤ j) : Summable (fun n : ℕ => 1 / ((n : ℝ) + 1) ^ j) := by
  have h := Real.summable_one_div_nat_pow.mpr (show 1 < j by omega)
  have h1 := (summable_nat_add_iff 1).mpr h
  exact h1.congr (fun n => by simp)

lemma summable_one_div_add_two_pow (j : ℕ) (hj : 2 ≤ j) : Summable (fun n : ℕ => 1 / ((n : ℝ) + 2) ^ j) := by
  have h := Real.summable_one_div_nat_pow.mpr (show 1 < j by omega)
  have h1 := (summable_nat_add_iff 2).mpr h
  exact h1.congr (fun n => by simp)

lemma zetaSeries_eq_one_add_tsum (j : ℕ) (hj : 2 ≤ j) : zetaR j = 1 + ∑' n : ℕ, 1 / ((n : ℝ) + 2) ^ j := by
  have h1 := (hasSum_nat_add_iff' 1).mpr (summable_one_div_add_one_pow j hj).hasSum
  have h2 : HasSum (fun n : ℕ => 1 / ((n : ℝ) + 2) ^ j) (Formalism.HermitianLatticeCounting.LatticeSumBounds.zetaR j - 1) := by
    unfold Formalism.HermitianLatticeCounting.LatticeSumBounds.zetaR
    simpa [add_assoc, one_add_one_eq_two] using h1
  rw [h2.tsum_eq]; ring

lemma tsum_one_div_add_two_sq : ∑' n : ℕ, 1 / ((n : ℝ) + 2) ^ 2 = Real.pi ^ 2 / 6 - 1 := by
  have h := (hasSum_nat_add_iff' 1).mpr hasSum_zeta_two
  have h2 : HasSum (fun n : ℕ => 1 / ((n : ℝ) + 1) ^ 2) (Real.pi ^ 2 / 6) := by simpa using h
  have h3 : Formalism.HermitianLatticeCounting.LatticeSumBounds.zetaR 2 = Real.pi ^ 2 / 6 := h2.tsum_eq
  have h4 := zetaSeries_eq_one_add_tsum 2 le_rfl
  linarith

lemma sum_Icc_three_pow_le (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x < 1) (N : ℕ) :
    ∑ j ∈ Finset.Icc 3 N, x ^ j ≤ x ^ 3 / (1 - x) := by
  have h1x : 0 < 1 - x := by linarith
  have key : ∀ n, (1 - x) * ∑ j ∈ Finset.Icc 3 (n + 2), x ^ j = x ^ 3 - x ^ (n + 3) := by
    intro n
    induction n with
    | zero =>
      rw [Finset.Icc_eq_empty (show ¬ 3 ≤ 0 + 2 by norm_num)]
      simp
    | succ n ih =>
      rw [show n + 1 + 2 = (n + 2) + 1 by ring,
        Finset.sum_Icc_succ_top (show 3 ≤ n + 2 + 1 by omega), mul_add, ih]
      ring
  rw [le_div_iff₀ h1x]
  rcases (show N ≤ 1 ∨ 2 ≤ N by omega) with h | h
  · rw [Finset.Icc_eq_empty (show ¬ 3 ≤ N by omega), Finset.sum_empty, zero_mul]; positivity
  · obtain ⟨n, rfl⟩ : ∃ n, N = n + 2 := ⟨N - 2, by omega⟩
    rw [mul_comm, key n]
    have : 0 ≤ x ^ (n + 3) := by positivity
    linarith

private theorem hasSum_inv_succ_sub_inv_succ_succ_eq_one :
    HasSum (fun n : ℕ => 1 / ((n:ℝ) + 1) - 1 / ((n:ℝ) + 2)) 1 := by
  have hnn : ∀ n : ℕ, 0 ≤ 1 / ((n:ℝ) + 1) - 1 / ((n:ℝ) + 2) := by
    intro n
    have h1 : (0:ℝ) < (n:ℝ) + 1 := by positivity
    rw [sub_nonneg]
    exact one_div_le_one_div_of_le h1 (by linarith)
  rw [hasSum_iff_tendsto_nat_of_nonneg hnn]
  have e : ∀ M : ℕ, ∑ i ∈ Finset.range M, (1 / ((i:ℝ) + 1) - 1 / ((i:ℝ) + 2)) =
      1 - 1 / ((M:ℝ) + 1) := by
    intro M
    induction M with
    | zero => simp
    | succ M ih =>
      rw [Finset.sum_range_succ, ih, Nat.cast_succ, show (M:ℝ) + 1 + 1 = M + 2 by ring]; ring
  simp_rw [e]
  have := (tendsto_const_nhds : Filter.Tendsto (fun _ : ℕ => (1:ℝ)) Filter.atTop (nhds 1)).sub
    tendsto_one_div_add_atTop_nhds_zero_nat
  simpa using this

private theorem hasSum_finset_sum_of_forall_hasSum {γ : Type*} [DecidableEq γ] (s : Finset γ) (f : γ → ℕ → ℝ)
    (a : γ → ℝ) : (∀ i ∈ s, HasSum (f i) (a i)) →
      HasSum (fun n => ∑ i ∈ s, f i n) (∑ i ∈ s, a i) := by
  refine Finset.induction_on s ?_ ?_
  · intro _
    simp only [Finset.sum_empty]
    exact hasSum_zero
  · intro i s hi ih h
    have e1 : (fun n => ∑ j ∈ insert i s, f j n) = fun n => f i n + ∑ j ∈ s, f j n := by
      funext n; rw [Finset.sum_insert hi]
    rw [e1, Finset.sum_insert hi]
    exact (h i (Finset.mem_insert_self i s)).add (ih (fun j hj => h j (Finset.mem_insert_of_mem hj)))

private theorem inv_cube_div_one_sub_inv_eq_of_eq_add_one (a b : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) (hab : b = a + 1) :
    (1 / b) ^ 3 / (1 - 1 / b) = 1 / a - 1 / b - 1 / b ^ 2 := by
  have e1 : 1 - 1 / b = a / b := by
    rw [eq_div_iff hb, sub_mul, one_div, inv_mul_cancel₀ hb, hab]; ring
  have ha' : a * a⁻¹ = 1 := mul_inv_cancel₀ ha
  have hb' : b * b⁻¹ = 1 := mul_inv_cancel₀ hb
  rw [e1, div_div_eq_mul_div, div_eq_iff ha]
  linear_combination (b⁻¹ ^ 2 + 1 + b⁻¹) * hb' - ha' - (b⁻¹ + b⁻¹ ^ 2) * hab

lemma sum_zetaSeries_sub_one_le (N : ℕ) : ∑ j ∈ Finset.Icc 3 N, (zetaR j - 1) ≤ 0.356 := by
  have hH : HasSum (fun n : ℕ => ∑ j ∈ Finset.Icc 3 N, (1 / ((n:ℝ) + 2)) ^ j)
      (∑ j ∈ Finset.Icc 3 N, (Formalism.HermitianLatticeCounting.LatticeSumBounds.zetaR j - 1)) := by
    apply hasSum_finset_sum_of_forall_hasSum
    intro j hj
    have hj2 : 2 ≤ j := by simp only [Finset.mem_Icc] at hj; omega
    show HasSum (fun n : ℕ => (1 / ((n:ℝ) + 2)) ^ j) (Formalism.HermitianLatticeCounting.LatticeSumBounds.zetaR j - 1)
    have e : (fun n : ℕ => (1 / ((n:ℝ) + 2)) ^ j) = fun n : ℕ => 1 / ((n:ℝ) + 2) ^ j := by
      funext n; exact _root_.one_div_pow _ _
    rw [e, show Formalism.HermitianLatticeCounting.LatticeSumBounds.zetaR j - 1 = ∑' n : ℕ, 1 / ((n:ℝ) + 2) ^ j by
      rw [zetaSeries_eq_one_add_tsum j hj2]; ring]
    exact (summable_one_div_add_two_pow j hj2).hasSum
  have hb : ∀ n : ℕ, ∑ j ∈ Finset.Icc 3 N, (1 / ((n:ℝ) + 2)) ^ j ≤
      (1 / ((n:ℝ) + 1) - 1 / ((n:ℝ) + 2)) - 1 / ((n:ℝ) + 2) ^ 2 := by
    intro n
    have hn1 : (0:ℝ) < (n:ℝ) + 1 := by positivity
    have hn2 : (0:ℝ) < (n:ℝ) + 2 := by positivity
    have hx0 : 0 ≤ 1 / ((n:ℝ) + 2) := by positivity
    have hx1 : 1 / ((n:ℝ) + 2) < 1 := by rw [div_lt_one hn2]; linarith
    refine (sum_Icc_three_pow_le _ hx0 hx1 N).trans (le_of_eq ?_)
    exact inv_cube_div_one_sub_inv_eq_of_eq_add_one _ _ hn1.ne' hn2.ne' (by ring)
  have hS1 : HasSum (fun n : ℕ => (1 / ((n:ℝ) + 1) - 1 / ((n:ℝ) + 2)) - 1 / ((n:ℝ) + 2) ^ 2)
      (1 - (Real.pi ^ 2 / 6 - 1)) := by
    have h2 : HasSum (fun n : ℕ => 1 / ((n:ℝ) + 2) ^ 2) (Real.pi ^ 2 / 6 - 1) := by
      rw [← tsum_one_div_add_two_sq]
      exact (summable_one_div_add_two_pow 2 le_rfl).hasSum
    exact hasSum_inv_succ_sub_inv_succ_succ_eq_one.sub h2
  have hle := hasSum_le hb hH hS1
  nlinarith [Real.pi_gt_d4]

lemma one_le_zetaSeries (j : ℕ) (hj : 2 ≤ j) : 1 ≤ zetaR j := by
  rw [zetaSeries_eq_one_add_tsum j hj]
  have : 0 ≤ ∑' n : ℕ, 1 / ((n : ℝ) + 2) ^ j := tsum_nonneg (fun n => by positivity)
  linarith

lemma prod_zetaSeries_le (S : Finset ℕ) (hS : ∀ j ∈ S, 3 ≤ j) : ∏ j ∈ S, zetaR j ≤ Real.exp 0.356 := by
  have hpos : ∀ j ∈ S, 0 < Formalism.HermitianLatticeCounting.LatticeSumBounds.zetaR j := fun j hj =>
    lt_of_lt_of_le one_pos (one_le_zetaSeries j (by have := hS j hj; omega))
  obtain ⟨M, hM⟩ : ∃ M, S ⊆ Finset.Icc 3 M :=
    ⟨S.sup id, fun j hj => Finset.mem_Icc.mpr ⟨hS j hj, Finset.le_sup (f := id) hj⟩⟩
  have hsub : ∑ j ∈ S, (Formalism.HermitianLatticeCounting.LatticeSumBounds.zetaR j - 1) ≤ ∑ j ∈ Finset.Icc 3 M, (Formalism.HermitianLatticeCounting.LatticeSumBounds.zetaR j - 1) :=
    Finset.sum_le_sum_of_subset_of_nonneg hM (fun i hi _ => by
      have : 2 ≤ i := by simp only [Finset.mem_Icc] at hi; omega
      linarith [one_le_zetaSeries i this])
  calc ∏ j ∈ S, Formalism.HermitianLatticeCounting.LatticeSumBounds.zetaR j = Real.exp (∑ j ∈ S, Real.log (Formalism.HermitianLatticeCounting.LatticeSumBounds.zetaR j)) := by
        rw [Real.exp_sum]
        exact Finset.prod_congr rfl (fun j hj => (Real.exp_log (hpos j hj)).symm)
    _ ≤ Real.exp (∑ j ∈ S, (Formalism.HermitianLatticeCounting.LatticeSumBounds.zetaR j - 1)) :=
        Real.exp_le_exp.mpr (Finset.sum_le_sum (fun j hj => Real.log_le_sub_one_of_pos (hpos j hj)))
    _ ≤ Real.exp 0.356 := Real.exp_le_exp.mpr (hsub.trans (sum_zetaSeries_sub_one_le M))

noncomputable def s5bA (v : ℝ) (j : ℕ) : ℝ := ((j - 1).factorial : ℝ) * (v / Real.pi) ^ j

lemma factorialPiWeight_pos (v : ℝ) (hv : 0 < v) (j : ℕ) : 0 < s5bA v j := by
  unfold s5bA
  have := Real.pi_pos
  exact mul_pos (Nat.cast_pos.mpr (Nat.factorial_pos _)) (pow_pos (div_pos hv this) _)

lemma one_le_mul_factorialPiWeight (v : ℝ) (hv : 1 ≤ v) (k : ℕ) (hk : 1 ≤ k) :
    1 ≤ (Real.exp 1 * Real.pi / (k * v)) ^ k * Real.sqrt (k / (2 * Real.pi)) * s5bA v k := by
  have hst := invFactorialLeStirling k hk
  have hk0 : (0:ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hv0 : 0 < v := by linarith
  have hπ0 : Real.pi ≠ 0 := Real.pi_pos.ne'
  have hk0' : (k:ℝ) ≠ 0 := hk0.ne'
  have hv0' : v ≠ 0 := hv0.ne'
  have hF : (0:ℝ) < ((k - 1).factorial : ℝ) := Nat.cast_pos.mpr (Nat.factorial_pos _)
  unfold s5bA
  have e0 : (Real.exp 1 / k) ^ k = (Real.exp 1 * Real.pi / (k * v)) ^ k * (v / Real.pi) ^ k := by
    rw [← mul_pow]; congr 1
    first | (field_simp; ring) | field_simp
  have e : (Real.exp 1 * Real.pi / (k * v)) ^ k * Real.sqrt (k / (2 * Real.pi)) *
      (((k - 1).factorial : ℝ) * (v / Real.pi) ^ k) =
      ((Real.exp 1 / k) ^ k * Real.sqrt (k / (2 * Real.pi))) * ((k - 1).factorial : ℝ) := by
    rw [e0]; ring
  rw [e]
  exact (div_le_iff₀ hF).mp hst

lemma prod_massFactor (f : ℕ) (v : ℝ) (Lv : ℕ → ℝ) (S : Finset ℕ) :
    ∏ j ∈ S, mJ f v Lv j =
      (∏ j ∈ S, s5bA v j) ^ f * ((Real.sqrt ((2 * v) ^ f))⁻¹) ^ S.card * ∏ j ∈ S, Lv j := by
  unfold Formalism.HermitianLatticeCounting.LatticeSumBounds.mJ s5bA
  rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_pow, Finset.prod_const]

lemma factorialPiWeight_le_pi_pow_mul (v : ℝ) (hv : 1 ≤ v) (j t : ℕ) : s5bA v j ≤ Real.pi ^ t * s5bA v (j + t) := by
  unfold s5bA
  have hπ := Real.pi_pos
  have hπ0 : Real.pi ≠ 0 := hπ.ne'
  have hf : ((j - 1).factorial : ℝ) ≤ ((j + t - 1).factorial : ℝ) := by
    exact_mod_cast Nat.factorial_le (show j - 1 ≤ j + t - 1 by omega)
  have hvp : v ^ j ≤ v ^ (j + t) := pow_le_pow_right₀ hv (by omega)
  have e1 : (v / Real.pi) ^ j = v ^ j / Real.pi ^ j := div_pow _ _ _
  have e2 : Real.pi ^ t * (((j + t - 1).factorial : ℝ) * (v / Real.pi) ^ (j + t)) =
      ((j + t - 1).factorial : ℝ) * v ^ (j + t) / Real.pi ^ j := by
    rw [eq_div_iff (pow_ne_zero j hπ0), div_pow, pow_add Real.pi j t]
    calc _ = ((j + t - 1).factorial : ℝ) * v ^ (j + t) *
          ((Real.pi ^ j * Real.pi ^ t) / (Real.pi ^ j * Real.pi ^ t)) := by ring
      _ = ((j + t - 1).factorial : ℝ) * v ^ (j + t) := by rw [div_self (by positivity), mul_one]
  rw [e1, e2, ← mul_div_assoc]
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact mul_le_mul hf hvp (by positivity) (by positivity)

lemma one_le_seventeen_mul_factorialPiWeight (v : ℝ) (hv : 1 ≤ v) (k : ℕ) (hk : 3 ≤ k) : 1 ≤ 17 * s5bA v (k - 1) := by
  have h := piPowDivFactorialLt k hk
  have hπ := Real.pi_pos
  have hF : (0:ℝ) < ((k - 2).factorial : ℝ) := Nat.cast_pos.mpr (Nat.factorial_pos _)
  unfold s5bA
  rw [show k - 1 - 1 = k - 2 by omega]
  have hv' : (1 / Real.pi) ^ (k - 1) ≤ (v / Real.pi) ^ (k - 1) :=
    pow_le_pow_left₀ (by positivity) (div_le_div_of_nonneg_right hv hπ.le) _
  rw [div_lt_iff₀ hF] at h
  have e : (1 / Real.pi) ^ (k - 1) = (Real.pi ^ (k - 1))⁻¹ := by rw [one_div, inv_pow]
  rw [e] at hv'
  have hpk : 0 < Real.pi ^ (k - 1) := pow_pos hπ _
  calc (1:ℝ) = (Real.pi ^ (k - 1))⁻¹ * Real.pi ^ (k - 1) := (inv_mul_cancel₀ hpk.ne').symm
    _ ≤ (Real.pi ^ (k - 1))⁻¹ * (17 * ((k - 2).factorial : ℝ)) :=
        mul_le_mul_of_nonneg_left h.le (inv_nonneg.mpr hpk.le)
    _ ≤ (v / Real.pi) ^ (k - 1) * (17 * ((k - 2).factorial : ℝ)) :=
        mul_le_mul_of_nonneg_right hv' (by positivity)
    _ = 17 * (((k - 2).factorial : ℝ) * (v / Real.pi) ^ (k - 1)) := by ring

lemma prod_factorialPiWeight_le (v : ℝ) (hv : 1 ≤ v) (k s : ℕ) (hs : 2 ≤ s) (hk : s + 2 ≤ k) :
    ∏ j ∈ Finset.Ioc 2 s, s5bA v j ≤
      (Real.pi ^ ((s - 2) * (k - s - 2)) * 17 *
        ((Real.exp 1 * Real.pi / (k * v)) ^ k * Real.sqrt (k / (2 * Real.pi)))) *
        ∏ j ∈ Finset.Ioc (k - s) k, s5bA v j := by
  have hv0 : 0 < v := by linarith
  have hW : ∀ j, 0 < s5bA v j := factorialPiWeight_pos v hv0
  obtain ⟨t, ht⟩ : ∃ t, t = k - s - 2 := ⟨_, rfl⟩
  rw [← ht]
  have h1 : ∏ j ∈ Finset.Ioc 2 s, s5bA v j ≤
      Real.pi ^ (t * (s - 2)) * ∏ j ∈ Finset.Ioc 2 s, s5bA v (j + t) := by
    calc ∏ j ∈ Finset.Ioc 2 s, s5bA v j
          ≤ ∏ j ∈ Finset.Ioc 2 s, (Real.pi ^ t * s5bA v (j + t)) :=
          Finset.prod_le_prod₀ (fun j _ => (hW j).le)
            (fun j _ => factorialPiWeight_le_pi_pow_mul v hv j t)
      _ = Real.pi ^ (t * (s - 2)) * ∏ j ∈ Finset.Ioc 2 s, s5bA v (j + t) := by
          rw [Finset.prod_mul_distrib, Finset.prod_const, Nat.card_Ioc, ← pow_mul]
  have h2 : ∏ j ∈ Finset.Ioc 2 s, s5bA v (j + t) =
      ∏ j ∈ Finset.Ioc (k - s) (k - 2), s5bA v j := by
    rw [show k - s = 2 + t by omega, show k - 2 = s + t by omega, ← Finset.map_add_right_Ioc,
      Finset.prod_map]
    rfl
  have h3 : ∏ j ∈ Finset.Ioc (k - s) k, s5bA v j =
      (∏ j ∈ Finset.Ioc (k - s) (k - 2), s5bA v j) * s5bA v (k - 1) *
        s5bA v k := by
    obtain ⟨m, rfl⟩ : ∃ m, k = m + 2 := ⟨k - 2, by omega⟩
    rw [show m + 2 - 2 = m by omega, show m + 2 - 1 = m + 1 by omega,
      show m + 2 = m + 1 + 1 by ring,
      Finset.prod_Ioc_succ_top (show m + 1 + 1 - s ≤ m + 1 by omega),
      Finset.prod_Ioc_succ_top (show m + 1 + 1 - s ≤ m by omega)]
  have hA := one_le_seventeen_mul_factorialPiWeight v hv k (by omega)
  have hB := one_le_mul_factorialPiWeight v hv k (by omega)
  have hP0 : 0 ≤ ∏ j ∈ Finset.Ioc (k - s) (k - 2), s5bA v j :=
    Finset.prod_nonneg (fun j _ => (hW j).le)
  have hX0 : 0 ≤ Real.pi ^ (t * (s - 2)) * ∏ j ∈ Finset.Ioc (k - s) (k - 2), s5bA v j :=
    mul_nonneg (pow_nonneg Real.pi_pos.le _) hP0
  rw [h3]
  calc ∏ j ∈ Finset.Ioc 2 s, s5bA v j
        ≤ Real.pi ^ (t * (s - 2)) * ∏ j ∈ Finset.Ioc (k - s) (k - 2), s5bA v j := by
        rw [← h2]; exact h1
    _ = (Real.pi ^ (t * (s - 2)) * ∏ j ∈ Finset.Ioc (k - s) (k - 2), s5bA v j) * 1 * 1 := by
        ring
    _ ≤ (Real.pi ^ (t * (s - 2)) * ∏ j ∈ Finset.Ioc (k - s) (k - 2), s5bA v j) *
          (17 * s5bA v (k - 1)) *
          ((Real.exp 1 * Real.pi / (k * v)) ^ k * Real.sqrt (k / (2 * Real.pi)) * s5bA v k) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hA hX0) hB zero_le_one
          (mul_nonneg hX0 (by linarith))
    _ = (Real.pi ^ ((s - 2) * t) * 17 *
          ((Real.exp 1 * Real.pi / (k * v)) ^ k * Real.sqrt (k / (2 * Real.pi)))) *
          ((∏ j ∈ Finset.Ioc (k - s) (k - 2), s5bA v j) * s5bA v (k - 1) *
            s5bA v k) := by ring

theorem massRatioBound : XiBound := by
  intro f k s v mass2 Lv hv hm2 hs hk hL
  have hv0 : 0 < v := by linarith
  have hA3 : ∀ j ∈ Finset.Ioc 2 s, 3 ≤ j := by intro j hj; rw [Finset.mem_Ioc] at hj; omega
  have hB3 : ∀ j ∈ Finset.Ioc (k - s) k, 3 ≤ j := by intro j hj; rw [Finset.mem_Ioc] at hj; omega
  have hzpos : ∀ j, 3 ≤ j → 0 < Formalism.HermitianLatticeCounting.LatticeSumBounds.zetaR j := fun j hj =>
    lt_of_lt_of_le one_pos (one_le_zetaSeries j (by omega))
  have hLpos : ∀ j, 3 ≤ j → 0 < Lv j := fun j hj =>
    lt_of_lt_of_le (inv_pos.mpr (pow_pos (hzpos j hj) f)) (hL j hj).1
  have hW : ∀ j, 0 < s5bA v j := factorialPiWeight_pos v hv0
  have hσ0 : 0 < Real.sqrt ((2 * v) ^ f) := Real.sqrt_pos.mpr (by positivity)
  have hσ2 : Real.sqrt ((2 * v) ^ f) ^ 2 = (2 * v) ^ f := Real.sq_sqrt (by positivity)
  have hPB0 : 0 < ∏ j ∈ Finset.Ioc (k - s) k, s5bA v j := Finset.prod_pos (fun j _ => hW j)
  have hLB0 : 0 < ∏ j ∈ Finset.Ioc (k - s) k, Lv j := Finset.prod_pos (fun j hj => hLpos j (hB3 j hj))
  have hR := prod_factorialPiWeight_le v hv k s hs hk
  have hratio : (∏ j ∈ Finset.Ioc 2 s, s5bA v j) /
      (∏ j ∈ Finset.Ioc (k - s) k, s5bA v j) ≤
      Real.pi ^ ((s - 2) * (k - s - 2)) * 17 *
        ((Real.exp 1 * Real.pi / (k * v)) ^ k * Real.sqrt (k / (2 * Real.pi))) := by
    rw [div_le_iff₀ hPB0]; exact hR
  have hLA : ∏ j ∈ Finset.Ioc 2 s, Lv j ≤ Real.exp 0.356 ^ f := by
    calc ∏ j ∈ Finset.Ioc 2 s, Lv j ≤ ∏ j ∈ Finset.Ioc 2 s, Formalism.HermitianLatticeCounting.LatticeSumBounds.zetaR j ^ f :=
          Finset.prod_le_prod₀ (fun j hj => (hLpos j (hA3 j hj)).le) (fun j hj => (hL j (hA3 j hj)).2)
      _ = (∏ j ∈ Finset.Ioc 2 s, Formalism.HermitianLatticeCounting.LatticeSumBounds.zetaR j) ^ f := Finset.prod_pow _ _ _
      _ ≤ Real.exp 0.356 ^ f :=
          pow_le_pow_left₀ (Finset.prod_nonneg (fun j hj => (hzpos j (hA3 j hj)).le))
            (prod_zetaSeries_le _ hA3) f
  have hLB : (∏ j ∈ Finset.Ioc (k - s) k, Lv j)⁻¹ ≤ Real.exp 0.356 ^ f := by
    have h1 : ((∏ j ∈ Finset.Ioc (k - s) k, Formalism.HermitianLatticeCounting.LatticeSumBounds.zetaR j) ^ f)⁻¹ ≤ ∏ j ∈ Finset.Ioc (k - s) k, Lv j := by
      rw [← Finset.prod_pow, ← Finset.prod_inv_distrib]
      exact Finset.prod_le_prod₀ (fun j hj => (inv_pos.mpr (pow_pos (hzpos j (hB3 j hj)) f)).le)
        (fun j hj => (hL j (hB3 j hj)).1)
    have h2 : 0 < (∏ j ∈ Finset.Ioc (k - s) k, Formalism.HermitianLatticeCounting.LatticeSumBounds.zetaR j) ^ f :=
      pow_pos (Finset.prod_pos (fun j hj => hzpos j (hB3 j hj))) f
    have h3 := inv_anti₀ (inv_pos.mpr h2) h1
    rw [inv_inv] at h3
    exact h3.trans (pow_le_pow_left₀ (Finset.prod_nonneg (fun j hj => (hzpos j (hB3 j hj)).le))
      (prod_zetaSeries_le _ hB3) f)
  have hexp : Real.exp 0.356 ^ f * Real.exp 0.356 ^ f ≤ Real.exp (0.72 * f) := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]
    exact Real.exp_le_exp.mpr (by have := (Nat.cast_nonneg f : (0:ℝ) ≤ f); linarith)
  have key : ∀ (M PA PB LA LB σ : ℝ) (a : ℕ), 0 < PB → 0 < LB → 0 < σ →
      M * (PA ^ f * σ⁻¹ ^ a * LA) / (PB ^ f * σ⁻¹ ^ (a + 2) * LB) =
        M * (PA / PB) ^ f * σ ^ 2 * (LA * LB⁻¹) := by
    intro M PA PB LA LB σ a hPB hLB hσ
    have hP : PB ^ f * PB⁻¹ ^ f = 1 := by rw [← mul_pow, mul_inv_cancel₀ hPB.ne', one_pow]
    have hS : σ ^ 2 * σ⁻¹ ^ 2 = 1 := by rw [← mul_pow, mul_inv_cancel₀ hσ.ne', one_pow]
    have hL : LB * LB⁻¹ = 1 := mul_inv_cancel₀ hLB.ne'
    rw [div_eq_iff (by positivity)]
    linear_combination (-(M * PA ^ f * σ⁻¹ ^ a * LA) * (σ ^ 2 * σ⁻¹ ^ 2) * (LB * LB⁻¹)) * hP +
      (-(M * PA ^ f * σ⁻¹ ^ a * LA) * (LB * LB⁻¹)) * hS + (-(M * PA ^ f * σ⁻¹ ^ a * LA)) * hL
  rw [prod_massFactor, prod_massFactor, Nat.card_Ioc, Nat.card_Ioc, show k - (k - s) = s by omega]
  have hs' : (Real.sqrt ((2 * v) ^ f))⁻¹ ^ s = (Real.sqrt ((2 * v) ^ f))⁻¹ ^ ((s - 2) + 2) := by
    congr 1; omega
  rw [hs', key _ _ _ _ _ _ _ hPB0 hLB0 hσ0, hσ2]
  have hRf0 : 0 ≤ Real.pi ^ ((s - 2) * (k - s - 2)) * 17 *
      ((Real.exp 1 * Real.pi / (k * v)) ^ k * Real.sqrt (k / (2 * Real.pi))) := by positivity
  calc mass2 * ((∏ j ∈ Finset.Ioc 2 s, s5bA v j) /
          (∏ j ∈ Finset.Ioc (k - s) k, s5bA v j)) ^ f * (2 * v) ^ f *
          ((∏ j ∈ Finset.Ioc 2 s, Lv j) * (∏ j ∈ Finset.Ioc (k - s) k, Lv j)⁻¹)
        ≤ mass2 * (Real.pi ^ ((s - 2) * (k - s - 2)) * 17 *
            ((Real.exp 1 * Real.pi / (k * v)) ^ k * Real.sqrt (k / (2 * Real.pi)))) ^ f * (2 * v) ^ f *
          (Real.exp 0.356 ^ f * Real.exp 0.356 ^ f) :=
        mul_le_mul (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (div_nonneg (Finset.prod_nonneg (fun j _ => (hW j).le)) hPB0.le) hratio f) hm2)
          (by positivity))
          (mul_le_mul hLA hLB (inv_nonneg.mpr hLB0.le) (by positivity))
          (mul_nonneg (Finset.prod_nonneg (fun j hj => (hLpos j (hA3 j hj)).le)) (inv_nonneg.mpr hLB0.le))
          (by positivity)
    _ ≤ mass2 * (Real.pi ^ ((s - 2) * (k - s - 2)) * 17 *
            ((Real.exp 1 * Real.pi / (k * v)) ^ k * Real.sqrt (k / (2 * Real.pi)))) ^ f * (2 * v) ^ f *
          Real.exp (0.72 * f) := mul_le_mul_of_nonneg_left hexp (by positivity)
    _ = mass2 * (2 * v) ^ f * Real.exp (0.72 * f) * 17 ^ f * Real.sqrt (k / (2 * Real.pi)) ^ f *
          Real.pi ^ ((s - 2) * (k - s - 2) * f) * (Real.exp 1 * Real.pi / (k * v)) ^ (k * f) := by
        ring

end Formalism.HermitianLatticeCounting.P
