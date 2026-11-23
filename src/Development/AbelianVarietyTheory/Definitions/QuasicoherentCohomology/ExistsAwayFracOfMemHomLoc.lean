module

public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.CubeComplexAcyclicIffQuasiIsoCechAug
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.CubeComplexExactAtOfIsLocalizedModuleRes
public import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.IsGradedMapLinearCombination
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.Algebra.Module.LocalizedModule.Exact
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
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open DirectSum MvPolynomial CategoryTheory

universe u

noncomputable section

namespace GlobalTheory

open GradedHilbert

section Away

variable {A : Type*} [CommRing A] (M : Type*) [AddCommGroup M] [Module A M]
  {N : Type*} [AddCommGroup N] [Module A N] {P : Type*} [AddCommGroup P] [Module A P]

def awayFrac (f : A) (k : ℕ) : M →ₗ[A] LocalizedModule.Away f M :=
  LocalizedModule.divBy (⟨f ^ k, k, rfl⟩ : Submonoid.powers f) ∘ₗ
    LocalizedModule.mkLinearMap (Submonoid.powers f) M

variable {M}

theorem awayFrac_apply (f : A) (k : ℕ) (m : M) :
    awayFrac M f k m = LocalizedModule.mk m (⟨f ^ k, k, rfl⟩ : Submonoid.powers f) := by
  simp [awayFrac, LocalizedModule.liftOn_mk]

theorem awayFrac_zero (f : A) :
    awayFrac M f 0 = LocalizedModule.mkLinearMap (Submonoid.powers f) M := by
  ext m
  rw [awayFrac_apply, LocalizedModule.mkLinearMap_apply]
  congr 1
  exact Subtype.ext (pow_zero f)

theorem exists_awayFrac {f : A} (z : LocalizedModule.Away f M) :
    ∃ k m, awayFrac M f k m = z := by
  induction z using LocalizedModule.induction_on with | _ m s
  obtain ⟨_, k, rfl⟩ := s
  exact ⟨k, m, awayFrac_apply f k m⟩

theorem awayFrac_eq_iff {f : A} {k j : ℕ} {m m' : M} :
    awayFrac M f k m = awayFrac M f j m' ↔ ∃ l : ℕ, f ^ (l + j) • m = f ^ (l + k) • m' := by
  rw [awayFrac_apply, awayFrac_apply, LocalizedModule.mk_eq]
  constructor
  · rintro ⟨⟨_, l, rfl⟩, h⟩
    exact ⟨l, by simpa [pow_add, mul_smul, Submonoid.smul_def] using h⟩
  · rintro ⟨l, h⟩
    exact ⟨⟨_, l, rfl⟩, by simpa [pow_add, mul_smul, Submonoid.smul_def] using h⟩

theorem awayFrac_eq_zero_iff {f : A} {k : ℕ} {m : M} :
    awayFrac M f k m = 0 ↔ ∃ l : ℕ, f ^ l • m = 0 := by
  rw [← map_zero (awayFrac M f 0), awayFrac_eq_iff]
  simp

theorem awayFrac_add_pow_smul (f : A) (k j : ℕ) (m : M) :
    awayFrac M f (k + j) (f ^ j • m) = awayFrac M f k m :=
  awayFrac_eq_iff.2 ⟨0, by simp [pow_add, mul_smul]⟩

theorem pow_smul_awayFrac (f : A) (k : ℕ) (m : M) :
    f ^ k • awayFrac M f k m = awayFrac M f 0 m := by
  rw [← map_smul, ← awayFrac_add_pow_smul f 0 k, zero_add]

theorem isUnit_away_of_dvd_pow {f g : A} {k : ℕ} (h : f ∣ g ^ k) :
    IsUnit (algebraMap A (Module.End A (LocalizedModule.Away g M)) f) :=
  isUnit_algebraMap_end_of_dvd h (IsLocalizedModule.map_units
    (LocalizedModule.mkLinearMap (Submonoid.powers g) M) (⟨g ^ k, k, rfl⟩ : Submonoid.powers g))

theorem smul_away_bijective {f g : A} {k : ℕ} (h : f ∣ g ^ k) :
    Function.Bijective (LinearMap.lsmul A (LocalizedModule.Away g M) f) :=
  (Module.End.isUnit_iff _).1 (isUnit_away_of_dvd_pow h)

theorem away_ext {f : A} {φ ψ : LocalizedModule.Away f M →ₗ[A] N}
    (h : ∀ k m, φ (awayFrac M f k m) = ψ (awayFrac M f k m)) : φ = ψ :=
  LinearMap.ext fun z => by
    obtain ⟨k, m, rfl⟩ := exists_awayFrac z
    exact h k m

def awayMap (f : A) (φ : M →ₗ[A] N) : LocalizedModule.Away f M →ₗ[A] LocalizedModule.Away f N :=
  IsLocalizedModule.map (Submonoid.powers f) (LocalizedModule.mkLinearMap _ M)
    (LocalizedModule.mkLinearMap _ N) φ

@[simp]
theorem awayMap_awayFrac (f : A) (φ : M →ₗ[A] N) (k : ℕ) (m : M) :
    awayMap f φ (awayFrac M f k m) = awayFrac N f k (φ m) := by
  rw [awayFrac_apply, awayFrac_apply]
  exact IsLocalizedModule.map_LocalizedModules _ _ _ _

theorem awayMap_comp (f : A) (ψ : N →ₗ[A] P) (φ : M →ₗ[A] N) :
    awayMap f (ψ ∘ₗ φ) = awayMap f ψ ∘ₗ awayMap f φ :=
  away_ext fun k m => by simp

@[simp]
theorem awayMap_zero (f : A) : awayMap f (0 : M →ₗ[A] N) = 0 := map_zero _

theorem awayMap_injective_of {f : A} {φ : M →ₗ[A] N}
    (h : ∀ m, φ m = 0 → ∃ k : ℕ, f ^ k • m = 0) : Function.Injective (awayMap f φ) := by
  rw [injective_iff_map_eq_zero]
  intro z hz
  obtain ⟨k, m, rfl⟩ := exists_awayFrac z
  rw [awayMap_awayFrac, awayFrac_eq_zero_iff] at hz
  obtain ⟨l, hl⟩ := hz
  obtain ⟨j, hj⟩ := h _ ((map_smul φ _ _).trans hl)
  exact awayFrac_eq_zero_iff.2 ⟨j + l, by rw [pow_add, mul_smul, hj]⟩

theorem awayMap_surjective_of {f : A} {φ : M →ₗ[A] N}
    (h : ∀ y, ∃ k : ℕ, f ^ k • y ∈ LinearMap.range φ) : Function.Surjective (awayMap f φ) := by
  intro z
  obtain ⟨k, y, rfl⟩ := exists_awayFrac z
  obtain ⟨j, m, hm⟩ := h y
  exact ⟨awayFrac M f (k + j) m, by rw [awayMap_awayFrac, hm, awayFrac_add_pow_smul]⟩

theorem awayMap_exact (f : A) {φ : M →ₗ[A] N} {ψ : N →ₗ[A] P} (h : Function.Exact φ ψ) :
    Function.Exact (awayMap f φ) (awayMap f ψ) :=
  IsLocalizedModule.map_exact _ _ _ _ _ _ h

theorem awayFrac_injective {f : A} (h : Function.Injective fun m : M => f • m) (k : ℕ) :
    Function.Injective (awayFrac M f k) := by
  rw [injective_iff_map_eq_zero]
  intro m hm
  obtain ⟨l, hl⟩ := awayFrac_eq_zero_iff.1 hm
  exact (IsSMulRegular.pow l h) (hl.trans (smul_zero _).symm)

theorem awayFrac_zero_bijective {f : A} (h : Function.Bijective fun m : M => f • m) :
    Function.Bijective (awayFrac M f 0) := by
  refine ⟨awayFrac_injective h.1 0, fun z => ?_⟩
  obtain ⟨k, m, rfl⟩ := exists_awayFrac z
  obtain ⟨y, rfl⟩ := (h.2.iterate k) m
  refine ⟨y, ?_⟩
  rw [smul_iterate_apply, ← awayFrac_add_pow_smul f 0 k, zero_add]

theorem locRes_awayFrac {ι : Type} (f : ι → A) {s t : Finset ι} (h : s ⊆ t) {c : A}
    (hc : ∏ i ∈ t, f i = c * ∏ i ∈ s, f i) (k : ℕ) (m : M) :
    locRes f M h (awayFrac M _ k m) = awayFrac M _ k (c ^ k • m) := by
  rw [awayFrac_apply, awayFrac_apply]
  exact locRes_mk f M h m _ _ _ (by simp [hc, mul_pow])

@[simp]
theorem locRes_awayFrac_zero {ι : Type} (f : ι → A) {s t : Finset ι} (h : s ⊆ t) (m : M) :
    locRes f M h (awayFrac M _ 0 m) = awayFrac M _ 0 m := by
  rw [awayFrac_zero, awayFrac_zero]
  exact locRes_mk_one f M h m

theorem awayMap_locRes {ι : Type} (f : ι → A) {s t : Finset ι} (h : s ⊆ t) (φ : M →ₗ[A] N)
    (z : LocalizedModule.Away (∏ i ∈ s, f i) M) :
    awayMap _ φ (locRes f M h z) = locRes f N h (awayMap _ φ z) := by
  obtain ⟨k, m, rfl⟩ := exists_awayFrac z
  obtain ⟨c, hc⟩ := exists_eq_mul_left_of_dvd (Finset.prod_dvd_prod_of_subset s t f h)
  rw [locRes_awayFrac f h hc, awayMap_awayFrac, awayMap_awayFrac, locRes_awayFrac f h hc, map_smul]

end Away

section HomLoc

variable {ι : Type} {R : Type*} [CommRing R]
  {M : Type*} [AddCommGroup M] [Module R M] [Module (MvPolynomial ι R) M]
  [IsScalarTower R (MvPolynomial ι R) M]
  {N : Type*} [AddCommGroup N] [Module R N] [Module (MvPolynomial ι R) N]
  [IsScalarTower R (MvPolynomial ι R) N]
  {P : Type*} [AddCommGroup P] [Module R P] [Module (MvPolynomial ι R) P]
  [IsScalarTower R (MvPolynomial ι R) P]

variable (R) in
abbrev xProd (s : Finset ι) : MvPolynomial ι R := ∏ i ∈ s, X i

variable (R) in
theorem xProd_mem (s : Finset ι) : xProd R s ∈ polyGrading ι R s.card := by
  simpa using SetLike.prod_mem_graded (polyGrading ι R) (fun _ => 1) X
    (F := s) fun i _ => X_mem_polyGrading i

variable (R) in
theorem xProd_pow_mem (s : Finset ι) (k : ℕ) :
    xProd R s ^ k ∈ polyGrading ι R (k * s.card) := by
  simpa using SetLike.pow_mem_graded k (xProd_mem R s)

variable (ℳ : ℤ → Submodule R M) [PolyGradedSMul ι ℳ] {𝒩 : ℤ → Submodule R N} [PolyGradedSMul ι 𝒩]
  {𝒬 : ℤ → Submodule R P} [PolyGradedSMul ι 𝒬]

omit [IsScalarTower R (MvPolynomial ι R) M] in
theorem xProd_pow_smul_mem {s : Finset ι} {n : ℤ} {k : ℕ} {m : M} (hm : m ∈ ℳ (n + k * s.card))
    (j : ℕ) : xProd R s ^ j • m ∈ ℳ (n + (k + j : ℕ) * s.card) := by
  convert grSMul_mem ℳ (xProd_pow_mem R s j) hm using 2
  push_cast
  ring

def homLoc (s : Finset ι) (n : ℤ) : Submodule R (LocalizedModule.Away (xProd R s) M) where
  carrier := {z | ∃ k : ℕ, ∃ m ∈ ℳ (n + k * s.card), awayFrac M (xProd R s) k m = z}
  zero_mem' := ⟨0, 0, zero_mem _, map_zero _⟩
  add_mem' := by
    rintro _ _ ⟨k, m, hm, rfl⟩ ⟨j, m', hm', rfl⟩
    refine ⟨k + j, xProd R s ^ j • m + xProd R s ^ k • m',
      add_mem (xProd_pow_smul_mem ℳ hm j) (add_comm j k ▸ xProd_pow_smul_mem ℳ hm' k), ?_⟩
    rw [map_add (f := _), awayFrac_add_pow_smul, add_comm k j, awayFrac_add_pow_smul]
  smul_mem' := by
    rintro r _ ⟨k, m, hm, rfl⟩
    exact ⟨k, r • m, Submodule.smul_mem _ r hm, LinearMap.map_smul_of_tower _ r m⟩

variable {ℳ} in
theorem mem_homLoc {s : Finset ι} {n : ℤ} {z : LocalizedModule.Away (xProd R s) M} :
    z ∈ homLoc ℳ s n ↔
      ∃ k : ℕ, ∃ m ∈ ℳ (n + k * s.card), awayFrac M (xProd R s) k m = z := Iff.rfl

variable {ℳ} in
theorem awayFrac_mem_homLoc {s : Finset ι} {n d : ℤ} {k : ℕ} {m : M} (hm : m ∈ ℳ d)
    (h : d = n + k * s.card) : awayFrac M (xProd R s) k m ∈ homLoc ℳ s n := ⟨k, m, h ▸ hm, rfl⟩

theorem exists_awayFrac_of_mem_homLoc {s : Finset ι} {n : ℤ}
    {z : LocalizedModule.Away (xProd R s) M} (hz : z ∈ homLoc ℳ s n) :
    ∃ k₀ : ℕ, ∀ k ≥ k₀, ∃ m ∈ ℳ (n + k * s.card), awayFrac M (xProd R s) k m = z := by
  obtain ⟨k₀, m, hm, rfl⟩ := hz
  refine ⟨k₀, fun k hk => ?_⟩
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hk
  exact ⟨_, xProd_pow_smul_mem ℳ hm j, awayFrac_add_pow_smul _ _ _ _⟩

instance homLoc.polyGradedSMul (s : Finset ι) : PolyGradedSMul ι (homLoc ℳ s) where
  smul_mem := by
    rintro d n p _ hp ⟨k, m, hm, rfl⟩
    rw [← map_smul]
    exact awayFrac_mem_homLoc (grSMul_mem ℳ hp hm) (by rw [vadd_eq_add]; ring)

instance homLoc.decomposition [Decomposition ℳ] (s : Finset ι) : Decomposition (homLoc ℳ s) :=
  IsInternal.chooseDecomposition _ <| isInternal_of_sum_eq_zero _
    (fun T v hv h j hj => by
      choose! k hk using fun i hi => exists_awayFrac_of_mem_homLoc ℳ (hv i hi)
      choose! m hm e using fun i hi => hk i hi (T.sup k) (Finset.le_sup hi)

      rw [← Finset.sum_congr rfl e, ← map_sum, awayFrac_eq_zero_iff] at h
      obtain ⟨l, hl⟩ := h
      rw [← e j hj, awayFrac_eq_zero_iff]
      refine ⟨l, ?_⟩
      have := grProj_sum (grShift ℳ ((T.sup k + l : ℕ) * s.card)) T
        (fun i => xProd R s ^ l • m i) (fun i hi => xProd_pow_smul_mem ℳ (hm i hi) l) hj
      rw [← this, ← Finset.smul_sum, hl, map_zero])
    fun z => by
      obtain ⟨k, m, rfl⟩ := exists_awayFrac z
      induction m using Decomposition.inductionOn ℳ with
      | zero => rw [map_zero]; exact zero_mem _
      | @homogeneous n m =>
        exact Submodule.mem_iSup_of_mem (n - k * s.card) (awayFrac_mem_homLoc m.2 (by ring))
      | add a b ha hb => rw [(awayFrac M (xProd R s) k).map_add]; exact add_mem ha hb

theorem isGradedMap_awayFrac (s : Finset ι) (k : ℕ) :
    IsGradedMap (grShift ℳ (k * s.card)) (homLoc ℳ s) (awayFrac M (xProd R s) k) :=
  fun _ _ h => awayFrac_mem_homLoc h rfl

theorem isGradedMap_awayFrac_zero (s : Finset ι) :
    IsGradedMap ℳ (homLoc ℳ s) (awayFrac M (xProd R s) 0) :=
  fun _ _ h => awayFrac_mem_homLoc h (by simp)

theorem isGradedMap_locRes {s t : Finset ι} (h : s ⊆ t) :
    IsGradedMap (homLoc ℳ s) (homLoc ℳ t) (locRes X M h) := by
  classical
  rintro n _ ⟨k, m, hm, rfl⟩
  rw [locRes_awayFrac X h (Finset.prod_sdiff h).symm]
  refine awayFrac_mem_homLoc (grSMul_mem ℳ (xProd_pow_mem R (t \ s) k) hm) ?_
  rw [← Finset.card_sdiff_add_card_eq_card h]
  push_cast
  ring

variable {ℳ} in
theorem IsGradedMap.awayMap {f : M →ₗ[MvPolynomial ι R] N} (hf : IsGradedMap ℳ 𝒩 f)
    (s : Finset ι) : IsGradedMap (homLoc ℳ s) (homLoc 𝒩 s) (awayMap (xProd R s) f) := by
  rintro n _ ⟨k, m, hm, rfl⟩
  rw [awayMap_awayFrac]
  exact awayFrac_mem_homLoc (hf hm) rfl

theorem homLoc_grShift (d : ℤ) (s : Finset ι) (n : ℤ) :
    homLoc (grShift ℳ d) s n = homLoc ℳ s (n + d) := by
  ext z
  simp only [mem_homLoc, grShift_apply, add_right_comm]

def homLocMk (s : Finset ι) (n : ℤ) (k : ℕ) : ℳ (n + k * s.card) →ₗ[R] homLoc ℳ s n :=
  (isGradedMap_awayFrac ℳ s k).piece n

@[simp]
theorem coe_homLocMk (s : Finset ι) (n : ℤ) (k : ℕ) (m : ℳ (n + k * s.card)) :
    (homLocMk ℳ s n k m : LocalizedModule.Away (xProd R s) M) = awayFrac M (xProd R s) k m := rfl

variable {ℳ} in
theorem exists_homLocMk {s : Finset ι} {n : ℤ} (z : homLoc ℳ s n) :
    ∃ k m, homLocMk ℳ s n k m = z := by
  obtain ⟨_, k, m, hm, rfl⟩ := z
  exact ⟨k, ⟨m, hm⟩, rfl⟩

def toHomLoc (s : Finset ι) (n : ℤ) : ℳ n →ₗ[R] homLoc ℳ s n :=
  (isGradedMap_awayFrac_zero ℳ s).piece n

@[simp]
theorem coe_toHomLoc (s : Finset ι) (n : ℤ) (m : ℳ n) :
    (toHomLoc ℳ s n m : LocalizedModule.Away (xProd R s) M) = awayFrac M (xProd R s) 0 m := rfl

def homLocRes {s t : Finset ι} (h : s ⊆ t) (n : ℤ) : homLoc ℳ s n →ₗ[R] homLoc ℳ t n :=
  (isGradedMap_locRes ℳ h).piece n

@[simp]
theorem coe_homLocRes {s t : Finset ι} (h : s ⊆ t) (n : ℤ) (z : homLoc ℳ s n) :
    (homLocRes ℳ h n z : LocalizedModule.Away (xProd R t) M) = locRes X M h z := rfl

@[simp]
theorem homLocRes_self {s : Finset ι} (h : s ⊆ s) (n : ℤ) (z : homLoc ℳ s n) :
    homLocRes ℳ h n z = z := Subtype.ext congr($(locRes_self X M s) z)

@[simp]
theorem homLocRes_homLocRes {s t w : Finset ι} (h : s ⊆ t) (h' : t ⊆ w) (n : ℤ)
    (z : homLoc ℳ s n) : homLocRes ℳ h' n (homLocRes ℳ h n z) = homLocRes ℳ (h.trans h') n z :=
  Subtype.ext congr($(locRes_comp X M h h') z)

@[simp]
theorem homLocRes_toHomLoc {s t : Finset ι} (h : s ⊆ t) (n : ℤ) (m : ℳ n) :
    homLocRes ℳ h n (toHomLoc ℳ s n m) = toHomLoc ℳ t n m := by
  apply Subtype.ext
  rw [coe_homLocRes, coe_toHomLoc, coe_toHomLoc, locRes_awayFrac_zero]

theorem toHomLoc_injective {s : Finset ι} (h : Function.Injective fun m : M => xProd R s • m)
    (n : ℤ) : Function.Injective (toHomLoc ℳ s n) :=
  fun _ _ e => Subtype.ext (awayFrac_injective h 0 (congrArg Subtype.val e))

theorem toHomLoc_bijective [Decomposition ℳ] {s : Finset ι}
    (h : Function.Bijective fun m : M => xProd R s • m) (n : ℤ) :
    Function.Bijective (toHomLoc ℳ s n) :=
  ⟨toHomLoc_injective ℳ h.1 n,
    (isGradedMap_awayFrac_zero ℳ s).surjective_iff.1 (awayFrac_zero_bijective h).2 n⟩

variable (ι) in
def homLocEmptyEquiv (n : ℤ) : ℳ n ≃ₗ[R] homLoc ℳ (∅ : Finset ι) n :=
  LinearEquiv.ofBijective (toHomLoc ℳ ∅ n)
    ⟨toHomLoc_injective ℳ (fun _ _ h => by simpa using h) n, by
      rintro ⟨_, k, m, hm, rfl⟩
      exact ⟨⟨m, by simpa using hm⟩, Subtype.ext (awayFrac_eq_iff.2 ⟨0, by simp⟩)⟩⟩

def homLocSMul {p : MvPolynomial ι R} {d : ℤ} (hp : p ∈ polyGrading ι R d) (s : Finset ι)
    (n : ℤ) : homLoc ℳ s n →ₗ[R] homLoc ℳ s (n + d) :=
  (isGradedMap_lsmul (homLoc ℳ s) hp).piece n

theorem homLocSMul_bijective [Decomposition ℳ] {p : MvPolynomial ι R} {d : ℤ}
    (hp : p ∈ polyGrading ι R d) {s : Finset ι} {k : ℕ} (h : p ∣ xProd R s ^ k) (n : ℤ) :
    Function.Bijective (homLocSMul ℳ hp s n) :=
  ⟨(isGradedMap_lsmul (homLoc ℳ s) hp).injective_iff.1 (smul_away_bijective h).1 n,
    (isGradedMap_lsmul (homLoc ℳ s) hp).surjective_iff.1 (smul_away_bijective h).2 n⟩

theorem homLocSMul_X_bijective [Decomposition ℳ] {s : Finset ι} {i : ι} (hi : i ∈ s) (n : ℤ) :
    Function.Bijective (homLocSMul ℳ (X_mem_polyGrading i) s n) :=
  homLocSMul_bijective ℳ _ (k := 1) (by rw [pow_one]; exact Finset.dvd_prod_of_mem _ hi) n

variable {ℳ}

def homLocMap {f : M →ₗ[MvPolynomial ι R] N} (hf : IsGradedMap ℳ 𝒩 f) (s : Finset ι) (n : ℤ) :
    homLoc ℳ s n →ₗ[R] homLoc 𝒩 s n := (hf.awayMap s).piece n

@[simp]
theorem homLocMap_homLocMk {f : M →ₗ[MvPolynomial ι R] N} (hf : IsGradedMap ℳ 𝒩 f) (s : Finset ι)
    (n : ℤ) (k : ℕ) (m : ℳ (n + k * s.card)) :
    homLocMap hf s n (homLocMk ℳ s n k m) = homLocMk 𝒩 s n k (hf.piece _ m) :=
  Subtype.ext (awayMap_awayFrac (xProd R s) f k (m : M))

@[simp]
theorem homLocMap_toHomLoc {f : M →ₗ[MvPolynomial ι R] N} (hf : IsGradedMap ℳ 𝒩 f) (s : Finset ι)
    (n : ℤ) (m : ℳ n) : homLocMap hf s n (toHomLoc ℳ s n m) = toHomLoc 𝒩 s n (hf.piece n m) :=
  Subtype.ext (awayMap_awayFrac (xProd R s) f 0 (m : M))

theorem homLocMap_homLocRes {f : M →ₗ[MvPolynomial ι R] N} (hf : IsGradedMap ℳ 𝒩 f)
    {s t : Finset ι} (h : s ⊆ t) (n : ℤ) (z : homLoc ℳ s n) :
    homLocMap hf t n (homLocRes ℳ h n z) = homLocRes 𝒩 h n (homLocMap hf s n z) :=
  Subtype.ext (awayMap_locRes X h f z.1)

theorem homLocMap_comp {g : N →ₗ[MvPolynomial ι R] P} {f : M →ₗ[MvPolynomial ι R] N}
    (hg : IsGradedMap 𝒩 𝒬 g) (hf : IsGradedMap ℳ 𝒩 f) (s : Finset ι) (n : ℤ) (z : homLoc ℳ s n) :
    homLocMap (hg.comp hf) s n z = homLocMap hg s n (homLocMap hf s n z) :=
  Subtype.ext congr($(awayMap_comp (xProd R s) g f) z.1)

@[simp]
theorem homLocMap_zero (h : IsGradedMap ℳ 𝒩 (0 : M →ₗ[MvPolynomial ι R] N))
    (s : Finset ι) (n : ℤ) (z : homLoc ℳ s n) : homLocMap h s n z = 0 :=
  Subtype.ext congr($(awayMap_zero (M := M) (N := N) (xProd R s)) z.1)

theorem homLocMap_injective_of {f : M →ₗ[MvPolynomial ι R] N} (hf : IsGradedMap ℳ 𝒩 f)
    {s : Finset ι} (h : ∀ m, f m = 0 → ∃ k : ℕ, xProd R s ^ k • m = 0) (n : ℤ) :
    Function.Injective (homLocMap hf s n) :=
  fun _ _ e => Subtype.ext (awayMap_injective_of h (congrArg Subtype.val e))

theorem homLocMap_injective {f : M →ₗ[MvPolynomial ι R] N} (hf : IsGradedMap ℳ 𝒩 f)
    (h : Function.Injective f) (s : Finset ι) (n : ℤ) : Function.Injective (homLocMap hf s n) :=
  homLocMap_injective_of hf
    (fun m hm => ⟨0, by rw [(map_eq_zero_iff f h).1 hm, smul_zero]⟩) n

variable [Decomposition ℳ] [Decomposition 𝒩]

theorem homLocMap_surjective_of {f : M →ₗ[MvPolynomial ι R] N} (hf : IsGradedMap ℳ 𝒩 f)
    {s : Finset ι} (h : ∀ y, ∃ k : ℕ, xProd R s ^ k • y ∈ LinearMap.range f) (n : ℤ) :
    Function.Surjective (homLocMap hf s n) :=
  (hf.awayMap s).surjective_iff.1 (awayMap_surjective_of h) n

theorem homLocMap_surjective {f : M →ₗ[MvPolynomial ι R] N} (hf : IsGradedMap ℳ 𝒩 f)
    (h : Function.Surjective f) (s : Finset ι) (n : ℤ) : Function.Surjective (homLocMap hf s n) :=
  homLocMap_surjective_of hf (fun _ => ⟨0, h _⟩) n

theorem homLocMap_exact {f : M →ₗ[MvPolynomial ι R] N} {g : N →ₗ[MvPolynomial ι R] P}
    (hf : IsGradedMap ℳ 𝒩 f) (hg : IsGradedMap 𝒩 𝒬 g) (h : Function.Exact f g) (s : Finset ι)
    (n : ℤ) : Function.Exact (homLocMap hf s n) (homLocMap hg s n) :=
  (hf.awayMap s).exact_piece (hg.awayMap s) (awayMap_exact _ h) n

theorem homLocMap_bijective_of_X {f : M →ₗ[MvPolynomial ι R] N} (hf : IsGradedMap ℳ 𝒩 f)
    {s : Finset ι} {i : ι} (hi : i ∈ s)
    (h₁ : ∀ m, f m = 0 → ∃ k : ℕ, (X i : MvPolynomial ι R) ^ k • m = 0)
    (h₂ : ∀ y, ∃ k : ℕ, (X i : MvPolynomial ι R) ^ k • y ∈ LinearMap.range f) (n : ℤ) :
    Function.Bijective (homLocMap hf s n) := by
  obtain ⟨c, hc⟩ : ∃ c, xProd R s = c * X i :=
    exists_eq_mul_left_of_dvd (Finset.dvd_prod_of_mem _ hi)
  refine ⟨homLocMap_injective_of hf (fun m hm => (h₁ m hm).imp fun k hk => ?_) n,
    homLocMap_surjective_of hf (fun y => (h₂ y).imp fun k hk => ?_) n⟩
  · rw [hc, mul_pow, mul_smul, hk, smul_zero]
  · rw [hc, mul_pow, mul_smul]
    exact Submodule.smul_mem _ _ hk

end HomLoc

section Lift

variable {ι : Type} {R : Type*} [CommRing R]
  {M : Type*} [AddCommGroup M] [Module R M] [Module (MvPolynomial ι R) M]
  [IsScalarTower R (MvPolynomial ι R) M] {ℳ : ℤ → Submodule R M} [PolyGradedSMul ι ℳ]
  {T : Type*} [AddCommGroup T] [Module R T] {s : Finset ι} {n : ℤ}
  (φ : ∀ k : ℕ, ℳ (n + k * s.card) →ₗ[R] T)
  (hφ : ∀ (k : ℕ) (m : ℳ (n + k * s.card)) (m' : ℳ (n + (k + 1 : ℕ) * s.card)),
    (m' : M) = xProd R s • (m : M) → φ (k + 1) m' = φ k m)
include hφ

omit [IsScalarTower R (MvPolynomial ι R) M] in
theorem homLocLift_pow (k j : ℕ) (m : ℳ (n + k * s.card)) :
    φ (k + j) ⟨_, xProd_pow_smul_mem ℳ m.2 j⟩ = φ k m := by
  induction j with
  | zero => exact congrArg (φ k) (Subtype.ext (by simp))
  | succ j ih => exact (hφ (k + j) _ _ (by simp [pow_succ', mul_smul])).trans ih

theorem homLocLift_congr {k j : ℕ} {m : ℳ (n + k * s.card)} {m' : ℳ (n + j * s.card)}
    (h : homLocMk ℳ s n k m = homLocMk ℳ s n j m') : φ k m = φ j m' := by
  obtain ⟨l, hl⟩ := awayFrac_eq_iff.1 (congrArg Subtype.val h)
  have key : ∀ (a b : ℕ) (_ : a = b) (x : ℳ (n + a * s.card)) (y : ℳ (n + b * s.card)),
      (x : M) = y → φ a x = φ b y := by
    rintro a _ rfl x y e
    rw [Subtype.ext e]
  rw [← homLocLift_pow φ hφ k (l + j), ← homLocLift_pow φ hφ j (l + k)]
  exact key _ _ (by ring) _ _ hl

def homLocLift : homLoc ℳ s n →ₗ[R] T :=
  have key (k : ℕ) (m : ℳ (n + k * s.card)) :
      φ _ (exists_homLocMk (homLocMk ℳ s n k m)).choose_spec.choose = φ k m :=
    homLocLift_congr φ hφ (exists_homLocMk (homLocMk ℳ s n k m)).choose_spec.choose_spec
  { toFun z := φ _ (exists_homLocMk z).choose_spec.choose
    map_add' z w := by
      obtain ⟨a, ha⟩ := exists_awayFrac_of_mem_homLoc ℳ z.2
      obtain ⟨b, hb⟩ := exists_awayFrac_of_mem_homLoc ℳ w.2
      obtain ⟨x, hx, ex⟩ := ha (max a b) (le_max_left _ _)
      obtain ⟨y, hy, ey⟩ := hb (max a b) (le_max_right _ _)
      obtain rfl : homLocMk ℳ s n _ ⟨x, hx⟩ = z := Subtype.ext ex
      obtain rfl : homLocMk ℳ s n _ ⟨y, hy⟩ = w := Subtype.ext ey
      rw [← map_add (f := _), key, key, key, map_add (f := _)]
    map_smul' r z := by
      obtain ⟨k, m, rfl⟩ := exists_homLocMk z
      rw [← map_smul, key, key, map_smul, RingHom.id_apply] }

@[simp]
theorem homLocLift_homLocMk (k : ℕ) (m : ℳ (n + k * s.card)) :
    homLocLift φ hφ (homLocMk ℳ s n k m) = φ k m :=
  homLocLift_congr φ hφ (exists_homLocMk (homLocMk ℳ s n k m)).choose_spec.choose_spec

theorem homLocLift_injective_iff : Function.Injective (homLocLift φ hφ) ↔
    ∀ k m, φ k m = 0 → ∃ l : ℕ, xProd R s ^ l • (m : M) = 0 := by
  rw [injective_iff_map_eq_zero]
  constructor
  · intro h k m hm
    exact awayFrac_eq_zero_iff.1
      (congrArg Subtype.val (h _ ((homLocLift_homLocMk φ hφ k m).trans hm)))
  · intro h z hz
    obtain ⟨k, m, rfl⟩ := exists_homLocMk z
    exact Subtype.ext (awayFrac_eq_zero_iff.2 (h k m ((homLocLift_homLocMk φ hφ k m).symm.trans hz)))

theorem homLocLift_surjective_iff : Function.Surjective (homLocLift φ hφ) ↔
    ∀ t, ∃ k m, φ k m = t := by
  refine forall_congr' fun t => ⟨?_, ?_⟩
  · rintro ⟨z, rfl⟩
    obtain ⟨k, m, rfl⟩ := exists_homLocMk z
    exact ⟨k, m, (homLocLift_homLocMk φ hφ k m).symm⟩
  · rintro ⟨k, m, rfl⟩
    exact ⟨_, homLocLift_homLocMk φ hφ k m⟩

end Lift

section Pi

variable {ι : Type} {R : Type*} [CommRing R] {κ : Type*} [Finite κ]
  {M : κ → Type*} [∀ k, AddCommGroup (M k)] [∀ k, Module R (M k)]
  [∀ k, Module (MvPolynomial ι R) (M k)] [∀ k, IsScalarTower R (MvPolynomial ι R) (M k)]
  (ℳ : ∀ k, ℤ → Submodule R (M k)) [∀ k, PolyGradedSMul ι (ℳ k)]

theorem homLocMap_piProj_bijective (s : Finset ι) (n : ℤ) :
    Function.Bijective (LinearMap.pi fun k => homLocMap (isGradedMap_piProj (ι := ι) ℳ k) s n) := by
  classical
  have := Fintype.ofFinite κ
  constructor
  · rw [injective_iff_map_eq_zero]
    intro z hz
    obtain ⟨j, m, rfl⟩ := exists_homLocMk z
    have h (k : κ) : ∃ l : ℕ, xProd R s ^ l • m.1 k = 0 := by
      have := congrFun hz k
      rw [LinearMap.pi_apply, homLocMap_homLocMk] at this
      exact awayFrac_eq_zero_iff.1 (congrArg Subtype.val this)
    choose l hl using h
    refine Subtype.ext ((coe_homLocMk _ s n j m).trans
      (awayFrac_eq_zero_iff.2 ⟨Finset.univ.sup l, funext fun k => ?_⟩))
    obtain ⟨c, hc⟩ := Nat.exists_eq_add_of_le' (Finset.le_sup (f := l) (Finset.mem_univ k))
    rw [Pi.smul_apply, hc, pow_add, mul_smul, hl, smul_zero, Pi.zero_apply]
  · intro z
    choose j hj using fun k => exists_awayFrac_of_mem_homLoc (ℳ k) (z k).2
    choose m hm e using fun k => hj k (Finset.univ.sup j) (Finset.le_sup (Finset.mem_univ k))
    refine ⟨homLocMk _ s n _ ⟨m, mem_grPi.2 hm⟩, funext fun k => ?_⟩
    rw [LinearMap.pi_apply, homLocMap_homLocMk]
    exact Subtype.ext (e k)

def homLocPiEquiv (s : Finset ι) (n : ℤ) :
    homLoc (grPi ℳ) s n ≃ₗ[R] ∀ k, homLoc (ℳ k) s n :=
  LinearEquiv.ofBijective _ (homLocMap_piProj_bijective ℳ s n)

end Pi

section Cech

variable (ι : Type) {R : Type u} [CommRing R]
  {M : Type u} [AddCommGroup M] [Module R M] [Module (MvPolynomial ι R) M]
  [IsScalarTower R (MvPolynomial ι R) M]
  {N : Type u} [AddCommGroup N] [Module R N] [Module (MvPolynomial ι R) N]
  [IsScalarTower R (MvPolynomial ι R) N]
  {P : Type u} [AddCommGroup P] [Module R P] [Module (MvPolynomial ι R) P]
  [IsScalarTower R (MvPolynomial ι R) P]
  (ℳ : ℤ → Submodule R M) [PolyGradedSMul ι ℳ] {𝒩 : ℤ → Submodule R N} [PolyGradedSMul ι 𝒩]
  {𝒬 : ℤ → Submodule R P} [PolyGradedSMul ι 𝒬]

def grCube (n : ℤ) : Cube.{u} ι R :=
  Cube.mk (fun s => ModuleCat.of R (homLoc ℳ s n)) (fun h => homLocRes ℳ h n)
    (fun _ => homLocRes_self ℳ _ n) fun h h' => homLocRes_homLocRes ℳ h h' n

def grCech [LinearOrder ι] (n : ℤ) : CochainComplex (ModuleCat.{u} R) ℕ :=
  cechComplex (grCube ι ℳ n)

abbrev grH [LinearOrder ι] (n : ℤ) (p : ℕ) : ModuleCat.{u} R := (grCech ι ℳ n).homology p

variable {ι}

theorem res_grCube (n : ℤ) {s t : Finset ι} (h : s ⊆ t) :
    Cube.res (grCube ι ℳ n) h = homLocRes ℳ h n := rfl

def grCubeShiftIso (d n : ℤ) : grCube ι (grShift ℳ d) n ≅ grCube ι ℳ (n + d) :=
  Cube.isoMk (fun s => LinearEquiv.ofEq _ _ (homLoc_grShift ℳ d s n)) fun _ _ => rfl

variable {ℳ}

def grCubeMap {f : M →ₗ[MvPolynomial ι R] N} (hf : IsGradedMap ℳ 𝒩 f) (n : ℤ) :
    grCube ι ℳ n ⟶ grCube ι 𝒩 n :=
  Cube.homMk ι R (fun s => homLocMap hf s n) fun h => homLocMap_homLocRes hf h n

theorem grCubeMap_comp {g : N →ₗ[MvPolynomial ι R] P} {f : M →ₗ[MvPolynomial ι R] N}
    (hg : IsGradedMap 𝒩 𝒬 g) (hf : IsGradedMap ℳ 𝒩 f) (n : ℤ) :
    grCubeMap (hg.comp hf) n = grCubeMap hf n ≫ grCubeMap hg n :=
  NatTrans.ext (funext fun s => ModuleCat.hom_ext (LinearMap.ext (homLocMap_comp hg hf s n)))

@[simp]
theorem grCubeMap_zero (h : IsGradedMap ℳ 𝒩 (0 : M →ₗ[MvPolynomial ι R] N)) (n : ℤ) :
    grCubeMap h n = 0 :=
  NatTrans.ext (funext fun s => ModuleCat.hom_ext (LinearMap.ext (homLocMap_zero h s n)))

theorem grCubeMap_congr {f g : M →ₗ[MvPolynomial ι R] N} (hf : IsGradedMap ℳ 𝒩 f)
    (hg : IsGradedMap ℳ 𝒩 g) (h : f = g) (n : ℤ) : grCubeMap hf n = grCubeMap hg n := by
  subst h; rfl

variable [LinearOrder ι]

variable (ℳ) in
theorem grCech_eq (n : ℤ) : grCech ι ℳ n = cechComplex (grCube ι ℳ n) := rfl

variable (ℳ) in
theorem grCech_d (n : ℤ) (p : ℕ) :
    (grCech ι ℳ n).d p (p + 1) = ModuleCat.ofHom (Cube.d (grCube ι ℳ n) (p + 1)) :=
  cechComplex_d _ p

def grCechMap {f : M →ₗ[MvPolynomial ι R] N} (hf : IsGradedMap ℳ 𝒩 f) (n : ℤ) :
    grCech ι ℳ n ⟶ grCech ι 𝒩 n := cechComplexMap (grCubeMap hf n)

abbrev grHMap {f : M →ₗ[MvPolynomial ι R] N} (hf : IsGradedMap ℳ 𝒩 f) (n : ℤ) (p : ℕ) :
    grH ι ℳ n p ⟶ grH ι 𝒩 n p := HomologicalComplex.homologyMap (grCechMap hf n) p

theorem isIso_grCechMap [Decomposition ℳ] [Decomposition 𝒩] {f : M →ₗ[MvPolynomial ι R] N}
    (hf : IsGradedMap ℳ 𝒩 f)
    (h₁ : ∀ (i : ι) m, f m = 0 → ∃ k : ℕ, (X i : MvPolynomial ι R) ^ k • m = 0)
    (h₂ : ∀ (i : ι) y, ∃ k : ℕ, (X i : MvPolynomial ι R) ^ k • y ∈ LinearMap.range f) (n : ℤ) :
    IsIso (grCechMap hf n) :=
  isIso_cechComplexMap _ fun _ ⟨i, hi⟩ => homLocMap_bijective_of_X hf hi (h₁ i) (h₂ i) n



variable (ι ℳ) in
def grAug (n : ℤ) : ℳ n →ₗ[R] grH ι ℳ n 0 :=
  (cechAugHomology (grCube ι ℳ n)).hom ∘ₗ toHomLoc ℳ ∅ n

variable (ℳ) in
theorem cechHomologyZeroIso_grAug (n : ℤ) (m : ℳ n) (s : {s : Finset ι // s.card = 1}) :
    ((cechHomologyZeroIso (grCube ι ℳ n)).hom.hom (grAug ι ℳ n m)).1 s = toHomLoc ℳ s.1 n m :=
  (congrFun congr(($(cechAugHomology_comp (grCube ι ℳ n))).hom (toHomLoc ℳ ∅ n m)) s).trans
    (homLocRes_toHomLoc ℳ _ n m)

theorem grHMap_grAug {f : M →ₗ[MvPolynomial ι R] N} (hf : IsGradedMap ℳ 𝒩 f) (n : ℤ) (m : ℳ n) :
    (grHMap hf n 0).hom (grAug ι ℳ n m) = grAug ι 𝒩 n (hf.piece n m) :=
  congr(($(cechAugHomology_naturality (grCubeMap hf n))).hom (toHomLoc ℳ ∅ n m)).symm.trans
    (congrArg (cechAugHomology (grCube ι 𝒩 n)).hom (homLocMap_toHomLoc hf ∅ n m))

variable (ℳ) in
theorem grAug_bijective_iff (n : ℤ) : Function.Bijective (grAug ι ℳ n) ↔
    (cubeComplex (grCube ι ℳ n)).ExactAt 0 ∧ (cubeComplex (grCube ι ℳ n)).ExactAt 1 := by
  rw [← isIso_cechAugHomology_iff, ConcreteCategory.isIso_iff_bijective]
  exact Function.Bijective.of_comp_iff (cechAugHomology (grCube ι ℳ n)).hom
    (g := toHomLoc ℳ ∅ n) (homLocEmptyEquiv ι ℳ n).bijective

end Cech

section ShortExactDef

variable {ι : Type} {R : Type*} [CommRing R]
  {M : Type*} [AddCommGroup M] [Module R M] [Module (MvPolynomial ι R) M]
  {N : Type*} [AddCommGroup N] [Module R N] [Module (MvPolynomial ι R) N]
  {P : Type*} [AddCommGroup P] [Module R P] [Module (MvPolynomial ι R) P]

structure GradedShortExact (ℳ : ℤ → Submodule R M) (𝒩 : ℤ → Submodule R N)
    (𝒬 : ℤ → Submodule R P) (f : M →ₗ[MvPolynomial ι R] N) (g : N →ₗ[MvPolynomial ι R] P) :
    Prop where

  graded_f : IsGradedMap ℳ 𝒩 f

  graded_g : IsGradedMap 𝒩 𝒬 g

  injective : Function.Injective f

  exact : Function.Exact f g

  surjective : Function.Surjective g

variable [IsScalarTower R (MvPolynomial ι R) M] [IsScalarTower R (MvPolynomial ι R) N]
  [IsScalarTower R (MvPolynomial ι R) P]

omit [IsScalarTower R (MvPolynomial ι R) P] in
theorem IsGradedMap.shortExact_ker {𝒩 : ℤ → Submodule R N} {𝒬 : ℤ → Submodule R P}
    {g : N →ₗ[MvPolynomial ι R] P} (hg : IsGradedMap 𝒩 𝒬 g) (h : Function.Surjective g) :
    GradedShortExact (grSub 𝒩 (LinearMap.ker g)) 𝒩 𝒬 (LinearMap.ker g).subtype g :=
  ⟨isGradedMap_subtype _ _, hg, Submodule.injective_subtype _, LinearMap.exact_subtype_ker_map g, h⟩

theorem GradedShortExact.homLoc {ℳ : ℤ → Submodule R M} {𝒩 : ℤ → Submodule R N}
    {𝒬 : ℤ → Submodule R P} [PolyGradedSMul ι ℳ] [PolyGradedSMul ι 𝒩] [PolyGradedSMul ι 𝒬]
    [Decomposition ℳ] [Decomposition 𝒩] [Decomposition 𝒬]
    {f : M →ₗ[MvPolynomial ι R] N} {g : N →ₗ[MvPolynomial ι R] P}
    (h : GradedShortExact ℳ 𝒩 𝒬 f g) (s : Finset ι) (n : ℤ) :
    Function.Injective (homLocMap h.graded_f s n) ∧
      Function.Exact (homLocMap h.graded_f s n) (homLocMap h.graded_g s n) ∧
      Function.Surjective (homLocMap h.graded_g s n) :=
  ⟨homLocMap_injective _ h.injective s n, homLocMap_exact _ _ h.exact s n,
    homLocMap_surjective _ h.surjective s n⟩

end ShortExactDef

namespace GradedShortExact

variable {ι : Type} {R : Type u} [CommRing R]
  {M : Type u} [AddCommGroup M] [Module R M] [Module (MvPolynomial ι R) M]
  [IsScalarTower R (MvPolynomial ι R) M]
  {N : Type u} [AddCommGroup N] [Module R N] [Module (MvPolynomial ι R) N]
  [IsScalarTower R (MvPolynomial ι R) N]
  {P : Type u} [AddCommGroup P] [Module R P] [Module (MvPolynomial ι R) P]
  [IsScalarTower R (MvPolynomial ι R) P]
  {ℳ : ℤ → Submodule R M} [PolyGradedSMul ι ℳ] {𝒩 : ℤ → Submodule R N} [PolyGradedSMul ι 𝒩]
  {𝒬 : ℤ → Submodule R P} [PolyGradedSMul ι 𝒬]
  {f : M →ₗ[MvPolynomial ι R] N} {g : N →ₗ[MvPolynomial ι R] P} (h : GradedShortExact ℳ 𝒩 𝒬 f g)

abbrev cubes (n : ℤ) : ShortComplex (Cube.{u} ι R) :=
  ShortComplex.mk (grCubeMap h.graded_f n) (grCubeMap h.graded_g n) (by
    rw [← grCubeMap_comp, grCubeMap_congr _ (IsGradedMap.zero (ι := ι) (ℳ := ℳ) (𝒩 := 𝒬))
      h.exact.linearMap_comp_eq_zero, grCubeMap_zero])

variable [LinearOrder ι]

variable [Decomposition ℳ] [Decomposition 𝒩] [Decomposition 𝒬]

omit [LinearOrder ι] in
theorem cubes_shortExact (n : ℤ) (s : Finset ι) :
    ((h.cubes n).map ((evaluation _ _).obj s)).ShortExact :=
  ModuleCat.shortComplex_shortExact _ (h.homLoc s n).2.1 (h.homLoc s n).1 (h.homLoc s n).2.2

theorem cubeComplex_shortExact (n : ℤ) : ((h.cubes n).map (cubeFunctor ι R)).ShortExact :=
  cubeFunctor_shortExact _ (h.cubes_shortExact n)

end GradedShortExact

section PiCech

variable {ι : Type} {R : Type u} [CommRing R] {κ : Type} [Fintype κ]
  {M : κ → Type u} [∀ k, AddCommGroup (M k)] [∀ k, Module R (M k)]
  [∀ k, Module (MvPolynomial ι R) (M k)] [∀ k, IsScalarTower R (MvPolynomial ι R) (M k)]
  (ℳ : ∀ k, ℤ → Submodule R (M k)) [∀ k, PolyGradedSMul ι (ℳ k)]

variable (ι) in
def grCubePiIso (n : ℤ) : grCube ι (grPi ℳ) n ≅ Cube.directSum fun k => grCube ι (ℳ k) n :=
  Cube.isoMk (fun s => homLocPiEquiv ℳ s n ≪≫ₗ
      (DirectSum.linearEquivFunOnFintype R κ fun k => homLoc (ℳ k) s n).symm)
    fun h z => DFinsupp.ext fun k => homLocMap_homLocRes (isGradedMap_piProj (ι := ι) ℳ k) h n z

variable [LinearOrder ι]


variable [Finite ι]

theorem cubeComplex_grPi_exactAt_iff (n : ℤ) (p : ℕ) :
    (cubeComplex (grCube ι (grPi ℳ) n)).ExactAt p ↔
      ∀ k, (cubeComplex (grCube ι (ℳ k) n)).ExactAt p := by
  classical
  exact (exactAt_iff_of_quasiIsoAt
    ((cubeFunctor ι R).mapIso (grCubePiIso ι ℳ n)).hom p).trans
    (cubeComplex_directSum_exactAt_iff _ p)

end PiCech

section Examples

variable {ι : Type} {R : Type u} [CommRing R]

theorem xProd_smul_injective (s : Finset ι) :
    Function.Injective fun p : MvPolynomial ι R => xProd R s • p :=
  (IsRegular.prod fun _ _ => MvPolynomial.isRegular_X).left

variable (ι R) in
theorem operatorsCommute_id :
    OperatorsCommute (ι := ι) (R := R) (A := fun _ => R) fun _ _ => LinearMap.id :=
  fun _ _ _ _ => rfl

end Examples

end GlobalTheory
