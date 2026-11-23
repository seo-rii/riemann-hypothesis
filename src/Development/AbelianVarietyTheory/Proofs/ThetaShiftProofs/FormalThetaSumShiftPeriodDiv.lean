module

public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.CoeffFSumDerivEqFderiv
public import Mathlib.Analysis.Fourier.AddCircleMulti
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.CStarAlgebra.ContinuousMap
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
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
import Mathlib.Topology.Algebra.ProperAction.Basic
import Mathlib.Topology.Compactness.CompactlyGeneratedSpace
import Mathlib.Topology.Separation.CompletelyRegular

@[expose] public section

noncomputable section

namespace GlobalTheory

open ReciprocityTheory.ChartRestriction.G.Geo.Tor (hermForm eTwoPi)

section Fourier

open MeasureTheory UnitAddTorus

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩

local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

theorem eq_zero_of_tsum_mFourier {d : Type} [Fintype d] {f : (d → ℤ) → ℂ} (hf : Summable f)
    (h : ∀ x : UnitAddTorus d, ∑' n, f n * mFourier n x = 0) : f = 0 := by
  classical
  have hs : Summable fun n => f n • mFourier n :=
    Summable.of_norm (by simpa only [norm_smul, mFourier_norm, mul_one] using hf.norm)
  have h0 : ∑' n, f n • mFourier n = 0 := by
    ext x
    have := ((ContinuousMap.evalCLM ℂ x).hasSum hs.hasSum).tsum_eq
    exact this.symm.trans (h x)
  have h1 : HasSum (fun n => f n • mFourier n) 0 := h0 ▸ hs.hasSum
  funext m
  have h2 := (innerSL ℂ (mFourierLp (d := d) 2 m)).hasSum
    ((ContinuousMap.toLp (E := ℂ) 2 (volume : Measure (UnitAddTorus d)) ℂ).hasSum h1)
  simp only [map_smul, map_zero, innerSL_apply_apply, orthonormal_iff_ite.1 orthonormal_mFourier,
    smul_eq_mul] at h2
  have h3 : HasSum (fun n => f n * if m = n then (1 : ℂ) else 0) (f m) := by
    convert hasSum_ite_eq m (f m) using 2 with n
    by_cases hn : n = m
    · simp [hn]
    · simp [hn, Ne.symm hn]
  exact h3.unique h2

end Fourier

namespace AnArc

variable {O : Type} [CommRing O] [StarRing O] (A : AnArc O)

theorem e_def (x : ℂ) : eTwoPi x = Complex.exp (2 * Real.pi * Complex.I * x) := rfl

theorem chi_ne_zero (l : A.abelian₂) : A.chi l ≠ 0 := fun h => by
  have := A.chi_norm l
  simp [h] at this

theorem H_sub_H (l m : A.abelian₂) : A.H l m - A.H m l = 2 * Complex.I * A.Ef l m := by
  have h : ((A.Ef l m : ℤ) : ℂ) = ((A.H l m).im : ℂ) := by rw [← Ef_eq_im]; simp
  rw [h, ← A.H_conj l m, Complex.sub_conj]
  push_cast; ring

def lin (la : A.La) : A.V →ₗ[ℂ] ℂ where
  toFun v := Real.pi * A.H v.2 la.l - 2 * Real.pi * Complex.I * v.1 la.y
  map_add' v v' := by simp only [Prod.snd_add, Prod.fst_add, H_add_left, AddMonoidHom.add_apply]; ring
  map_smul' c v := by
    simp only [Prod.smul_snd, Prod.smul_fst, H_smul_left, AddMonoidHom.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

theorem lin_apply (la : A.La) (v : A.V) :
    A.lin la v = Real.pi * A.H v.2 la.l - 2 * Real.pi * Complex.I * v.1 la.y := rfl

theorem exp_lin (la : A.La) (v : A.V) :
    Complex.exp (A.lin la v) = Complex.exp (Real.pi * A.H v.2 la.l) / eTwoPi (v.1 la.y) := by
  rw [lin_apply, Complex.exp_sub, e_def]

theorem lin_Pw_sub (w : ℂ) (la la' : A.La) :
    A.lin la (A.Pw w la') - A.lin la' (A.Pw w la) = -(2 * Real.pi * Complex.I * A.EF la la') := by
  have h2 := A.H_sub_H la.l la'.l
  have hI := Complex.I_ne_zero
  simp only [lin_apply, Pw_snd, Pw_fst_apply, H_add_left, EF_apply, A.T_symm la'.y la.y, A.be_symm la'.y la.y]
  push_cast
  have h3 : ∀ x : ℂ, x / (2 * Complex.I) = -(Complex.I * x / 2) := fun x => by
    field_simp; simp
  simp only [h3]
  linear_combination (-Real.pi : ℂ) * h2 +
    (Real.pi * (A.H (A.ct la'.y) la.l - A.H (A.ct la.y) la'.l) : ℂ) * Complex.I_mul_I

theorem Pw_zero : A.Pw 0 = A.P0 := by simp [Pw]

theorem linear_part_commutator_period (la la' : A.La) :
    A.lin la (A.P0 la') - A.lin la' (A.P0 la) = -(2 * Real.pi * Complex.I * A.EF la la') := by
  rw [← Pw_zero, lin_Pw_sub]

def logConst (w : ℂ) (la : A.La) : ℂ :=
  Complex.log (A.chi la.l) - Complex.log (A.psi la.y) + Real.pi * A.H (A.ct la.y) la.l +
    Real.pi / 2 * A.H la.l la.l - 2 * Real.pi * Complex.I * (w * A.q la.y)

def L (w : ℂ) (la : A.La) (v : A.V) : ℂ := A.lin la v + A.logConst w la

theorem L_apply (w : ℂ) (la : A.La) (v : A.V) : A.L w la v = A.lin la v + A.logConst w la := rfl

theorem perFactor_eq_exp (w : ℂ) (la : A.La) (v : A.V) : A.perFactor w la v = Complex.exp (A.L w la v) := by
  rw [perFactor, ah, L, logConst, lin_apply, H_add_left]
  simp only [Complex.exp_add, Complex.exp_sub, mul_add, Complex.exp_log (A.chi_ne_zero _),
    Complex.exp_log (A.psi _).ne_zero, e_def]
  ring

theorem term_add (j : ℕ) (α : A.X) (th th' : (Fin A.gB → ℂ) → ℂ) (μ : A.X) (v : A.V) :
    A.term j α (th + th') μ v = A.term j α th μ v + A.term j α th' μ v := by
  simp only [term, Pi.add_apply]; ring

theorem term_smul (j : ℕ) (α : A.X) (c : ℂ) (th : (Fin A.gB → ℂ) → ℂ) (μ : A.X) (v : A.V) :
    A.term j α (c • th) μ v = c * A.term j α th μ v := by
  simp only [term, Pi.smul_apply, smul_eq_mul]; ring

theorem FSum_smul (j : ℕ) [NeZero j] (α : A.X) (c : ℂ) (th : (Fin A.gB → ℂ) → ℂ) (v : A.V) :
    A.FSum j α (c • th) v = c • A.FSum j α th v := by
  ext n
  simp only [coeff_FSum, HahnSeries.coeff_smul, smul_eq_mul, term_smul, Finset.mul_sum]

theorem FSum_add (j : ℕ) [NeZero j] (α : A.X) (th th' : (Fin A.gB → ℂ) → ℂ) (v : A.V) :
    A.FSum j α (th + th') v = A.FSum j α th v + A.FSum j α th' v := by
  ext n
  simp only [coeff_FSum, HahnSeries.coeff_add, term_add, Finset.sum_add_distrib]

theorem exponent_add (j : ℕ) (α μ y : A.X) :
    A.exponent j α (μ + y) = A.exponent j (α + j • y) μ + A.exponent j α y := by
  simp [exponent, q_add]; ring

theorem term_add_index (j : ℕ) (α : A.X) (th : (Fin A.gB → ℂ) → ℂ) (μ y : A.X) (v : A.V) :
    A.term j α th (μ + y) v =
      (A.psi y : ℂ) ^ j * eTwoPi (A.T y α) * A.term j (α + j • y) (fun z => th (z + A.ct y)) μ v := by
  have h1 : α + j • (μ + y) = α + j • y + j • μ := by rw [smul_add]; abel
  rw [term, term, h1, psi_add, map_add A.ct, add_assoc v.2, map_add A.T, AddMonoidHom.add_apply,
    map_add (A.T μ), map_nsmul (A.T μ), nsmul_eq_mul]
  simp only [e_add, e_nat_mul, mul_pow]
  ring

theorem FSum_eq_translate (j : ℕ) [NeZero j] (α : A.X) (th : (Fin A.gB → ℂ) → ℂ) (y : A.X) (v : A.V) :
    A.FSum j α th v = HahnSeries.single (A.exponent j α y) ((A.psi y : ℂ) ^ j * eTwoPi (A.T y α)) *
      A.FSum j (α + j • y) (fun z => th (z + A.ct y)) v := by
  ext n
  obtain ⟨n, rfl⟩ : ∃ m, n = m + A.exponent j α y := ⟨n - _, (sub_add_cancel _ _).symm⟩
  rw [HahnSeries.coeff_single_mul_add, coeff_FSum, coeff_FSum, Finset.mul_sum]
  symm
  refine Finset.sum_equiv (Equiv.addRight y) (fun μ => ?_) fun μ _ => ?_
  · simp [exponent_add]
  · rw [Equiv.coe_addRight, term_add_index]

section Shift

variable (k : ℕ) [NeZero k]

def shift (k : ℕ) [NeZero k] (la : A.La) (α : A.X) : ((Fin A.gB → ℂ) → ℂ) →ₗ[ℂ] ((Fin A.gB → ℂ) → ℂ) where
  toFun th z := eTwoPi ((A.P0 la).1 α / k) * Complex.exp (-(Real.pi * A.H z la.l)) *
    th (z + (k : ℂ)⁻¹ • (A.P0 la).2)
  map_add' th th' := by funext z; simp only [Pi.add_apply]; ring
  map_smul' c th := by funext z; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring

theorem shift_apply' (la : A.La) (α : A.X) (th : (Fin A.gB → ℂ) → ℂ) (z : Fin A.gB → ℂ) :
    A.shift k la α th z = eTwoPi ((A.P0 la).1 α / k) * Complex.exp (-(Real.pi * A.H z la.l)) *
      th (z + (k : ℂ)⁻¹ • (A.P0 la).2) := rfl

theorem shift_apply (la : A.La) (α : A.X) (th : (Fin A.gB → ℂ) → ℂ) (z : Fin A.gB → ℂ) :
    A.shift k la α th z = eTwoPi ((A.T la.y α + la.n α - A.H (A.ct α) la.l / (2 * Complex.I)) / k) *
      Complex.exp (-(Real.pi * A.H z la.l)) * th (z + (k : ℂ)⁻¹ • (A.ct la.y + la.l)) := rfl


variable {k} in
theorem shift_mem_Theta {α : A.X} {th : (Fin A.gB → ℂ) → ℂ} (h : th ∈ A.Theta k α) (la : A.La) :
    A.shift k la α th ∈ A.Theta k (α + la.y) := by
  have hk : (k : ℂ) ≠ 0 := NeZero.ne _
  refine ⟨?_, fun m z => ?_⟩
  · have h1 : Differentiable ℂ fun z : Fin A.gB → ℂ => A.H z la.l := by
      unfold H hermForm dotProduct; fun_prop
    have h2 := h.1
    change Differentiable ℂ fun z => eTwoPi ((A.P0 la).1 α / k) * Complex.exp (-(Real.pi * A.H z la.l)) *
      th (z + (k : ℂ)⁻¹ • (A.P0 la).2)
    fun_prop
  · have h2 := A.H_sub_H la.l m
    have h3 : Complex.exp (-(Real.pi * (A.H z la.l + A.H m la.l))) *
        Complex.exp (k * (Real.pi * ((k : ℂ)⁻¹ * (A.H (A.ct la.y) m + A.H la.l m)))) *
        Complex.exp (Real.pi * A.H (A.ct α) m) =
        Complex.exp (Real.pi * (A.H (A.ct α) m + A.H (A.ct la.y) m)) * Complex.exp (-(Real.pi * A.H z la.l)) := by
      simp only [← Complex.exp_add]
      rw [Complex.exp_eq_exp_iff_exists_int, mul_left_comm (k : ℂ), mul_inv_cancel_left₀ hk]
      exact ⟨A.Ef la.l m, by linear_combination (Real.pi : ℂ) * h2⟩
    rw [shift_apply', shift_apply', add_right_comm, h.2, ah_add, mul_pow, ← Complex.exp_nat_mul, degeneratingTori_basePeriodMap_snd,
      H_smul_left, map_add, H_add_left, H_add_left, H_add_left]
    linear_combination (eTwoPi ((A.P0 la).1 α / k) * A.ah m z ^ k * th (z + (k : ℂ)⁻¹ • (A.ct la.y + la.l))) * h3

@[simp] theorem shift_zero (α : A.X) (th : (Fin A.gB → ℂ) → ℂ) : A.shift k 0 α th = th := by
  funext z; simp [shift_apply]

theorem shift_shift (la la' : A.La) (α : A.X) (th : (Fin A.gB → ℂ) → ℂ) :
    A.shift k la (α + la'.y) (A.shift k la' α th) =
      Complex.exp (-(A.lin la' (A.P0 la) / k)) • A.shift k (la + la') α th := by
  funext z
  have h1 : z + (k : ℂ)⁻¹ • (A.P0 la).2 + (k : ℂ)⁻¹ • (A.P0 la').2 = z + (k : ℂ)⁻¹ • (A.P0 (la + la')).2 := by
    rw [map_add (f := _), Prod.snd_add, smul_add, add_assoc]
  rw [Pi.smul_apply, smul_eq_mul, shift_apply', shift_apply', shift_apply', h1, ← mul_assoc _ _ (th _), ← mul_assoc _ _ (th _)]
  congr 1
  rw [map_add A.P0, Prod.fst_add, AddMonoidHom.add_apply, map_add (f := _), lin_apply, La.add_l, Submodule.coe_add,
    H_add_left, H_add_right, H_smul_left]
  simp only [e_def, ← Complex.exp_add]
  congr 1; ring

theorem shift_comm (la la' : A.La) (α : A.X) (th : (Fin A.gB → ℂ) → ℂ) :
    A.shift k la (α + la'.y) (A.shift k la' α th) =
      eTwoPi (-(A.EF la la' / k)) • A.shift k la' (α + la.y) (A.shift k la α th) := by
  rw [shift_shift, shift_shift, smul_smul, add_comm la' la, e_def, ← Complex.exp_add]
  congr 2
  linear_combination (k : ℂ)⁻¹ * A.linear_part_commutator_period la la'

theorem shift_injective (la : A.La) (α : A.X) : Function.Injective (A.shift k la α) := by
  rw [injective_iff_map_eq_zero]
  intro th h
  have := A.shift_shift k (-la) la α th
  rw [h, map_zero, neg_add_cancel, shift_zero] at this
  exact (smul_eq_zero.1 this.symm).resolve_left (Complex.exp_ne_zero _)

theorem term_add_P0_div (la : A.La) (α : A.X) (th : (Fin A.gB → ℂ) → ℂ) (μ : A.X) (v : A.V) :
    A.term k α th μ (v + (k : ℂ)⁻¹ • A.P0 la) =
      Complex.exp (A.lin la v) * A.term k (α + la.y) (A.shift k la α th) μ v := by
  have hk : (k : ℂ) ≠ 0 := NeZero.ne _
  have h1 : (v + (k : ℂ)⁻¹ • A.P0 la).1 (α + k • μ) = v.1 (α + k • μ) + (A.P0 la).1 α / k + A.T μ la.y +
      la.n μ + -(A.H (A.ct μ) la.l / (2 * Complex.I)) := by
    rw [Prod.fst_add, AddMonoidHom.add_apply, Prod.smul_fst, AddMonoidHom.smul_apply, map_add (A.P0 la).1,
      map_nsmul, degeneratingTori_basePeriodMap_fst_apply A la μ, A.T_symm μ, smul_eq_mul, nsmul_eq_mul, mul_add, inv_mul_cancel_left₀ hk]
    ring
  have h2 : (v + (k : ℂ)⁻¹ • A.P0 la).2 + A.ct μ = v.2 + A.ct μ + (k : ℂ)⁻¹ • (A.P0 la).2 := by
    rw [Prod.snd_add, Prod.smul_snd]; abel
  have h3 : v.1 (α + la.y + k • μ) = v.1 (α + k • μ) + v.1 la.y := by
    rw [add_right_comm, map_add (f := _)]
  rw [term, term, h1, h2, h3, shift_apply', exp_lin, map_add (A.T μ), H_add_left]
  simp only [e_add, e_intCast, e_neg_div, mul_add, neg_add, Complex.exp_add, Complex.exp_neg]
  have := e_ne_zero (v.1 la.y)
  have := Complex.exp_ne_zero (Real.pi * A.H v.2 la.l)
  field_simp


omit [NeZero k] in
theorem exponent_add_weight (α y μ : A.X) : A.exponent k (α + y) μ = A.exponent k α μ + A.be y μ := by
  rw [exponent, exponent, map_add (f := _), A.be_symm μ y, add_assoc]

theorem term_add_Pw_div (w : ℂ) (la : A.La) (α : A.X) (th : (Fin A.gB → ℂ) → ℂ) (μ : A.X) (v : A.V) :
    A.term k α th μ (v + (k : ℂ)⁻¹ • A.Pw w la) * eTwoPi (w * A.exponent k α μ) =
      Complex.exp (A.lin la v) * eTwoPi (w * A.be la.y α / k) *
        (A.term k (α + la.y) (A.shift k la α th) μ v * eTwoPi (w * A.exponent k (α + la.y) μ)) := by
  have hk : (k : ℂ) ≠ 0 := NeZero.ne _
  have h1 : (v + (k : ℂ)⁻¹ • A.Pw w la).1 (α + k • μ) =
      (v + (k : ℂ)⁻¹ • A.P0 la).1 (α + k • μ) + w * A.be la.y α / k + w * A.be la.y μ := by
    simp only [Prod.fst_add, AddMonoidHom.add_apply, Prod.smul_fst, AddMonoidHom.smul_apply, Pw_fst_apply,
      degeneratingTori_basePeriodMap_fst_apply, smul_eq_mul, map_add (A.be la.y), map_nsmul (A.be la.y), nsmul_eq_mul]
    push_cast
    field_simp
    ring
  have h2 : A.term k α th μ (v + (k : ℂ)⁻¹ • A.Pw w la) = A.term k α th μ (v + (k : ℂ)⁻¹ • A.P0 la) *
      eTwoPi (w * A.be la.y α / k) * eTwoPi (w * A.be la.y μ) := by
    rw [term, term, h1, e_add, e_add]
    simp only [Prod.snd_add, Prod.smul_snd, Pw_snd, degeneratingTori_basePeriodMap_snd]
    ring
  rw [h2, term_add_P0_div, exponent_add_weight]
  push_cast
  rw [mul_add w, e_add]
  ring

theorem Sum_add_Pw_div (w : ℂ) (la : A.La) (α : A.X) (th : (Fin A.gB → ℂ) → ℂ) (v : A.V) :
    A.Sum k α th w (v + (k : ℂ)⁻¹ • A.Pw w la) = Complex.exp (A.lin la v) * eTwoPi (w * A.be la.y α / k) *
      A.Sum k (α + la.y) (A.shift k la α th) w v := by
  simp only [Sum, term_add_Pw_div, tsum_mul_left]

theorem FSumShift_eq (la : A.La) {α : A.X} {m : ℤ} (hm : A.be la.y α = k * m) (th : (Fin A.gB → ℂ) → ℂ) (v : A.V) :
    A.FSumShift k α th la v =
      HahnSeries.single m (Complex.exp (A.lin la v)) * A.FSum k (α + la.y) (A.shift k la α th) v := by
  ext n
  rw [coeff_FSumShift, hm, Int.mul_ediv_cancel_left _ (NeZero.ne (k : ℤ))]
  conv_rhs => rw [← sub_add_cancel n m, HahnSeries.coeff_single_mul_add, coeff_FSum, Finset.mul_sum]
  exact Finset.sum_congr rfl fun μ _ => A.term_add_P0_div k la α th μ v

end Shift

theorem eq_zero_of_tsum_char {f : A.X → ℂ} (hf : Summable f)
    (h : ∀ l : A.X →+ ℂ, (∀ x, (l x).im = 0) → ∑' χ, f χ * eTwoPi (l χ) = 0) : f = 0 := by
  classical
  let b := Module.Free.chooseBasis ℤ A.X
  let E := b.equivFun.toEquiv
  have key : f ∘ E.symm = 0 := by
    refine eq_zero_of_tsum_mFourier (E.symm.summable_iff.2 hf) fun x => ?_
    choose t ht using fun i => QuotientAddGroup.mk_surjective (x i)
    have hl : ∀ χ, A.coord.symm (fun i => (t i : ℂ)) χ = ∑ i, (E χ i : ℂ) * t i := fun χ => by
      change b.constr ℤ (fun i => (t i : ℂ)) χ = _
      rw [Module.Basis.constr_apply_fintype]
      simp [E]
    have := h (A.coord.symm fun i => (t i : ℂ)) fun x => by simp [hl]
    rw [← E.symm.tsum_eq] at this
    refine Eq.trans (tsum_congr fun n => ?_) this
    rw [hl, Equiv.apply_symm_apply, eTwoPi, Finset.mul_sum, Complex.exp_sum]
    congr 1
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [← ht i, fourier_coe_apply]
    congr 1
    push_cast; ring
  funext χ
  simpa using congrFun key (E χ)

theorem sum_coeff_eq_zero [DecidableEq A.X] {j : ℕ} (hj : j ≠ 0) {ι : Type*} (s : Finset ι) (wt : ι → A.X)
    (hwt : ∀ p p' μ, wt p = wt p' + j • μ → wt p = wt p') {a : ι → A.X → ℂ} (ha : ∀ p ∈ s, Summable (a p))
    (h : ∀ l : A.X →+ ℂ, (∀ x, (l x).im = 0) → ∑ p ∈ s, ∑' μ, a p μ * eTwoPi (l (wt p + j • μ)) = 0)
    (p₀ : ι) (μ₀ : A.X) : ∑ p ∈ s with wt p = wt p₀, a p μ₀ = 0 := by
  have : HasUniqueDiv A.X := .of_isTorsionFree ℤ _
  have hinj : ∀ p, Function.Injective fun μ : A.X => wt p + j • μ := fun p μ ν hμ =>
    nsmul_right_injective hj (add_left_cancel hμ)
  let g : ι → A.X → ℂ := fun p => Function.extend (fun μ : A.X => wt p + j • μ) (a p) 0
  have hg : ∀ p μ, g p (wt p + j • μ) = a p μ := fun p μ => (hinj p).extend_apply _ _ μ
  have hg0 : ∀ p χ, χ ∉ Set.range (fun μ : A.X => wt p + j • μ) → g p χ = 0 := fun p χ hχ =>
    Function.extend_apply' _ _ _ hχ
  have hgs : ∀ p ∈ s, Summable (g p) := fun p hp =>
    ((hinj p).summable_iff (hg0 p)).1 ((ha p hp).congr fun μ => (hg p μ).symm)
  have key := A.eq_zero_of_tsum_char (f := fun χ => ∑ p ∈ s, g p χ) (summable_sum hgs) fun l hl => by
    have hn : ∀ χ, ‖eTwoPi (l χ)‖ = 1 := fun χ => by
      rw [e_def, Complex.norm_exp]; simp [hl χ]
    simp only [Finset.sum_mul]
    rw [Summable.tsum_finsetSum fun p hp =>
      Summable.of_norm (by simpa only [norm_mul, hn, mul_one] using (hgs p hp).norm), ← h l hl]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [← (hinj p).tsum_eq (f := fun χ => g p χ * eTwoPi (l χ))]
    · simp only [hg]
    · intro χ hχ
      by_contra hc
      exact hχ (by simp [hg0 p χ hc])
  have h1 := congrFun key (wt p₀ + j • μ₀)
  rw [Finset.sum_filter]
  refine Eq.trans (Finset.sum_congr rfl fun p _ => ?_) h1
  split_ifs with hp
  · rw [← hp, hg]
  · refine (hg0 p _ ?_).symm
    rintro ⟨μ, hμ⟩
    refine hp (hwt p p₀ (μ₀ - μ) ?_)
    rw [smul_sub, ← add_sub_assoc, ← hμ]
    simp

theorem term_eq_mul_char (j : ℕ) (α : A.X) (th : (Fin A.gB → ℂ) → ℂ) (μ : A.X) (l : A.X →+ ℂ) (z : Fin A.gB → ℂ) :
    A.term j α th μ (l, z) = A.term j α th μ (0, z) * eTwoPi (l (α + j • μ)) := by
  simp only [term, AddMonoidHom.zero_apply, e_zero]; ring

@[simp] theorem term_zero_zero (j : ℕ) (α : A.X) (th : (Fin A.gB → ℂ) → ℂ) (z : Fin A.gB → ℂ) :
    A.term j α th 0 (0, z) = th z := by simp [term]

@[simp] theorem exponent_zero (j : ℕ) (α : A.X) : A.exponent j α 0 = 0 := by simp [exponent]

theorem eq_zero_of_sum_filter {X W ι : Type*} [DecidableEq X] {s : Finset ι} {wt : ι → X} {th : ι → W → ℂ}
    (hth : ∀ α, LinearIndepOn ℂ th {p | wt p = α}) {r : ι → ℂ}
    (h : ∀ p₀ z, ∑ p ∈ s with wt p = wt p₀, r p * th p z = 0) : ∀ p ∈ s, r p = 0 := fun p₀ hp₀ =>
  linearIndepOn_iff'.1 (hth (wt p₀)) (s.filter fun p => wt p = wt p₀) r
    (fun p hp => (Finset.mem_filter.1 hp).2) (funext fun z => by simpa [Finset.sum_apply] using h p₀ z) p₀
    (Finset.mem_filter.2 ⟨hp₀, rfl⟩)

theorem linearIndependent_Sum {j : ℕ} (hj : j ≠ 0) {ι : Type*} (wt : ι → A.X)
    (hwt : ∀ p p' μ, wt p = wt p' + j • μ → wt p = wt p') (th : ι → (Fin A.gB → ℂ) → ℂ)
    (hth : ∀ α, LinearIndepOn ℂ th {p | wt p = α}) (w : ℂ)
    (hs : ∀ p z, Summable fun μ => A.term j (wt p) (th p) μ (0, z) * eTwoPi (w * A.exponent j (wt p) μ)) :
    LinearIndependent ℂ fun p => A.Sum j (wt p) (th p) w := by
  classical
  refine linearIndependent_iff'.2 fun s r hr => eq_zero_of_sum_filter hth fun p₀ z => ?_
  have := A.sum_coeff_eq_zero hj s wt hwt
    (a := fun p μ => r p * (A.term j (wt p) (th p) μ (0, z) * eTwoPi (w * A.exponent j (wt p) μ)))
    (fun p _ => (hs p z).mul_left _) (fun l _ => ?_) p₀ 0
  · simpa using this
  · refine Eq.trans ?_ (congrFun hr (l, z))
    rw [Finset.sum_apply]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [Pi.smul_apply, smul_eq_mul, Sum, ← tsum_mul_left]
    exact tsum_congr fun μ => by rw [A.term_eq_mul_char j _ _ μ l z]; ring

theorem hasSum_coeff_mul_FSum (j : ℕ) [NeZero j] (α : A.X) (th : (Fin A.gB → ℂ) → ℂ) (v : A.V)
    (r : LaurentSeries ℂ) (n : ℤ) :
    HasSum (fun μ => r.coeff (n - A.exponent j α μ) * A.term j α th μ v) ((r * A.FSum j α th v).coeff n) := by
  classical
  have hP : (Set.Ici (-A.be α α)).IsPWO := (BddBelow.isWF bddBelow_Ici).isPWO
  rw [HahnSeries.coeff_mul_right' hP fun m hm => by
    by_contra hc
    exact hm (A.coeff_FSum_eq_zero j α th v (not_le.1 hc))]
  have h1 : ∀ p : ℤ × ℤ, HasSum (fun μ => if A.exponent j α μ = p.2 then r.coeff p.1 * A.term j α th μ v else 0)
      (r.coeff p.1 * (A.FSum j α th v).coeff p.2) := fun p => by
    rw [coeff_FSum, Finset.mul_sum]
    convert hasSum_sum_of_ne_finset_zero (s := A.level j α p.2) (L := SummationFilter.unconditional _)
      (f := fun μ => if A.exponent j α μ = p.2 then r.coeff p.1 * A.term j α th μ v else 0)
      fun μ hμ => if_neg (by simpa using hμ) using 1
    exact Finset.sum_congr rfl fun μ hμ => (if_pos (by simpa using hμ)).symm
  convert hasSum_sum fun p _ => h1 p using 2 with μ
  rw [Finset.sum_eq_single (n - A.exponent j α μ, A.exponent j α μ)]
  · simp
  · rintro ⟨a, b⟩ hab hne
    refine if_neg fun hb => hne ?_
    have := (Finset.mem_antidiagonal.1 hab).2.2
    simp only at hb this
    ext <;> simp only <;> omega
  · intro hn
    rw [if_pos rfl]
    by_contra hc
    exact hn (Finset.mem_antidiagonal.2 ⟨left_ne_zero_of_mul hc, A.neg_be_le_exponent (NeZero.ne j) α μ, by simp⟩)

theorem linearIndependent_FSum (j : ℕ) [NeZero j] {ι : Type*} (wt : ι → A.X)
    (hwt : ∀ p p' μ, wt p = wt p' + j • μ → wt p = wt p') (th : ι → (Fin A.gB → ℂ) → ℂ)
    (hth : ∀ α, LinearIndepOn ℂ th {p | wt p = α}) :
    LinearIndependent (LaurentSeries ℂ) fun p => A.FSum j (wt p) (th p) := by
  classical
  refine linearIndependent_iff'.2 fun s r hr p hp => ?_
  ext n
  refine eq_zero_of_sum_filter (r := fun p => (r p).coeff n) hth (fun p₀ z => ?_) p hp
  have := A.sum_coeff_eq_zero (NeZero.ne j) s wt hwt
    (a := fun p μ => (r p).coeff (n - A.exponent j (wt p) μ) * A.term j (wt p) (th p) μ (0, z))
    (fun p _ => (A.hasSum_coeff_mul_FSum j _ _ _ _ _).summable) (fun l _ => ?_) p₀ 0
  · simpa using this
  · refine Eq.trans ?_ (congrArg (fun S : LaurentSeries ℂ => S.coeff n) (congrFun hr (l, z)))
    rw [Finset.sum_apply, HahnSeries.coeff_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [Pi.smul_apply, smul_eq_mul, ← (A.hasSum_coeff_mul_FSum j _ _ _ _ _).tsum_eq]
    exact tsum_congr fun μ => by rw [A.term_eq_mul_char j _ _ μ l z]; ring

theorem linearIndepOn_sigma {X W C : Type*} {I : C → Type*} {rep : C → X} (hrep : Function.Injective rep)
    {th : ∀ c, I c → W → ℂ} (hth : ∀ c, LinearIndependent ℂ (th c)) (α : X) :
    LinearIndepOn ℂ (fun p : Σ c, I c => th p.1 p.2) {p | rep p.1 = α} := by
  by_cases h : ∃ c, rep c = α
  · obtain ⟨c, rfl⟩ := h
    have : {p : Σ c, I c | rep p.1 = rep c} = Set.range (Sigma.mk c) := by
      ext ⟨c', i⟩
      simp only [Set.mem_setOf_eq, hrep.eq_iff, Set.mem_range]
      exact ⟨by rintro rfl; exact ⟨i, rfl⟩, by rintro ⟨i', hi⟩; exact (congrArg Sigma.fst hi).symm⟩
    rw [this]
    exact (linearIndepOn_range_iff sigma_mk_injective _).2 (hth c)
  · have : {p : Σ c, I c | rep p.1 = α} = ∅ := Set.eq_empty_of_forall_notMem fun p hp => h ⟨p.1, hp⟩
    rw [this]
    exact linearIndepOn_empty _ _

section Classes

variable {C : Type*} {I : C → Type*} {j : ℕ} {rep : C → A.X}

theorem linearIndependent_Sum_sigma (hj : j ≠ 0) (hrep : ∀ c c' μ, rep c = rep c' + j • μ → c = c')
    {th : ∀ c, I c → (Fin A.gB → ℂ) → ℂ} (hth : ∀ c, LinearIndependent ℂ (th c)) (w : ℂ)
    (hs : ∀ c i z, Summable fun μ => A.term j (rep c) (th c i) μ (0, z) * eTwoPi (w * A.exponent j (rep c) μ)) :
    LinearIndependent ℂ fun p : Σ c, I c => A.Sum j (rep p.1) (th p.1 p.2) w :=
  A.linearIndependent_Sum hj (fun p : Σ c, I c => rep p.1) (fun _ _ μ h => congrArg rep (hrep _ _ μ h)) _
    (linearIndepOn_sigma (fun c c' h => hrep c c' 0 (by simpa using h)) hth) w fun p => hs p.1 p.2

theorem linearIndependent_FSum_sigma [NeZero j] (hrep : ∀ c c' μ, rep c = rep c' + j • μ → c = c')
    {th : ∀ c, I c → (Fin A.gB → ℂ) → ℂ} (hth : ∀ c, LinearIndependent ℂ (th c)) :
    LinearIndependent (LaurentSeries ℂ) fun p : Σ c, I c => A.FSum j (rep p.1) (th p.1 p.2) :=
  A.linearIndependent_FSum j (fun p : Σ c, I c => rep p.1) (fun _ _ μ h => congrArg rep (hrep _ _ μ h)) _
    (linearIndepOn_sigma (fun c c' h => hrep c c' 0 (by simpa using h)) hth)

variable [Fintype C] [∀ c, Fintype (I c)]

theorem eq_zero_of_sum_FSum [NeZero j] (hrep : ∀ c c' μ, rep c = rep c' + j • μ → c = c')
    {th : ∀ c, I c → (Fin A.gB → ℂ) → ℂ} (hth : ∀ c, LinearIndependent ℂ (th c))
    {r : ∀ c, I c → LaurentSeries ℂ} (h : ∀ v, ∑ c, ∑ i, r c i * A.FSum j (rep c) (th c i) v = 0) (c : C) (i : I c) :
    r c i = 0 :=
  Fintype.linearIndependent_iff.1 (A.linearIndependent_FSum_sigma hrep hth) (fun p => r p.1 p.2)
    (funext fun v => by simpa [Finset.sum_apply, Fintype.sum_sigma] using h v) ⟨c, i⟩

end Classes

theorem exists_Sum_ne_zero {j : ℕ} (hj : j ≠ 0) (α : A.X) {th : (Fin A.gB → ℂ) → ℂ} (h : th ≠ 0) {w : ℂ}
    (hs : ∀ z, Summable fun μ => A.term j α th μ (0, z) * eTwoPi (w * A.exponent j α μ)) :
    ∃ v, A.Sum j α th w v ≠ 0 :=
  Function.ne_iff.1 ((A.linearIndependent_Sum hj (fun _ : Unit => α) (fun _ _ _ _ => rfl) (fun _ => th)
    (fun _ => (linearIndependent_unique_iff.2 h).linearIndepOn _) w fun _ => hs).ne_zero ())

theorem exists_FSum_ne_zero (j : ℕ) [NeZero j] (α : A.X) {th : (Fin A.gB → ℂ) → ℂ} (h : th ≠ 0) :
    ∃ v, A.FSum j α th v ≠ 0 :=
  Function.ne_iff.1 ((A.linearIndependent_FSum j (fun _ : Unit => α) (fun _ _ _ _ => rfl) (fun _ => th)
    (fun _ => (linearIndependent_unique_iff.2 h).linearIndepOn _)).ne_zero ())

end AnArc

end GlobalTheory
