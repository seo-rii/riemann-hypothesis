module

public import Development.AbelianVarietyTheory.Definitions.Foundations.NotCoboundaryConstantOne
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

@[expose] public section

open GlobalTheory.K5

noncomputable section

namespace GlobalTheory.K5.DerAlg

open Polynomial

variable {p : ℕ} [Fact p.Prime] {Ω : Type} [Field Ω] [Algebra (O0 p) Ω]

abbrev phiZ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω] : ℤ_[p] →+* Ω :=
  (algebraMap (O0 p) Ω).comp (algebraMap ℤ_[p] (O0 p))

theorem phiZ_injective [CharZero Ω] : Function.Injective (phiZ p Ω) := by
  rw [injective_iff_map_eq_zero]
  intro c hc
  by_contra h0
  rw [PadicInt.unitCoeff_spec h0, map_mul, map_pow, map_natCast] at hc
  have hu : IsUnit (phiZ p Ω (PadicInt.unitCoeff h0 : ℤ_[p])) :=
    (Units.isUnit _).map _
  have hp : ((p : Ω)) ^ c.valuation ≠ 0 :=
    pow_ne_zero _ (by exact_mod_cast (Fact.out : p.Prime).ne_zero)
  exact mul_ne_zero hu.ne_zero hp hc

theorem der_eval₂ (E : Derivation ℤ Ω Ω)
    (hE : ∀ r : ℤ_[p], E (algebraMap (O0 p) Ω (algebraMap ℤ_[p] (O0 p) r)) = 0)
    (x : Ω) (Q : ℤ_[p][X]) :
    E (eval₂ (phiZ p Ω) x Q) = eval₂ (phiZ p Ω) x (derivative Q) * E x := by
  induction Q using Polynomial.induction_on' with
  | add P Q hP hQ => rw [eval₂_add, map_add (f := _), hP, hQ, derivative_add, eval₂_add, add_mul]
  | monomial n c =>
    have hc : E (phiZ p Ω c) = 0 := hE c
    rw [eval₂_monomial, Derivation.leibniz, Derivation.leibniz_pow, hc, smul_zero, add_zero,
      derivative_monomial, eval₂_monomial]
    simp only [smul_eq_mul, nsmul_eq_mul, map_mul, map_natCast]
    ring

theorem der_algZp : ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], IsClo p Ω →
    ∀ E : Derivation ℤ Ω Ω, (∀ r : ℤ_[p], E (algebraMap (O0 p) Ω (algebraMap ℤ_[p] (O0 p) r)) = 0) →
    ∀ x : Ω, IsAlgZp (p := p) x → E x = 0 := by
  intro p _ Ω _ _ hC E hE x hx
  haveI : CharZero Ω := GlobalTheory.K5.Basic.charZero_of_isClo hC
  obtain ⟨P, hP0, hPx⟩ := hx
  rw [aeval_def, eval₂_map] at hPx
  change eval₂ (phiZ p Ω) x P = 0 at hPx
  by_contra hEx
  have key : ∀ n, ∀ P : ℤ_[p][X], P.natDegree = n → P ≠ 0 → eval₂ (phiZ p Ω) x P ≠ 0 := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro P hn hP hzero
      by_cases hd : P.natDegree = 0
      · rw [eq_C_of_natDegree_eq_zero hd, eval₂_C] at hzero
        have := phiZ_injective (p := p) (Ω := Ω) (hzero.trans (map_zero _).symm)
        exact hP (by rw [eq_C_of_natDegree_eq_zero hd, this, C_0])
      · have hD : derivative P ≠ 0 := fun h => hd (natDegree_eq_zero_of_derivative_eq_zero h)
        have hlt := natDegree_derivative_lt hd
        refine ih _ (hn ▸ hlt) (derivative P) rfl hD ?_
        have h1 := der_eval₂ E hE x P
        rw [hzero, map_zero] at h1
        exact (mul_eq_zero.1 h1.symm).resolve_right hEx
  exact key _ P rfl hP0 hPx

end GlobalTheory.K5.DerAlg
