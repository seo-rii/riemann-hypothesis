module

public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedTraceEquivariantAndInjectiveOfGroupDet
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Topology.Sheaves.Init
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic

@[expose] public section

open scoped BigOperators Matrix
open Polynomial

namespace GlobalTheory

theorem finrank_le_card_mul_finrank_eigenspace_le :
    ∀ (H K R : Type) [Group H] [Fintype H] [DecidableEq H] [Field K] [CommRing R] [Algebra K R]
      (st : H → R →ₐ[K] R), (∀ x, st 1 x = x) → (∀ h h' x, st (h * h') x = st h' (st h x)) →
      ∀ (χ : H →* Kˣ) (u : R),
      (Matrix.of fun h g : H => st (h * g) u).det ∈ nonZeroDivisors R →
      ∀ (Vm V Vp N : Submodule K R) [FiniteDimensional K Vm] [FiniteDimensional K V]
        [FiniteDimensional K Vp], (∀ h, ∀ x ∈ V, st h x ∈ V) →
      (∀ h, ∀ x ∈ Vm, x * st h u ∈ V) → (∀ h, ∀ x ∈ V, x * st h u ∈ Vp) →
      (∀ x, x ∈ N ↔ x ∈ V ∧ ∀ h, st h x = ((χ h : Kˣ) : K) • x) →
      Module.finrank K Vm ≤ Fintype.card H * Module.finrank K N ∧
        Fintype.card H * Module.finrank K N ≤ Module.finrank K Vp := by
  intro H K R _ _ _ _ _ _ st h1 hmul χ u hdet Vm V Vp N _ _ _ hV hm hp hN
  obtain ⟨hTr, hPhi, hPsi⟩ := GlobalTheory.twistedTrace_equivariant_and_injective_of_groupDet H K R st h1 hmul χ u hdet
  have hNV : N ≤ V := fun x hx => ((hN x).1 hx).1
  have : FiniteDimensional K N := Submodule.finiteDimensional_of_le hNV
  have hrk : Module.finrank K (H → N) = Fintype.card H * Module.finrank K N := by
    rw [Module.finrank_pi_fintype]
    simp
  rw [← hrk]
  constructor
  · have hmem : ∀ (f : Vm) (h : H),
        ∑ g, (((χ g)⁻¹ : Kˣ) : K) • st g ((f : R) * st h u) ∈ N := fun f h =>
      (hN _).2 ⟨V.sum_mem fun g _ => V.smul_mem _ (hV g _ (hm h _ f.2)), fun g => hTr _ g⟩
    let Φ : Vm →ₗ[K] (H → N) :=
      { toFun := fun f h => ⟨_, hmem f h⟩
        map_add' := fun f f' => by
          funext h
          apply Subtype.ext
          simp only [Submodule.coe_add, add_mul, map_add (f := _), smul_add, Finset.sum_add_distrib,
            Pi.add_apply]
        map_smul' := fun c f => by
          funext h
          apply Subtype.ext
          simp only [Submodule.coe_smul, smul_mul_assoc, map_smul, Pi.smul_apply,
            RingHom.id_apply, Finset.smul_sum]
          exact Finset.sum_congr rfl fun g _ => smul_comm _ _ _ }
    refine LinearMap.finrank_le_finrank_of_injective (f := Φ) ?_
    rw [injective_iff_map_eq_zero]
    intro f hf
    apply Subtype.ext
    exact hPhi f fun h => congrArg Subtype.val (congrFun hf h)
  · have hmem : ∀ F : H → N, ∑ h, (F h : R) * st h u ∈ Vp := fun F =>
      Vp.sum_mem fun h _ => hp h _ (hNV (F h).2)
    let Ψ : (H → N) →ₗ[K] Vp :=
      { toFun := fun F => ⟨_, hmem F⟩
        map_add' := fun F F' => by
          apply Subtype.ext
          simp only [Submodule.coe_add, add_mul, Finset.sum_add_distrib, Pi.add_apply]
        map_smul' := fun c F => by
          apply Subtype.ext
          simp only [Submodule.coe_smul, smul_mul_assoc, Pi.smul_apply,
            RingHom.id_apply, Finset.smul_sum] }
    refine LinearMap.finrank_le_finrank_of_injective (f := Ψ) ?_
    rw [injective_iff_map_eq_zero]
    intro F hF
    have := hPsi (fun h => (F h : R)) (fun h g => ((hN _).1 (F h).2).2 g)
      (congrArg Subtype.val hF)
    funext h
    exact Subtype.ext (congrFun this h)

end GlobalTheory
