module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.RepAlg
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
public import Mathlib.Topology.Instances.Matrix
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.DeterminantRepresentations.Imports
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.DeterminantRepresentations.MapApi
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.DeterminantRepresentations.RepApi
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.DeterminantRepresentations.RepCont
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Polynomial UpperTheory.V.W

private def UpperTheory.V.AlgebraTools.Det.piRep {n : ℕ} {G X : Type} [Group G] (K : X → Type) [∀ x, CommRing (K x)]
    (ρ : ∀ x, G →* Matrix (Fin n) (Fin n) (K x)) : G →* Matrix (Fin n) (Fin n) (∀ x, K x) where
  toFun g := Matrix.of fun i j x => ρ x g i j
  map_one' := by
    ext i j x
    by_cases h : i = j <;> simp [Matrix.one_apply, h]
  map_mul' g h := by
    ext i j x
    simp [Matrix.mul_apply, Finset.sum_apply]

theorem UpperTheory.V.AlgebraTools.Det.glueRep :
    ∀ {n : ℕ} {A G : Type} [CommRing A] [Group G] [TopologicalSpace A] [CompactSpace A] [TopologicalSpace G] {X : Type} (K : X → Type) [∀ x, CommRing (K x)]
    [∀ x, TopologicalSpace (K x)] [∀ x, IsTopologicalRing (K x)] [∀ x, T2Space (K x)] (f : ∀ x, A →+* K x)
    (ρ : ∀ x, G →* Matrix (Fin n) (Fin n) (K x)) (S : Set G), (∀ x, Continuous (f x)) → (∀ a, (∀ x, f x a = 0) → a = 0) → Dense S →
    (∀ x, Continuous (ρ x)) → (∀ g ∈ S, ∃ p : A[X], ∀ x, p.map (f x) = (ρ x g).charpoly) →
    ∃ D : GDet n A G, (∀ x, D.map (f x) = GDet.ofRep (ρ x)) ∧ ∀ i ≤ n, Continuous fun g : G => D.lam i (MonoidAlgebra.single g 1) := by
  intro n A G _ _ _ _ _ X K _ _ _ _ f ρ S hf hinj hS hρ hp
  let ι : A →+* (∀ x, K x) := Pi.ringHom f
  have hιc : Continuous ι := continuous_pi fun x => hf x
  have hιi : Function.Injective ι := by
    rw [injective_iff_map_eq_zero]
    intro a ha
    exact hinj a fun x => congrFun ha x
  let R := UpperTheory.V.AlgebraTools.Det.piRep K ρ
  have hR : Continuous R := by
    apply continuous_matrix
    intro i j
    apply continuous_pi
    intro x
    exact ((hρ x).matrix_elem i j)
  obtain ⟨D, hD, hDc⟩ := UpperTheory.V.AlgebraTools.Det.glue ι (GDet.ofRep R) S hιc hιi hS
    (fun i _ => UpperTheory.V.AlgebraTools.Det.repCont R hR i)
    (by
      intro g hg i _
      obtain ⟨p, hp⟩ := hp g hg
      have hchar : (R g).charpoly = p.map ι := by
        ext k x
        have h1 := congrArg (fun q : (K x)[X] => q.coeff k)
          (Matrix.charpoly_map (R g) (Pi.evalRingHom K x))
        have h2 : (R g).map (Pi.evalRingHom K x) = ρ x g := by
          ext i j
          rfl
        rw [h2, ← hp x, Polynomial.coeff_map, Polynomial.coeff_map] at h1
        rw [Polynomial.coeff_map]
        exact h1.symm
      refine ⟨(-1) ^ i * p.coeff (n - i), ?_⟩
      show ι ((-1) ^ i * p.coeff (n - i)) = (-1) ^ i * ((GDet.ofRep R).chi (MonoidAlgebra.single g 1)).coeff (n - i)
      rw [(UpperTheory.V.AlgebraTools.Det.repApi R).2.1 g, hchar, Polynomial.coeff_map, map_mul, map_pow, map_neg, map_one])
  refine ⟨D, ?_, hDc⟩
  intro x
  have hfx : f x = (Pi.evalRingHom K x).comp ι := by
    ext a
    rfl
  rw [hfx, ← (UpperTheory.V.AlgebraTools.Det.mapApi D ι).2.2.2.2.2.2.1 (Pi.evalRingHom K x), hD, (UpperTheory.V.AlgebraTools.Det.repApi R).2.2.2.2.2.1 (Pi.evalRingHom K x)]
  congr 1
