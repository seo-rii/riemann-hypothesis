module

public import Mathlib.Analysis.Analytic.Basic
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsLieBasis
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.CompactSpacePointsPolAV
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.ContinuousOnValue
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.ExistsEtaleCoordsVanishing
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.ExistsLinearLift
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.ExistsTestFunctionsSubsetOfMemNhds
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.ExistsUniquePointOfRingHom
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.HolFamilyOfIsPullback
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.IsTopologicalGroupComplexPoints
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.TopLePreimageOfValAtNeZero
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Convex.Contractible
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
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.LatticeHom

theorem eq_zero_of_forall_smul_mem {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (Λ : Submodule ℤ E) (hd : DiscreteTopology Λ) {z : E} (hz : ∀ t : ℂ, t • z ∈ Λ) : z = 0 := by
  have hc : Continuous fun t : ℂ => (⟨t • z, hz t⟩ : Λ) := by fun_prop
  have h := (IsLocallyConstant.iff_continuous _).2 hc |>.apply_eq_of_preconnectedSpace 1 0
  simpa using congrArg Subtype.val h

theorem exists_linearEquiv_of_lifting {A : Over (Sp ℂ)} [GrpObj A] {L L₁ : LB A.left} {g : ℕ}
    (u : HolUnif A L g) (v : HolUnif A L₁ g)
    (hv : ∀ (n : ℕ) (a : (Fin n → ℂ) → (𝟙_ (Over (Sp ℂ)) ⟶ A)), (∀ (U : A.left.Opens) (f : Γ(A.left, U)),
      IsOpen {w | w ∈ (Set.univ : Set (Fin n → ℂ)) ∧ ⊤ ≤ (a w).left ⁻¹ᵁ U} ∧
        DifferentiableOn ℂ (fun w => valAt' (a w).left U f)
          {w | w ∈ (Set.univ : Set (Fin n → ℂ)) ∧ ⊤ ≤ (a w).left ⁻¹ᵁ U}) → a 0 = 1 →
      ∃ G : (Fin n → ℂ) → (Fin g → ℂ), G 0 = 0 ∧ AnalyticAt ℂ G 0 ∧ ∀ᶠ w in 𝓝 0, v.ex (G w) = a w) :
    ∃ T : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ), ∀ z, v.ex (T z) = u.ex z := by
  obtain ⟨G, hG0, hGa, hGe⟩ := hv g u.ex (fun U f => by simpa using u.hol U f)
    ((u.ker 0).2 u.Λ.zero_mem)
  have hT := EndoLinear.fderiv_lifts v.ex v.ex_add v.Λ v.ker v.discrete u.ex u.ex_add G hG0
    hGa.differentiableAt hGe
  have hi : Function.Injective (fderiv ℂ G 0).toLinearMap := by
    rw [injective_iff_map_eq_zero]
    intro z hz
    refine eq_zero_of_forall_smul_mem u.Λ u.discrete fun t => ?_
    have hz' : fderiv ℂ G 0 z = 0 := hz
    rw [← u.ker, ← hT, map_smul, hz', smul_zero]
    exact (v.ker 0).2 v.Λ.zero_mem
  exact ⟨LinearEquiv.ofInjectiveEndo _ hi, hT⟩

theorem exists_linearEquiv_of_holUnif (hmul : Out.MulNSt) (P : Out.PolAV (Sp ℂ)) {L L' : LB P.A.left}
    (u : HolUnif P.A L P.g) (u' : HolUnif P.A L' P.g) :
    ∃ T : (Fin P.g → ℂ) ≃ₗ[ℂ] (Fin P.g → ℂ), ∀ z, u'.ex (T z) = u.ex z := by
  have hval := @valAt'_rules
  have hvalaff := @existsUnique_point_of_ringHom
  obtain ⟨v, -, hv⟩ := @AbelianExp.exists_holUnif hmul hval (@holFamily_lift hval)
    (@isTopologicalGroup_complexPoints hval) (@PointsCompact.compactSpace_points_polAV hval hvalaff)
    (@HolChart.exists_holomorphic_chart hval hvalaff @exists_holomorphic_section_of_etale) P
  obtain ⟨T, hT⟩ := exists_linearEquiv_of_lifting u v hv
  obtain ⟨T', hT'⟩ := exists_linearEquiv_of_lifting u' v hv
  refine ⟨T.trans T'.symm, fun z => ?_⟩
  rw [← hT', ← hT]
  simp

end GlobalTheory.LatticeHom
