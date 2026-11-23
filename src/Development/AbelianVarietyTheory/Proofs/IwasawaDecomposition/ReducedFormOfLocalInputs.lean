module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsobaricDiscreteSelfDualStrongMultiplicityOne
public import Formalism.SharpRestriction.LevelLetterCocycles.SumRepresentations
import Formalism.PadicSubsetSums.StableGradedCounts.ZBrauerNesbittAlg
public import Formalism.SharpRestriction.LevelLetterCocycles.ExistsInertiaCharpolyFactorOfTameType
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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

@[expose] public section

noncomputable section

namespace GlobalTheory.PtSt

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N GlobalTheory.RowCopy

theorem map_MjSig_eq (D : D7) (i : D.nd.Loc) (hInt : Rows.IsotInternal D.what₂) (h42 : SumRepresentations.At.Conclusion42 D.nd D.naut i)
    (hUp : ParUpRec D.nd D.naut i) (hDown : DownMemRec D.nd D.naut i) (hNZ : TypeNZRec D.nd D.naut i) :
    ∀ x ∈ ZgoodN D.nd D.naut i, ∀ Sig, HasParamX D.nd D.naut i x Sig →
      (MjSig D.nd D.naut i Sig).map (D.what₂.thetaT (D.nd.mu i) (D.nd.j i)) = eigC D.nd D.naut i x := by
  intro x hx Sig hS
  refine Submodule.eq_of_le_of_finrank_le (hUp x hx Sig hS) ?_
  have hinj := SumRepresentations.thetaT_injective D.nd D.naut i hInt h42
  have h1 : Module.finrank ℂ ↥((MjSig D.nd D.naut i Sig).map (D.what₂.thetaT (D.nd.mu i) (D.nd.j i))) =
      Module.finrank ℂ ↥(MjSig D.nd D.naut i Sig) :=
    (LinearEquiv.finrank_eq (Submodule.equivMapOfInjective _ hinj (MjSig D.nd D.naut i Sig))).symm
  have hfi : Function.Injective ((D.what₂.thetaP (D.nd.mu i) (D.nd.j i)).domRestrict (eigC D.nd D.naut i x)) := by
    rw [injective_iff_map_eq_zero]
    intro F hF
    exact Subtype.ext (hNZ x hx F.1 F.2 hF)
  have h2 : Module.finrank ℂ ↥(eigC D.nd D.naut i x) =
      Module.finrank ℂ ↥((eigC D.nd D.naut i x).map (D.what₂.thetaP (D.nd.mu i) (D.nd.j i))) := by
    rw [← LinearMap.range_domRestrict]
    exact (LinearMap.finrank_range_of_inj hfi).symm
  rw [h1, h2]
  exact Submodule.finrank_mono (hDown x hx Sig hS)

end GlobalTheory.PtSt

end
