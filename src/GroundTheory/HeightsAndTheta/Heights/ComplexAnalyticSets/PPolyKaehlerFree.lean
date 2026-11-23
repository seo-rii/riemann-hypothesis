module

public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StPolyKaehlerFree
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
import Mathlib.RingTheory.Smooth.StandardSmoothCotangent
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
public import Mathlib.Algebra.Module.Projective
public import Mathlib.RingTheory.Kaehler.JacobiZariski

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open KaehlerDifferential TensorProduct

theorem PolyKaehlerFree.proof : PolyKaehlerFree.Statement := by
  intro R k _ _ _ n
  set B := MvPolynomial (Fin n) k

  have hinj : Function.Injective (mapBaseChange R k B) := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨y, rfl⟩ := (Algebra.H1Cotangent.exact_δ_mapBaseChange R k B x).mp hx
    rw [Subsingleton.elim y 0, map_zero]
  have hex := exact_mapBaseChange_map R k B

  obtain ⟨l, hl⟩ := Module.projective_lifting_property ((map R k B B).restrictScalars B)
    LinearMap.id (map_surjective R k B)
  let e := ((hex.splitSurjectiveEquiv hinj) ⟨l, hl⟩).1
  have : Module.Free B Ω[B⁄k] := Module.Free.of_basis (mvPolynomialBasis k (Fin n))
  exact Module.Free.of_equiv e.symm
