module

public import Development.EtaleCohomology.EtaleSheaves.TruncKerPf
public import Development.EtaleCohomology.EtaleSheaves.LocalDescent
public import Development.EtaleCohomology.EtaleSheaves.BijOfIso
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

@[expose] public section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.E.t_E3Cut LateralTheory.E.StalkCut LateralTheory.E.DescLocPf
open LateralTheory.E.LeafGhostCut

namespace LateralTheory.E.KernelLocalization

theorem KerLoc_of (hC : Coprod) (hD : LateralTheory.E.TruncationKernel.RelDesc) : KerLoc := by
  intro hH q _ i n A Y φ hq P hpush het hlow _ D d hPD hpts Y' w φ' hpo
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨z, rfl⟩ := relExact _ _ _ n x hx
  obtain ⟨E, e, Z, u, ψ, h, he, hs, h0⟩ := relKill hH.2.2.2.2.2.2.1 hC q i n φ hq d hpts w φ' hpo z hx
  have hz : z = 0 := (injective_iff_map_eq_zero _).1
    (hD hH q i n φ hq P hpush het hlow D d hPD Y' w φ' hpo E e Z u ψ he hs (het d e hPD he) h) z h0
  rw [hz, map_zero]

end LateralTheory.E.KernelLocalization
