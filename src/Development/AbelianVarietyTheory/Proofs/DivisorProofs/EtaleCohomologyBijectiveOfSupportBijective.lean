module

public import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
public import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChosenInjectiveResolutionEtaleSheafPropertiesStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HypercohomologyMappingConeSecondVariableExactStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MappingConeLocallyExactOfComponentSectionsStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MappingConeResolutionLocalChaseOnSupportStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SubsingletonHypercohomologyOfLocallyExactOnSuppoStatement
public import Mathlib.Algebra.Homology.HomotopyCategory.Plus
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

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory.EtC.ConeLocalization

theorem cone_kinj (R : Type) [CommRing R] {F G : Shv R} (φ : F ⟶ G) :
    (mappingCone (resMap R φ)).IsKInjective := by
  haveI := (GlobalTheory.T.chosenInjectiveResolution_etaleSheaf_properties R F).2.1
  haveI := (GlobalTheory.T.chosenInjectiveResolution_etaleSheaf_properties R G).2.1
  haveI := (GlobalTheory.T.chosenInjectiveResolution_etaleSheaf_properties R F).2.2.1
  haveI := (GlobalTheory.T.chosenInjectiveResolution_etaleSheaf_properties R G).2.2.1
  haveI : ∀ n, Injective ((mappingCone (resMap R φ)).X n) := fun n =>
    Injective.of_iso (HomologicalComplex.homotopyCofiber.XIsoBiprod (resMap R φ) n (n + 1) rfl).symm inferInstance
  haveI : (mappingCone (resMap R φ)).IsStrictlyGE (-1) := CochainComplex.isStrictlyGE_mappingCone _ 0 0 (-1)
  exact isKInjective_of_injective _ (-1)

theorem cone_loc (R : Type) [CommRing R] (E : Spc) {F G : Shv R} (φ : F ⟶ G)
    (hφ : ∀ U : Scheme.{0}, Nonempty (Sx E 0 U) → Function.Bijective (Sec.map φ (U := U))) :
    ∀ (U : Scheme.{0}), Nonempty (Sx E 0 U) → ∀ (n : ℤ) (b : Sec ((mappingCone (resMap R φ)).X n) U),
      Sec.map ((mappingCone (resMap R φ)).d n (n + 1)) b = 0 →
      Loc U fun V g => ∃ a : Sec ((mappingCone (resMap R φ)).X (n - 1)) V,
        Sec.map ((mappingCone (resMap R φ)).d (n - 1) n) a = Sec.res g b := by
  intro U hU n b hb
  exact GlobalTheory.T.mappingCone_locallyExact_of_component_sections R (resMap R φ) U n (GlobalTheory.T.mappingCone_resolution_localChase_on_support R E φ hφ U hU n) b hb

end GlobalTheory.EtC.ConeLocalization

theorem GlobalTheory.EtC.a10 : GlobalTheory.EtC.A10 := by
  intro R _ E F G φ hφ
  haveI := GlobalTheory.EtC.ConeLocalization.cone_kinj R φ
  have hC := GlobalTheory.T.subsingleton_hypercohomology_of_locallyExact_on_support R E (mappingCone (resMap R φ)) (GlobalTheory.EtC.ConeLocalization.cone_loc R E φ hφ)
  have ex := GlobalTheory.T.hypercohomology_mappingCone_second_variable_exact R ((chains R).obj E) (resMap R φ)
  intro n
  constructor
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by ring⟩
    rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨y, rfl⟩ := ((ex m).2.2 x).1 hx
    rw [Subsingleton.elim y 0, map_zero]
  · intro y
    exact ((ex n).1 y).1 (Subsingleton.elim _ _)
