module

public import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.CategoryTheory.Sites.EpiMono
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

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory.EtC.MonoEpi

instance wEqLBMonoEpi (R : Type) [CommRing R] :
    (Scheme.etaleTopology.{0}).WEqualsLocallyBijective (ModuleCat.{1} (ULift.{1} R)) := by
  have : EssentiallySmall.{1} Scheme.{0} := inferInstance
  exact GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall _

variable {R : Type} [CommRing R]

theorem sec_ext {F G : Shv R} (φ ψ : F ⟶ G) (h : ∀ U (a : Sec F U), Sec.map φ a = Sec.map ψ a) : φ = ψ := by
  apply Sheaf.hom_ext
  ext U a
  exact h (unop U) a

theorem mono_iff_inj {F G : Shv R} (φ : F ⟶ G) :
    Mono φ ↔ ∀ U, Function.Injective (Sec.map φ (U := U)) := by
  constructor
  · intro h U
    have : Mono φ.hom := inferInstanceAs (Mono ((sheafToPresheaf _ _).map φ))
    have : Mono (φ.hom.app (op U)) := inferInstance
    exact (ModuleCat.mono_iff_injective _).1 this
  · intro h
    have : Mono φ.hom := by
      rw [NatTrans.mono_iff_mono_app]
      intro U
      exact (ModuleCat.mono_iff_injective _).2 (h (unop U))
    exact (sheafToPresheaf _ _).mono_of_mono_map this

theorem inj_iff_loc {F G : Shv R} (φ : F ⟶ G) :
    (∀ U, Function.Injective (Sec.map φ (U := U))) ↔
      ∀ U (a : Sec F U), Sec.map φ a = 0 → Loc U fun _ g => Sec.res g a = 0 := by
  constructor
  · intro h U a ha
    have : a = 0 := h U (by rw [ha]; exact (map_zero _).symm)
    subst this
    exact ⟨⊤, Scheme.etaleTopology.top_mem U, fun V g _ => map_zero _⟩
  · intro h U
    rw [injective_iff_map_eq_zero]
    intro a ha
    obtain ⟨S, hS, hP⟩ := h U a ha
    have hF : Presieve.IsSheaf Scheme.etaleTopology (F.obj ⋙ forget _) :=
      (isSheaf_iff_isSheaf_of_type _ _).1 ((sheafCompose Scheme.etaleTopology (forget (ModuleCat.{1} (ULift.{1} R)))).obj F).property
    refine (hF S hS).isSeparatedFor.ext fun V g hg => ?_
    change Sec.res g a = Sec.res g (0 : Sec F U)
    rw [hP V g hg]
    exact (map_zero _).symm

theorem epi_iff_loc {F G : Shv R} (φ : F ⟶ G) :
    Epi φ ↔ ∀ U (b : Sec G U), Loc U fun V g => ∃ a : Sec F V, Sec.map φ a = Sec.res g b := by
  rw [← Sheaf.isLocallySurjective_iff_epi']
  constructor
  · intro h U b
    exact ⟨_, Presheaf.imageSieve_mem Scheme.etaleTopology φ.hom b, fun V g hg => hg⟩
  · intro h
    constructor
    intro U b
    obtain ⟨S, hS, hP⟩ := h U b
    refine Scheme.etaleTopology.superset_covering ?_ hS
    intro V g hg
    exact hP V g hg

end GlobalTheory.EtC.MonoEpi

open GlobalTheory.EtC.MonoEpi in
theorem GlobalTheory.EtC.mono_epi_sections : ∀ (R : Type) [CommRing R] {F G : Shv R} (φ : F ⟶ G), (Mono φ ↔ ∀ U, Function.Injective (Sec.map φ (U := U))) ∧ (Mono φ ↔ ∀ U (a : Sec F U), Sec.map φ a = 0 → Loc U fun _ g => Sec.res g a = 0) ∧ (Epi φ ↔ ∀ U (b : Sec G U), Loc U fun V g => ∃ a : Sec F V, Sec.map φ a = Sec.res g b) ∧ (∀ ψ : F ⟶ G, (∀ U (a : Sec F U), Sec.map φ a = Sec.map ψ a) → φ = ψ) := by
  intro R _ F G φ
  exact ⟨mono_iff_inj φ, (mono_iff_inj φ).trans (inj_iff_loc φ), epi_iff_loc φ, fun ψ h => sec_ext φ ψ h⟩
