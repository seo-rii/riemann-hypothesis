module

public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsFiniteProjectiveComplexQuasiIso
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.Algebra.Module.StablyFree.Basic
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
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.RingTheory.LocalProperties.Projective
public import Mathlib.RingTheory.LocalRing.Module

@[expose] public section

open TensorProduct Function

namespace GlobalTheory

section LinearAlgebra

variable {R : Type*} [CommRing R] {A B C : Type*}
  [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B] [AddCommGroup C] [Module R C]

theorem exact_lTensor_iff_of_faithfullyFlat (k L : Type*) [CommRing k] [CommRing L] [Algebra R k]
    [Algebra R L] [Algebra k L] [IsScalarTower R k L] [Module.FaithfullyFlat k L]
    (f : A →ₗ[R] B) (g : B →ₗ[R] C) :
    Exact (f.lTensor L) (g.lTensor L) ↔ Exact (f.lTensor k) (g.lTensor k) := by
  have h1 := Module.FaithfullyFlat.lTensor_exact_iff_exact k L (f.baseChange k) (g.baseChange k)
  have h2 : Exact (AlgebraTensorModule.lTensor k L f) (AlgebraTensorModule.lTensor k L g) ↔
      Exact ((f.baseChange k).lTensor L) ((g.baseChange k).lTensor L) :=
    Function.Exact.iff_of_ladder_linearEquiv
      (e₁ := AlgebraTensorModule.cancelBaseChange R k k L A)
      (e₂ := AlgebraTensorModule.cancelBaseChange R k k L B)
      (e₃ := AlgebraTensorModule.cancelBaseChange R k k L C)
      (by ext; simp) (by ext; simp)
  exact h2.trans h1

theorem exact_lTensor_iff_residueField (p : Ideal R) [p.IsPrime] (L : Type*) [Field L]
    [Algebra R L] (hL : RingHom.ker (algebraMap R L) = p) (f : A →ₗ[R] B) (g : B →ₗ[R] C) :
    Exact (f.lTensor L) (g.lTensor L) ↔
      Exact (f.lTensor p.ResidueField) (g.lTensor p.ResidueField) := by
  let φ : p.ResidueField →ₐ[R] L := Ideal.ResidueField.liftₐ p (Algebra.ofId R L) hL.ge (by
    intro x hx
    simp only [Submonoid.mem_comap, IsUnit.mem_submonoid_iff, isUnit_iff_ne_zero]
    intro h0
    exact hx (hL ▸ h0))
  letI : Algebra p.ResidueField L := φ.toRingHom.toAlgebra
  haveI : IsScalarTower R p.ResidueField L :=
    IsScalarTower.of_algebraMap_eq fun x => (φ.commutes x).symm
  exact exact_lTensor_iff_of_faithfullyFlat p.ResidueField L f g

theorem split_injective_of_forall_lTensor_residueField_injective [Module.Finite R B]
    [Module.Finite R C] [Module.Projective R C] (l : B →ₗ[R] C)
    (h : ∀ (m : Ideal R) [m.IsMaximal], Injective (l.lTensor m.ResidueField)) :
    ∃ r : C →ₗ[R] B, r ∘ₗ l = LinearMap.id := by
  have hloc : ∀ (m : Ideal R) [m.IsMaximal], Injective ((l.baseChange (Localization.AtPrime m)).lTensor
      (IsLocalRing.ResidueField (Localization.AtPrime m))) := by
    intro m _
    have e : (AlgebraTensorModule.cancelBaseChange R (Localization.AtPrime m)
          (Localization.AtPrime m) m.ResidueField C) ∘
          ((l.baseChange (Localization.AtPrime m)).lTensor m.ResidueField) =
        (l.lTensor m.ResidueField) ∘ (AlgebraTensorModule.cancelBaseChange R
          (Localization.AtPrime m) (Localization.AtPrime m) m.ResidueField B) := by
      funext x
      exact (LinearMap.congr_fun (AlgebraTensorModule.lTensor_comp_cancelBaseChange R
        (Localization.AtPrime m) (Localization.AtPrime m) (M := m.ResidueField) l) x).symm
    exact Injective.of_comp (e ▸ (h m).comp (LinearEquiv.injective _))
  have hfree : ∀ (m : Ideal R) [m.IsMaximal],
      Module.Free (Localization.AtPrime m) (Localization.AtPrime m ⊗[R] C) := fun m _ =>
    Module.free_of_flat_of_isLocalRing
  have hinj : Injective l := by
    rw [← LinearMap.ker_eq_bot, ← Submodule.subsingleton_iff_eq_bot]
    refine Module.subsingleton_of_localization_maximal (R := R)
      (fun m _ => Localization.AtPrime m ⊗[R] LinearMap.ker l)
      (fun m _ => TensorProduct.mk R (Localization.AtPrime m) _ 1) (fun m _ => ?_)
    obtain ⟨r, hr⟩ := (IsLocalRing.split_injective_iff_lTensor_residueField_injective _).2 (hloc m)
    have h1 : Injective (l.lTensor (Localization.AtPrime m)) :=
      HasLeftInverse.injective ⟨r, LinearMap.congr_fun hr⟩
    have h2 : Injective ((LinearMap.ker l).subtype.lTensor (Localization.AtPrime m)) :=
      Module.Flat.lTensor_preserves_injective_linearMap _ Subtype.val_injective
    refine (subsingleton_iff_forall_eq 0).2 fun y => h2 (h1 ?_)
    rw [map_zero, map_zero, ← LinearMap.comp_apply, ← LinearMap.lTensor_comp,
      l.exact_subtype_ker_map.linearMap_comp_eq_zero, LinearMap.lTensor_zero,
      LinearMap.zero_apply]
  have : Module.FinitePresentation R C := Module.finitePresentation_of_projective R C
  have : Module.FinitePresentation R (C ⧸ LinearMap.range l) :=
    Module.finitePresentation_of_surjective (LinearMap.range l).mkQ (Submodule.mkQ_surjective _)
      (by rw [Submodule.ker_mkQ, LinearMap.range_eq_map]; exact Module.Finite.fg_top.map l)
  have : Module.Projective R (C ⧸ LinearMap.range l) := by
    refine Module.projective_of_localization_maximal' (fun m _ => Localization.AtPrime m)
      (fun m _ => Localization.AtPrime m ⊗[R] (C ⧸ LinearMap.range l))
      (fun m _ => TensorProduct.mk R (Localization.AtPrime m) _ 1) (fun m _ => ?_)
    have := Module.free_of_lTensor_residueField_injective
      (l.baseChange (Localization.AtPrime m))
      ((LinearMap.range l).mkQ.baseChange (Localization.AtPrime m))
      (LinearMap.lTensor_surjective _ (Submodule.mkQ_surjective _))
      (lTensor_exact _ l.exact_map_mkQ_range (Submodule.mkQ_surjective _)) (hloc m)
    infer_instance
  have := (Exact.split_tfae l.exact_map_mkQ_range hinj (Submodule.mkQ_surjective _)).out 1 2
  rw [← this]
  exact Module.projective_lifting_property _ _ (Submodule.mkQ_surjective _)

theorem lTensor_liftQ_injective_of_exact (N : Type*) [AddCommGroup N] [Module R N]
    {f : A →ₗ[R] B} {g : B →ₗ[R] C} (hfg : LinearMap.range f ≤ LinearMap.ker g)
    (h : Exact (f.lTensor N) (g.lTensor N)) :
    Injective (((LinearMap.range f).liftQ g hfg).lTensor N) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨y, rfl⟩ := LinearMap.lTensor_surjective N (Submodule.mkQ_surjective _) x
  rw [← LinearMap.comp_apply, ← LinearMap.lTensor_comp, Submodule.liftQ_mkQ] at hx
  obtain ⟨z, rfl⟩ := (h y).1 hx
  rw [← LinearMap.comp_apply, ← LinearMap.lTensor_comp,
    f.exact_map_mkQ_range.linearMap_comp_eq_zero, LinearMap.lTensor_zero, LinearMap.zero_apply]

theorem exists_homotopy_of_forall_exact_residueField [Module.Finite R B] [Module.Projective R B]
    [Module.Finite R C] [Module.Projective R C] {f : A →ₗ[R] B} {g : B →ₗ[R] C} (hfg : g ∘ₗ f = 0)
    (h : ∀ (m : Ideal R) [m.IsMaximal],
      Exact (f.lTensor m.ResidueField) (g.lTensor m.ResidueField)) :
    ∃ (s : B →ₗ[R] A) (t : C →ₗ[R] B), f ∘ₗ s + t ∘ₗ g = LinearMap.id := by
  have hle : LinearMap.range f ≤ LinearMap.ker g := LinearMap.range_le_ker_iff.2 hfg
  obtain ⟨r, hr⟩ := split_injective_of_forall_lTensor_residueField_injective
    ((LinearMap.range f).liftQ g hle) fun m _ => lTensor_liftQ_injective_of_exact _ hle (h m)
  obtain ⟨t, ht⟩ := Module.projective_lifting_property (LinearMap.range f).mkQ r
    (Submodule.mkQ_surjective _)
  have hmem : ∀ b, (LinearMap.id - t ∘ₗ g : B →ₗ[R] B) b ∈ LinearMap.range f := by
    intro b
    have h1 := LinearMap.congr_fun ht (g b)
    have h2 := LinearMap.congr_fun hr (Submodule.Quotient.mk b)
    simp only [LinearMap.comp_apply, Submodule.liftQ_apply, Submodule.mkQ_apply,
      LinearMap.id_apply] at h1 h2
    rw [LinearMap.sub_apply, LinearMap.id_apply, LinearMap.comp_apply, ← Submodule.Quotient.eq,
      h1, h2]
  obtain ⟨s, hs⟩ := Module.projective_lifting_property f.rangeRestrict
    (LinearMap.codRestrict _ _ hmem) f.surjective_rangeRestrict
  refine ⟨s, t, LinearMap.ext fun b => ?_⟩
  have := congrArg Subtype.val (LinearMap.congr_fun hs b)
  simp only [LinearMap.comp_apply, LinearMap.codRestrict_apply, LinearMap.sub_apply,
    LinearMap.id_apply, LinearMap.rangeRestrict] at this
  simp [this]

theorem forall_exact_residueField_of_isLocalRing [IsLocalRing R] {f : A →ₗ[R] B} {g : B →ₗ[R] C}
    (h : Exact (f.lTensor (IsLocalRing.ResidueField R)) (g.lTensor (IsLocalRing.ResidueField R)))
    (m : Ideal R) [m.IsMaximal] :
    Exact (f.lTensor m.ResidueField) (g.lTensor m.ResidueField) :=
  (exact_lTensor_iff_residueField m (IsLocalRing.ResidueField R)
    (IsLocalRing.ker_residue.trans (IsLocalRing.eq_maximalIdeal ‹_›).symm) f g).1 h

theorem exact_of_homotopy {f : A →ₗ[R] B} {g : B →ₗ[R] C} (hfg : g ∘ₗ f = 0)
    {s : B →ₗ[R] A} {t : C →ₗ[R] B} (h : f ∘ₗ s + t ∘ₗ g = LinearMap.id) : Exact f g := by
  intro x
  constructor
  · intro hx
    refine ⟨s x, ?_⟩
    simpa [hx] using LinearMap.congr_fun h x
  · rintro ⟨y, rfl⟩
    exact LinearMap.congr_fun hfg y

end LinearAlgebra

section Comparison

open CategoryTheory Category Limits

set_option backward.isDefEq.respectTransparency false

variable {C D : Type*} [Category* C] [Category* D]

section ShortComplex

variable [HasZeroMorphisms C] [HasZeroMorphisms D] (F : C ⥤ D) [F.PreservesZeroMorphisms]

variable [PreservesColimitsOfShape WalkingParallelPair F]

end ShortComplex

section Complex

variable [HasZeroMorphisms C] [HasZeroMorphisms D] [CategoryWithHomology C]
  [CategoryWithHomology D] (F : C ⥤ D) [F.PreservesZeroMorphisms] {ι : Type*} {c : ComplexShape ι}

variable [PreservesColimitsOfShape WalkingParallelPair F]

end Complex

end Comparison

section Homotopy

open CategoryTheory Category Limits

set_option backward.isDefEq.respectTransparency false

variable {C D : Type*} [Category* C] [Category* D] [Preadditive C] [Preadditive D]
  [CategoryWithHomology C] [CategoryWithHomology D] {ι : Type*} {c : ComplexShape ι}

end Homotopy

section Modules

open CategoryTheory Category Limits

universe u w

variable {R : Type u} [CommRing R] {ι : Type*} {c : ComplexShape ι}

theorem isZero_homology_extendScalars_iff (S : Type w) [CommRing S] [inst : Algebra R S]
    (K : HomologicalComplex (ModuleCat.{u} R) c) {p q r : ι} (hp : c.prev q = p)
    (hr : c.next q = r) :
    IsZero ((((ModuleCat.extendScalars.{u, w, u} (algebraMap R S)).mapHomologicalComplex c).obj
        K).homology q) ↔
      Exact ((K.d p q).hom.lTensor S) ((K.d q r).hom.lTensor S) := by
  obtain ⟨φ, rfl⟩ : ∃ φ : R →+* S, φ.toAlgebra = inst := ⟨_, toAlgebra_algebraMap⟩
  rw [← HomologicalComplex.exactAt_iff_isZero_homology,
    HomologicalComplex.exactAt_iff' _ p q r hp hr,
    ShortComplex.ShortExact.moduleCat_exact_iff_function_exact]
  rfl

end Modules

section Explicit

open CategoryTheory Category Limits ChangeOfRings

universe u

variable {R : Type u} [CommRing R] (S : Type u) [CommRing S] [Algebra R S]
  {ι : Type*} {c : ComplexShape ι}

end Explicit

section Main

open CategoryTheory Category Limits

universe u

variable {R : Type u} [CommRing R]

end Main

end GlobalTheory
