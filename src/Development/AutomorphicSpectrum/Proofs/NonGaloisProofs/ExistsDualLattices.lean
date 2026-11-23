module

public import Formalism.WeaklyAdmissibleFiltrations.Statement
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
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Development.AutomorphicSpectrum.Definitions.NonGaloisLines.TopLine
import Formalism.ConjugateSelfDual.Statement
import Formalism.SharpRestriction.CuspSpanNormBounds.Point
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.RingTheory.Localization.Module

@[expose] public section

open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Module GlobalTheory.CompanionTheory.LocDual

namespace GlobalTheory.CompanionTheory.LocDual.Lat

section Basis

variable {LL : Type} [Field LL] {O : Type} [CommRing O] [Algebra O LL]
  {W : Type} [AddCommGroup W] [Module LL W] [Module O W] [IsScalarTower O LL W]

theorem mem_span_basis {ι : Type} [Fintype ι] (b : Basis ι LL W) (y : W) :
    y ∈ Submodule.span O (Set.range b) ↔ ∀ i, b.repr y i ∈ Set.range (algebraMap O LL) := by
  constructor
  · intro hy
    induction hy using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨j, rfl⟩ := hx
      intro i
      by_cases h : j = i
      · subst h; exact ⟨1, by simp⟩
      · exact ⟨0, by simp [Finsupp.single_apply, h]⟩
    | zero => intro i; exact ⟨0, by simp⟩
    | add x z _ _ hx hz =>
      intro i
      obtain ⟨a, ha⟩ := hx i
      obtain ⟨c, hc⟩ := hz i
      exact ⟨a + c, by simp [ha, hc]⟩
    | smul a x _ hx =>
      intro i
      obtain ⟨c, hc⟩ := hx i
      refine ⟨a * c, ?_⟩
      rw [← algebraMap_smul LL a x, map_smul, Finsupp.smul_apply, ← hc, map_mul, smul_eq_mul]
  · intro h
    rw [← b.sum_repr y]
    refine Submodule.sum_mem _ fun i _ => ?_
    obtain ⟨a, ha⟩ := h i
    rw [← ha, algebraMap_smul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

end Basis

section Dual

variable {LL : Type} [Field LL] {O : Type} [CommRing O] [IsDomain O] [Algebra O LL]
  [IsFractionRing O LL]
  {V : Type} [AddCommGroup V] [Module LL V] [Module O V] [IsScalarTower O LL V]
  [FiniteDimensional LL V]
  {V' : Type} [AddCommGroup V'] [Module LL V'] [Module O V'] [IsScalarTower O LL V']
  [FiniteDimensional LL V']

theorem exists_dual (T : Submodule O V) (hfg : T.FG) (hfree : Module.Free O T)
    (hspan : Submodule.span LL (T : Set V) = ⊤) (P : V →ₗ[LL] V' →ₗ[LL] LL)
    (hr : ∀ y, (∀ x, P x y = 0) → y = 0) (hd : finrank LL V = finrank LL V') :
    ∃ T' : Submodule O V', T'.FG ∧ Module.Free O T' ∧ Submodule.span LL (T' : Set V') = ⊤ ∧
      (∀ y, y ∈ T' ↔ ∀ x ∈ T, ∃ a : O, P x y = algebraMap O LL a) ∧
      (∀ x, x ∈ T ↔ ∀ y ∈ T', ∃ a : O, P x y = algebraMap O LL a) := by
  classical
  haveI : Module.Finite O T := Module.Finite.iff_fg.2 hfg
  let bT := Module.Free.chooseBasis O T
  let ι := Module.Free.ChooseBasisIndex O T
  haveI : Fintype ι := Module.Free.ChooseBasisIndex.fintype O T
  let e : ι → V := fun i => (bT i : V)
  have hli : LinearIndependent O e :=
    bT.linearIndependent.map' T.subtype (Submodule.ker_subtype T)
  have hliL : LinearIndependent LL e := (LinearIndependent.iff_fractionRing O LL).1 hli
  have hTe : T = Submodule.span O (Set.range e) := by
    have h := congrArg (Submodule.map T.subtype) bT.span_eq
    rw [Submodule.map_span, Submodule.map_top, Submodule.range_subtype, ← Set.range_comp] at h
    exact h.symm
  have hsp : ⊤ ≤ Submodule.span LL (Set.range e) := by
    rw [← hspan, Submodule.span_le]
    intro x hx
    rw [SetLike.mem_coe, hTe] at hx
    have := Submodule.span_le_restrictScalars O LL (Set.range e) hx
    exact this
  let bV : Basis ι LL V := Basis.mk hliL hsp
  have hbV : ∀ i, bV i = e i := fun i => Basis.mk_apply hliL hsp i
  have hinj : Function.Injective P.flip := by
    rw [injective_iff_map_eq_zero]
    intro y hy
    exact hr y fun x => by simpa using congrArg (fun f => f x) hy
  let φ : V' ≃ₗ[LL] Dual LL V := LinearMap.linearEquivOfInjective P.flip hinj
    (by rw [Subspace.dual_finrank_eq, hd])
  let bb : Basis ι LL V' := bV.dualBasis.map φ.symm
  have hflip : ∀ j x, P x (bb j) = bV.repr x j := by
    intro j x
    have h1 : φ (bb j) = bV.coord j := by simp [bb]
    have h2 : φ (bb j) x = P x (bb j) := rfl
    rw [← h2, h1]; rfl
  have hcoord : ∀ i y, P (e i) y = bb.repr y i := by
    intro i y
    have : (P (e i)) = bb.coord i := by
      refine bb.ext fun j => ?_
      rw [hflip, ← hbV]
      simp [Finsupp.single_apply, eq_comm]
    rw [this]; rfl
  have hTV : T = Submodule.span O (Set.range bV) := by
    rw [hTe]; congr 2; ext x; simp [hbV]
  have hpair : ∀ x ∈ T, ∀ y ∈ Submodule.span O (Set.range bb), ∃ a : O, P x y = algebraMap O LL a := by
    intro x hx y hy
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨j, rfl⟩ := hy
      rw [hflip]
      rw [hTV] at hx
      obtain ⟨a, ha⟩ := (mem_span_basis bV x).1 hx j
      exact ⟨a, ha.symm⟩
    | zero => exact ⟨0, by simp⟩
    | add y z _ _ hy hz =>
      obtain ⟨a, ha⟩ := hy
      obtain ⟨c, hc⟩ := hz
      exact ⟨a + c, by simp [ha, hc]⟩
    | smul a y _ hy =>
      obtain ⟨c, hc⟩ := hy
      refine ⟨a * c, ?_⟩
      rw [← algebraMap_smul LL a y, map_smul, hc, map_mul, smul_eq_mul]
  refine ⟨Submodule.span O (Set.range bb), Submodule.fg_span (Set.finite_range _), ?_, ?_, ?_, ?_⟩
  · have hl : LinearIndependent O bb :=
      (LinearIndependent.iff_fractionRing O LL).2 bb.linearIndependent
    exact Module.Free.of_basis (Basis.span hl)
  · refine top_le_iff.1 ?_
    rw [← bb.span_eq]
    exact Submodule.span_mono (Submodule.subset_span)
  · intro y
    constructor
    · intro hy x hx
      exact hpair x hx y hy
    · intro h
      refine (mem_span_basis bb y).2 fun i => ?_
      obtain ⟨a, ha⟩ := h (e i) (by rw [hTe]; exact Submodule.subset_span ⟨i, rfl⟩)
      exact ⟨a, by rw [← hcoord, ha]⟩
  · intro x
    constructor
    · intro hx y hy
      exact hpair x hx y hy
    · intro h
      rw [hTV]
      refine (mem_span_basis bV x).2 fun j => ?_
      obtain ⟨a, ha⟩ := h (bb j) (Submodule.subset_span ⟨j, rfl⟩)
      exact ⟨a, by rw [← hflip, ha]⟩

end Dual

section Stable

variable {G : Type} [Group G] [TopologicalSpace G] [CompactSpace G]
  {LL : Type} [Field LL] [TopologicalSpace LL] [IsTopologicalRing LL]
  {O : Type} [CommRing O] [IsDomain O] [IsPrincipalIdealRing O] [Algebra O LL]
  [IsFractionRing O LL]
  {V : Type} [AddCommGroup V] [Module LL V] [Module O V] [IsScalarTower O LL V]
  [FiniteDimensional LL V] [TopologicalSpace V] [IsModuleTopology LL V]

theorem exists_stable (hO : IsOpen (Set.range (algebraMap O LL)))
    (ρ : Representation LL G V) (cont : ∀ x, Continuous fun g => ρ g x) :
    Nonempty (Lattice (O := O) ρ) := by
  classical
  let b : Basis (Fin (finrank LL V)) LL V := Module.finBasis LL V
  have hinj : Function.Injective (algebraMap O LL) := IsFractionRing.injective O LL
  have hc : ∀ i j, Continuous fun g => b.repr (ρ g (b i)) j := by
    intro i j
    have hl : Continuous (b.coord j) := IsModuleTopology.continuous_of_linearMap (b.coord j)
    exact hl.comp (cont (b i))
  let Wa : nonZeroDivisors O → Set G := fun a =>
    {g | ∀ i j, algebraMap O LL a * b.repr (ρ g (b i)) j ∈ Set.range (algebraMap O LL)}
  have hWo : ∀ a, IsOpen (Wa a) := by
    intro a
    have h : Wa a = ⋂ i, ⋂ j, (fun g => algebraMap O LL a * b.repr (ρ g (b i)) j) ⁻¹'
        Set.range (algebraMap O LL) := by
      ext g
      simp only [Wa, Set.mem_setOf_eq, Set.mem_iInter, Set.mem_preimage]
    rw [h]
    exact isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j =>
      hO.preimage (continuous_const.mul (hc i j))
  have hcov : (Set.univ : Set G) ⊆ ⋃ a, Wa a := by
    intro g _
    obtain ⟨d, hd⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors O)
      (Finset.univ : Finset (Fin (finrank LL V) × Fin (finrank LL V)))
      (fun p => b.repr (ρ g (b p.1)) p.2)
    refine Set.mem_iUnion.2 ⟨d, fun i j => ?_⟩
    obtain ⟨c, hc'⟩ := hd (i, j) (Finset.mem_univ _)
    refine ⟨c, ?_⟩
    rw [hc']
    exact Algebra.smul_def (d : O) _
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover Wa hWo hcov
  let a : O := ∏ s ∈ t, (s : O)
  have ha0 : a ≠ 0 := Finset.prod_ne_zero_iff.2 fun s _ => nonZeroDivisors.ne_zero s.2
  have hbound : ∀ g i j, algebraMap O LL a * b.repr (ρ g (b i)) j ∈
      Set.range (algebraMap O LL) := by
    intro g i j
    obtain ⟨s, hs, hg⟩ := Set.mem_iUnion₂.1 (ht (Set.mem_univ g))
    obtain ⟨c, hc'⟩ := hg i j
    obtain ⟨q, hq⟩ := Finset.dvd_prod_of_mem (fun s : nonZeroDivisors O => (s : O)) hs
    have hq' : a = (s : O) * q := hq
    refine ⟨q * c, ?_⟩
    rw [hq', map_mul, map_mul, hc']
    ring
  let T0 : Submodule O V := Submodule.span O (Set.range b)
  let T : Submodule O V := Submodule.span O (Set.range fun p : G × Fin (finrank LL V) => ρ p.1 (b p.2))
  have hTa : ∀ x ∈ T, a • x ∈ T0 := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨⟨g, i⟩, rfl⟩ := hx
      refine (mem_span_basis b _).2 fun j => ?_
      rw [← algebraMap_smul LL a, map_smul, Finsupp.smul_apply, smul_eq_mul]
      exact hbound g i j
    | zero => simp
    | add x z _ _ hx hz => rw [smul_add]; exact T0.add_mem hx hz
    | smul c x _ hx => rw [smul_comm]; exact T0.smul_mem c hx
  let φ : T →ₗ[O] T0 := (a • (LinearMap.id : V →ₗ[O] V)).restrict hTa
  have hφ : Function.Injective φ := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    have h1 : a • (x : V) = 0 := congrArg Subtype.val hx
    rw [← algebraMap_smul LL a, smul_eq_zero] at h1
    rcases h1 with h1 | h1
    · exact absurd ((map_eq_zero_iff _ hinj).1 h1) ha0
    · exact Subtype.ext h1
  have hl0 : LinearIndependent O b :=
    (LinearIndependent.iff_fractionRing O LL).2 b.linearIndependent
  haveI : Module.Free O T0 := Module.Free.of_basis (Basis.span hl0)
  haveI : Module.Finite O T0 := Module.Finite.span_of_finite O (Set.finite_range _)
  haveI : Module.Finite O T := Module.Finite.of_injective φ hφ
  haveI : Module.Free O (LinearMap.range φ) := Module.free_of_finite_type_torsion_free'
  refine ⟨{ T := T, stable := ?_, fg := Module.Finite.iff_fg.1 inferInstance,
            free := Module.Free.of_equiv (LinearEquiv.ofInjective φ hφ).symm, span := ?_ }⟩
  · intro h x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨⟨g, i⟩, rfl⟩ := hx
      refine Submodule.subset_span ⟨(h * g, i), ?_⟩
      simp [map_mul, Module.End.mul_apply]
    | zero => simp
    | add x z _ _ hx hz => rw [map_add (f := _)]; exact T.add_mem hx hz
    | smul c x _ hx =>
      rw [LinearMap.map_smul_of_tower]
      exact T.smul_mem c hx
  · refine top_le_iff.1 ?_
    rw [← b.span_eq]
    refine Submodule.span_mono ?_
    rintro _ ⟨i, rfl⟩
    exact Submodule.subset_span ⟨(1, i), by simp⟩

end Stable

end GlobalTheory.CompanionTheory.LocDual.Lat
