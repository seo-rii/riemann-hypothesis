module

public import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CotDComp
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiscreteProjBundleModelCohomologyEquivProdFibre
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDiscreteSpaceCocycleVanishingPosStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsZeroChains
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

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
open GlobalTheory.EtC.CupSpec GlobalTheory.EtC.DiscCoch in

theorem _root_.GlobalTheory.T.discrete_projBundleModel_cohomology_equiv_prod_fibre :
    ∀ (R : Type) [CommRing R] (q N : ℕ) (I : Cx R) (F : PSh) (n : ℤ),
      ∃ e : CohomologyClass ((chains R).obj (disc.obj F)) (Jcx R q N I) n ≃+
          CohomologyClass ((chains R).obj (disc.obj F ⨯ fibQ q N)) I n,
        ∀ (β : Cocycle ((chains R).obj (disc.obj F)) (Jcx R q N I) n)
          (γ : Cocycle ((chains R).obj (disc.obj F ⨯ fibQ q N)) I n),
          (∀ (p : ℕ), 0 < p → ∀ (s : ℤ) (h : -(p : ℤ) + n = s), β.1.v (-(p : ℤ)) s h = 0) →
          (∀ (U : Scheme.{0}) (x : F.obj (op U)),
            ∃ c : Cochain ((chains R).obj (sch.obj U ⨯ fibQ q N)) I n,
              ev (R := R) β.1 0 n (by simp) U x = Jsec c ∧
              ∀ (k : ℕ) (s : ℤ) (hs : -(k : ℤ) + n = s) (V : Scheme.{0})
                (y : Sx (sch.obj U ⨯ fibQ q N) k V),
                ev (R := R) c k s hs V y =
                  ev (R := R) γ.1 k s hs V
                    (Sx.map (prod.map (disc.map (yonedaEquiv.symm x)) (𝟙 (fibQ q N))) y)) →
          e (CohomologyClass.mk β) = CohomologyClass.mk γ := by
  intro R _ q N I F n
  -- Evaluate cochains on the free generators of the sheaves of chains.
  have ev_def {E : Spc} {L : Cx R} {n : ℤ} (α : Cochain ((chains R).obj E) L n)
      (p : ℕ) (s : ℤ) (h : -(p : ℤ) + n = s) (U : Scheme.{0}) (x : Sx E p U) :
      ev (R := R) α p s h U x = Sec.map ((chainsXIso R E p).inv ≫ α.v _ _ h) (freeGen R _ U x) := rfl
  have ev_ext {E : Spc} {L : Cx R} {n : ℤ} (α β : Cochain ((chains R).obj E) L n)
      (h : ∀ p s h U x, ev (R := R) α p s h U x = ev (R := R) β p s h U x) : α = β := by
    ext p s hs : 1
    by_cases hp : p ≤ 0
    · obtain ⟨k, rfl⟩ : ∃ k : ℕ, p = -(k : ℤ) := ⟨(-p).toNat, by omega⟩
      rw [← cancel_epi (chainsXIso R E k).inv]
      exact free_ext _ _ (fun U x => h k s hs U x)
    · exact (isZero_chains E p (by omega)).eq_of_src _ _
  have ev_exists {E : Spc} {L : Cx R} {n : ℤ}
      (a : ∀ (p : ℕ) (s : ℤ), -(p : ℤ) + n = s → ∀ U : Scheme.{0}, Sx E p U → Sec (L.X s) U)
      (ha : ∀ p s h (V U : Scheme.{0}) (g : V ⟶ U) (x : Sx E p U), Sec.res g (a p s h U x) = a p s h V (x.res g)) :
      ∃ α : Cochain ((chains R).obj E) L n, ∀ p s h U x, ev (R := R) α p s h U x = a p s h U x := by
    have key : ∀ (i j : ℤ) (hij : i + n = j), ∃ φ : ((chains R).obj E).X i ⟶ L.X j, ∀ (p : ℕ) (hp : i = -(p : ℤ)) U x,
        Sec.map ((chainsXIso R E p).inv ≫ eqToHom (congrArg ((chains R).obj E).X hp.symm) ≫ φ) (freeGen R _ U x) =
          a p j (hp ▸ hij) U x := by
      intro i j hij
      by_cases hi : i ≤ 0
      · obtain ⟨k, rfl⟩ : ∃ k : ℕ, i = -(k : ℤ) := ⟨(-i).toNat, by omega⟩
        obtain ⟨φ, hφ⟩ := free_exists (R := R) _ _ (a k j hij) (ha k j hij)
        refine ⟨(chainsXIso R E k).hom ≫ φ, fun p hp U x => ?_⟩
        obtain rfl : k = p := by omega
        rw [eqToHom_refl, Category.id_comp, Iso.inv_hom_id_assoc]
        exact hφ U x
      · exact ⟨0, fun p hp => by omega⟩
    choose φ hφ using key
    refine ⟨Cochain.mk φ, fun p s h U x => ?_⟩
    have := hφ _ _ h p rfl U x
    rw [eqToHom_refl, Category.id_comp] at this
    exact this
  have ev_res {E : Spc} {L : Cx R} {n : ℤ} (α : Cochain ((chains R).obj E) L n)
      (p : ℕ) (s : ℤ) (h : -(p : ℤ) + n = s) {V U : Scheme.{0}} (g : V ⟶ U)
      (x : Sx E p U) : Sec.res g (ev (R := R) α p s h U x) = ev (R := R) α p s h V (x.res g) := by
    rw [ev_def, map_res, freeGen_res]
    rfl
  have ev_add {E : Spc} {L : Cx R} {n : ℤ} (a b : Cochain ((chains R).obj E) L n)
      (p : ℕ) (s : ℤ) (h : -(p : ℤ) + n = s) (U : Scheme.{0}) (x : Sx E p U) :
      ev (R := R) (a + b) p s h U x = ev (R := R) a p s h U x + ev (R := R) b p s h U x := by
    simp [_root_.GlobalTheory.EtC.ev, Cochain.add_v]
  let evHom {E : Spc} (I : Cx R) (n : ℤ) (p : ℕ) (s : ℤ) (h : -(p : ℤ) + n = s) (U : Scheme.{0}) (x : Sx E p U) :
      Cochain ((chains R).obj E) I n →+ Sec (I.X s) U :=
    AddMonoidHom.mk' (fun a => ev (R := R) a p s h U x) (fun a b => ev_add a b p s h U x)
  have ev_zero {E : Spc} {L : Cx R} {n : ℤ} (p : ℕ) (s : ℤ) (h : -(p : ℤ) + n = s) (U : Scheme.{0}) (x : Sx E p U) :
      ev (R := R) (0 : Cochain ((chains R).obj E) L n) p s h U x = 0 := map_zero (evHom L n p s h U x)
  have ev_pull {E : Spc} {L : Cx R} {n : ℤ} {E' : Spc} (f : E' ⟶ E) (α : Cochain ((chains R).obj E) L n)
      (p : ℕ) (s : ℤ) (h : -(p : ℤ) + n = s)
      (U : Scheme.{0}) (x : Sx E' p U) :
      ev (R := R) ((Cochain.ofHom ((chains R).map f)).comp α (zero_add n)) p s h U x = ev (R := R) α p s h U (x.map f) := by
    rw [ev_def, ev_def, Cochain.zero_cochain_comp_v, Cochain.ofHom_v, ← Category.assoc, chains_map, Category.assoc]
    change Sec.map ((chainsXIso R E p).inv ≫ α.v _ _ h) (Sec.map ((free R).map _) (freeGen R _ U x)) = _
    rw [freeGen_map]
    rfl
  have ev_δ_zero {E : Spc} {L : Cx R} {n : ℤ} {m : ℤ} (hm : n + 1 = m)
      (α : Cochain ((chains R).obj E) L n) (U : Scheme.{0}) (s t : ℤ)
      (hs : -((0 : ℕ) : ℤ) + n = s) (ht : -((0 : ℕ) : ℤ) + m = t) (x : Sx E 0 U) :
      ev (R := R) (δ n m α) 0 t ht U x = Sec.map (L.d s t) (ev (R := R) α 0 s hs U x) := by
    rw [ev_def, δ_v n m hm α _ t ht s 1 (by omega) (by simp),
      (isZero_chains E 1 one_pos).eq_of_tgt (((chains R).obj E).d _ 1) 0, zero_comp, smul_zero, add_zero]
    rfl
  have ev_δ_succ {E : Spc} {L : Cx R} {n : ℤ} {m : ℤ} (hm : n + 1 = m)
      (α : Cochain ((chains R).obj E) L n) (U : Scheme.{0}) (p : ℕ) (s t : ℤ)
      (hs : -((p + 1 : ℕ) : ℤ) + n = s) (ht : -((p + 1 : ℕ) : ℤ) + m = t) (x : Sx E (p + 1) U) :
      ev (R := R) (δ n m α) (p + 1) t ht U x = Sec.map (L.d s t) (ev (R := R) α (p + 1) s hs U x) +
        m.negOnePow • ∑ i : Fin (p + 2), (-1 : ℤ) ^ (i : ℕ) • ev (R := R) α p t (by omega) U (x.face i) := by
    rw [ev_def, δ_v n m hm α _ t ht s (-(p : ℤ)) (by omega) (by omega), Preadditive.comp_add, Units.smul_def,
      Preadditive.comp_zsmul, ← Category.assoc _ (((chains R).obj E).d _ _), chains_d, Category.assoc, Preadditive.sum_comp]
    refine (map_add (mapHom _ _ (freeGen R _ U x)) _ _).trans ?_

    rw [map_zsmul, map_sum, Units.smul_def]
    refine congrArg₂ (· + ·) rfl (congrArg _ (Finset.sum_congr rfl fun i _ => ?_))
    rw [Preadditive.zsmul_comp, map_zsmul]
    congr 1
    change Sec.map ((chainsXIso R E p).inv ≫ α.v _ _ _) (Sec.map ((free R).map _) (freeGen R _ U x)) = _
    rw [freeGen_map]
    rfl
  have ev_zero_of_v {E : Spc} {L : Cx R} {n : ℤ} (β : Cochain ((chains R).obj E) L n)
      (p : ℕ) (s : ℤ)
    (h : -(p : ℤ) + n = s) (hβ : β.v (-(p : ℤ)) s h = 0) (U : Scheme.{0}) (x : Sx E p U) : ev (R := R) β p s h U x = 0 := by
    rw [ev_def, hβ, comp_zero]
    rfl
  have conc_δ {L : Cx R} {n m : ℤ} (hm : n + 1 = m) (β : Cochain ((chains R).obj (disc.obj F)) L n)
    (hβ : ∀ (p : ℕ) s h U x, ev (R := R) β (p + 1) s h U x = 0) :
    ∀ (p : ℕ) s h U x, ev (R := R) (δ n m β) (p + 1) s h U x = 0 := by
    intro p s h U x
    rw [ev_δ_succ hm β U p (s - m + n) s (by omega) h x, hβ, sec_map_at_zero, zero_add]
    cases p with
    | zero =>
      have hf : ∀ i, Sx.face x i = x := fun i => rfl
      simp [Fin.sum_univ_two, hf]
    | succ p => simp [hβ]

  -- Lift the pullbacks to a cochain supported in simplicial degree zero.
  have exS {n : ℤ} (γ : Cochain ((chains R).obj (disc.obj F ⨯ fibQ q N)) I n) :
    ∃ β : Cochain ((chains R).obj (disc.obj F)) (Jcx R q N I) n,
      (∀ (U : Scheme.{0}) (x : F.obj (op U)), ev (R := R) β 0 n (by simp) U x = Jsec (ptPull γ x)) ∧
      ∀ (p : ℕ) s h U x, ev (R := R) β (p + 1) s h U x = 0 := by
    obtain ⟨β, hβ⟩ := ev_exists (E := disc.obj F) (L := Jcx R q N I) (n := n) (aS γ) (by
      intro p s h V U g x
      cases p with
      | zero =>
        obtain rfl : n = s := by omega
        exact (jsec_res g _).trans (congrArg Jsec (ptPull_res γ g x).symm)
      | succ p => exact map_zero _)
    exact ⟨β, fun U x => hβ 0 n _ U x, fun p s h U x => hβ (p + 1) s h U x⟩
  choose S hS0 hS1 using fun (m : ℤ) (γ : Cochain ((chains R).obj (disc.obj F ⨯ fibQ q N)) I m) => exS γ
  have hSδ : ∀ (m m' : ℤ) (hm : m + 1 = m') (η : Cochain ((chains R).obj (disc.obj F ⨯ fibQ q N)) I m),
      S m' (δ m m' η) = δ m m' (S m η) := by
    intro m m' hm η
    apply ev_ext
    intro p s h U x
    cases p with
    | zero =>
      obtain rfl : m' = s := by omega
      rw [hS0, ev_δ_zero hm (S m η) U m m' (by simp) h x, hS0, jsec_d hm, ptPull_δ hm]
    | succ p => rw [hS1, conc_δ hm _ (hS1 m η)]
  have hSadd : ∀ (γ γ' : Cochain ((chains R).obj (disc.obj F ⨯ fibQ q N)) I n), S n (γ + γ') = S n γ + S n γ' := by
    intro γ γ'
    apply ev_ext
    intro p s h U x
    rw [ev_add]
    cases p with
    | zero =>
      obtain rfl : n = s := by omega
      rw [hS0, hS0, hS0, ptPull_add, jsec_add]
    | succ p => rw [hS1, hS1, hS1, add_zero]
  have hSzero : ∀ m : ℤ, S m 0 = 0 := by
    intro m
    apply ev_ext
    intro p s h U x
    rw [ev_zero]
    cases p with
    | zero =>
      obtain rfl : m = s := by omega
      rw [hS0, ptPull_zero, jsec_zero]
    | succ p => rw [hS1]
  have hScyc : ∀ γ : Cocycle ((chains R).obj (disc.obj F ⨯ fibQ q N)) I n, δ n (n + 1) (S n γ.1) = 0 := by
    intro γ
    rw [← hSδ n (n + 1) rfl, Cocycle.δ_eq_zero, hSzero]
  let Sc : Cocycle ((chains R).obj (disc.obj F ⨯ fibQ q N)) I n →+
      CohomologyClass ((chains R).obj (disc.obj F)) (Jcx R q N I) n :=
    AddMonoidHom.mk' (fun γ => CohomologyClass.mk (Cocycle.mk (S n γ.1) (n + 1) rfl (hScyc γ))) (by
      intro a b
      rw [← CohomologyClass.mk_add]
      exact congrArg CohomologyClass.mk (Cocycle.ext (hSadd a.1 b.1)))
  have hcob : coboundaries ((chains R).obj (disc.obj F ⨯ fibQ q N)) I n ≤ Sc.ker := by
    rintro ⟨γ, hγ⟩ ⟨n', hn', η, rfl⟩
    change CohomologyClass.mk _ = 0
    rw [CohomologyClass.mk_eq_zero_iff]
    exact ⟨n', hn', S n' η, (hSδ n' n hn' η).symm⟩
  let Φ := CohomologyClass.descAddMonoidHom Sc hcob
  have hnat : ∀ (m : ℤ) (b : Cochain ((chains R).obj (disc.obj F)) (Jcx R q N I) m)
      (c' : ∀ U : Scheme.{0}, F.obj (op U) → Cochain ((chains R).obj (sch.obj U ⨯ fibQ q N)) I m),
      (∀ U x, Jsec (c' U x) = ev (R := R) b 0 m (by simp) U x) →
      ∀ (V U : Scheme.{0}) (g : V ⟶ U) (x : F.obj (op U)), c' V (F.map g.op x) =
        (Cochain.ofHom ((chains R).map (prod.map (sch.map g) (𝟙 (fibQ q N))))).comp (c' U x) (zero_add m) := by
    intro m b c' hc' V U g x
    apply (jsec_bij R q N I m V).1
    change Jsec _ = Jsec _
    rw [hc', ← jsec_res, hc', ev_res]
    rfl
  have hΦinj : Function.Injective Φ := by
    rw [injective_iff_map_eq_zero]
    intro c hc
    obtain ⟨γ, rfl⟩ := c.mk_surjective
    change CohomologyClass.mk _ = 0 at hc
    rw [CohomologyClass.mk_eq_zero_iff] at hc
    obtain ⟨n', hn', β', hβ'⟩ := hc
    have hc' : ∀ (U : Scheme.{0}) (x : F.obj (op U)), ∃ c : Cochain ((chains R).obj (sch.obj U ⨯ fibQ q N)) I n',
        Jsec c = ev (R := R) β' 0 n' (by simp) U x := fun U x => (jsec_bij R q N I n' U).2 _
    choose c' hc' using hc'
    obtain ⟨η, hη, -⟩ := glue R q N I F n' c' (hnat n' β' c' hc')
    have h2 : ∀ (U : Scheme.{0}) (x : F.obj (op U)), ptPull (δ n' n η) x = ptPull γ.1 x := by
      intro U x
      have h1 : ptPull η x = c' U x := hη U x
      rw [ptPull_δ hn', h1]
      apply (jsec_bij R q N I n U).1
      change Jsec _ = Jsec _
      rw [← jsec_d hn', hc', ← ev_δ_zero hn' β' U n' n (by simp) (by simp) x]
      rw [hβ']
      exact hS0 n γ.1 U x
    have huniq := (glue R q N I F n (fun U x => ptPull γ.1 x) (fun V U g x => ptPull_res γ.1 g x)).unique
      (y₁ := γ.1) (y₂ := δ n' n η) (fun U x => rfl) h2
    rw [CohomologyClass.mk_eq_zero_iff]
    exact ⟨n', hn', η, huniq.symm⟩
  have hΦsurj : Function.Surjective Φ := by
    intro c
    obtain ⟨α, hαc, hα0⟩ := GlobalTheory.T.exists_discreteSpace_cocycle_vanishing_pos R F (Jcx R q N I) n c
    have hc' : ∀ (U : Scheme.{0}) (x : F.obj (op U)), ∃ c : Cochain ((chains R).obj (sch.obj U ⨯ fibQ q N)) I n,
        Jsec c = ev (R := R) α.1 0 n (by simp) U x := fun U x => (jsec_bij R q N I n U).2 _
    choose c' hc' using hc'
    obtain ⟨γ, hγ, -⟩ := glue R q N I F n c' (hnat n α.1 c' hc')
    have hδ : δ n (n + 1) γ = 0 := by
      refine (glue R q N I F (n + 1) (fun U x => 0) (fun V U g x => (Cochain.comp_zero _ _).symm)).unique
        (fun U x => ?_) (fun U x => Cochain.comp_zero _ _)
      show ptPull (δ n (n + 1) γ) x = 0
      rw [ptPull_δ rfl, show ptPull γ x = c' U x from hγ U x]
      apply (jsec_bij R q N I (n + 1) U).1
      change Jsec _ = Jsec _
      rw [← jsec_d rfl, hc', ← ev_δ_zero rfl α.1 U n (n + 1) (by simp) (by simp) x, Cocycle.δ_eq_zero, ev_zero,
        jsec_zero]
    refine ⟨CohomologyClass.mk (Cocycle.mk γ (n + 1) rfl hδ), ?_⟩
    rw [← hαc]
    change CohomologyClass.mk _ = _
    congr 1
    apply Cocycle.ext
    apply ev_ext
    intro p s h U x
    cases p with
    | zero =>
      obtain rfl : n = s := by omega
      show ev (R := R) (S n γ) 0 n h U x = ev (R := R) α.1 0 n h U x
      rw [hS0, show ptPull γ x = c' U x from hγ U x, hc']
    | succ p =>
      show ev (R := R) (S n γ) (p + 1) s h U x = ev (R := R) α.1 (p + 1) s h U x
      rw [hS1, ev_zero_of_v _ _ _ _ (hα0 (p + 1) (by omega) s h)]
  refine ⟨(AddEquiv.ofBijective Φ ⟨hΦinj, hΦsurj⟩).symm, fun β γ hβ0 hβc => ?_⟩
  rw [AddEquiv.symm_apply_eq]
  change CohomologyClass.mk β = CohomologyClass.mk _
  congr 1
  apply Cocycle.ext
  apply ev_ext
  intro p s h U x
  cases p with
  | zero =>
    obtain rfl : n = s := by omega
    obtain ⟨c, hc1, hc2⟩ := hβc U x
    show ev (R := R) β.1 0 n h U x = ev (R := R) (S n γ.1) 0 n h U x
    rw [hS0, hc1]
    congr 1
    apply ev_ext
    intro k s hs V y
    rw [hc2]
    exact (ev_pull _ γ.1 k s hs V y).symm
  | succ p =>
    show ev (R := R) β.1 (p + 1) s h U x = ev (R := R) (S n γ.1) (p + 1) s h U x
    rw [hS1, ev_zero_of_v _ _ _ _ (hβ0 (p + 1) (by omega) s h)]
