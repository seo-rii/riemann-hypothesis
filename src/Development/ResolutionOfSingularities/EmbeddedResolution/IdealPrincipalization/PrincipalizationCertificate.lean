module

public import Mathlib
public import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.StrictNormalCrossings
public import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.IdealSheafOrder

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace FunctorialResolution.EmbeddedResolution

/-- Which of the two certificate families a `Certificate` belongs to. -/
inductive CertificateKind
  | principalization
  | order

/-- Principalization certificates (`.principalization`) and order certificates (`.order`) as
one inductive family.

The two families used to be a `mutual` block. Its members are reflexive (`localize` and
`descend` take functions into the family), and the external checkers con-leche and con-ron
refuse a mutual block with a reflexive member, while they accept a single reflexive inductive.
`PrincipalizationCertificate` and `OrderCertificate` below keep the old names, constructors and
recursors. -/
inductive Certificate {k : Type u} [Field k] :
    CertificateKind → ∀ (W : Scheme.{u}), (W ⟶ Spec (CommRingCat.of k)) → W.IdealSheafData → ℕ →
      Set ↥W → W.IdealSheafData → Prop
  | principalizationMemory {W : Scheme.{u}} {p : W ⟶ Spec (CommRingCat.of k)}
      {I : W.IdealSheafData} {m : ℕ} {Mem : Set ↥W} {Z : W.IdealSheafData}
      (h : (Z.support : Set ↥W) ⊆ Mem) :
      Certificate .principalization W p I m Mem Z
  | principalizationLarge {W : Scheme.{u}} {p : W ⟶ Spec (CommRingCat.of k)}
      {I : W.IdealSheafData} {m : ℕ} {Mem : Set ↥W} {Z : W.IdealSheafData}
      (hm : 2 ≤ m) :
      Certificate .principalization W p I m Mem Z
  | principalizationToOrder {W : Scheme.{u}} {p : W ⟶ Spec (CommRingCat.of k)}
      {I : W.IdealSheafData} {m : ℕ} {Mem : Set ↥W} {Z : W.IdealSheafData}
      (M N : W.IdealSheafData) (μ : ℕ)
      (hI : I = M * N)
      (hM : (M.support : Set ↥W) ⊆ Mem)
      (hmu : m ≤ μ)
      (hZ : (Z.support : Set ↥W) ⊆ orderAtLeastLocus N μ)
      (hcert : Certificate .order W p N μ Mem Z) :
      Certificate .principalization W p I m Mem Z
  | principalizationLocalize {W : Scheme.{u}} {p : W ⟶ Spec (CommRingCat.of k)}
      {I : W.IdealSheafData} {m : ℕ} {Mem : Set ↥W} {Z : W.IdealSheafData}
      (U : ∀ z : ↥W, z ∈ Z.support → W.Opens)
      (hU : ∀ (z : ↥W) (hz : z ∈ Z.support), z ∈ U z hz)
      (hcert : ∀ (z : ↥W) (hz : z ∈ Z.support),
        Certificate .principalization (U z hz).toScheme ((U z hz).ι ≫ p) (I.comap (U z hz).ι) m
          ((U z hz).ι.base ⁻¹' Mem) (Z.comap (U z hz).ι)) :
      Certificate .principalization W p I m Mem Z
  | orderMemory {W : Scheme.{u}} {p : W ⟶ Spec (CommRingCat.of k)}
      {N : W.IdealSheafData} {μ : ℕ} {Mem : Set ↥W} {Z : W.IdealSheafData}
      (h : (Z.support : Set ↥W) ⊆ Mem) :
      Certificate .order W p N μ Mem Z
  | orderLarge {W : Scheme.{u}} {p : W ⟶ Spec (CommRingCat.of k)}
      {N : W.IdealSheafData} {μ : ℕ} {Mem : Set ↥W} {Z : W.IdealSheafData}
      (hmu : 2 ≤ μ) :
      Certificate .order W p N μ Mem Z
  | orderLocalize {W : Scheme.{u}} {p : W ⟶ Spec (CommRingCat.of k)}
      {N : W.IdealSheafData} {μ : ℕ} {Mem : Set ↥W} {Z : W.IdealSheafData}
      (U : ∀ z : ↥W, z ∈ Z.support → W.Opens)
      (hU : ∀ (z : ↥W) (hz : z ∈ Z.support), z ∈ U z hz)
      (hcert : ∀ (z : ↥W) (hz : z ∈ Z.support),
        Certificate .order (U z hz).toScheme ((U z hz).ι ≫ p) (N.comap (U z hz).ι) μ
          ((U z hz).ι.base ⁻¹' Mem) (Z.comap (U z hz).ι)) :
      Certificate .order W p N μ Mem Z
  | orderDescend {W : Scheme.{u}} {p : W ⟶ Spec (CommRingCat.of k)}
      {N : W.IdealSheafData} {μ : ℕ} {Mem : Set ↥W} {Z : W.IdealSheafData}
      (U : ∀ z : ↥W, z ∈ Z.support → W.Opens)
      (hU : ∀ (z : ↥W) (hz : z ∈ Z.support), z ∈ U z hz)
      (H : ∀ (z : ↥W) (hz : z ∈ Z.support), (U z hz).toScheme.IdealSheafData)
      (hH : ∀ (z : ↥W) (hz : z ∈ Z.support),
        IsSmoothDivisor ((U z hz).ι ≫ p) (H z hz))
      (hNsubH : ∀ (z : ↥W) (hz : z ∈ Z.support),
        (((N.comap (U z hz).ι).support : Set ↥(U z hz).toScheme)) ⊆
          ((H z hz).support : Set ↥(U z hz).toScheme))
      (hZH : ∀ (z : ↥W) (hz : z ∈ Z.support),
        (((Z.comap (U z hz).ι).support : Set ↥(U z hz).toScheme)) ⊆
          ((H z hz).support : Set ↥(U z hz).toScheme))
      (J : ∀ (z : ↥W) (hz : z ∈ Z.support), Option ((H z hz).subscheme.IdealSheafData))
      (hJnone : ∀ (z : ↥W) (hz : z ∈ Z.support), J z hz = none →
        IsOpen ((H z hz).subschemeι.base ⁻¹'
          (((Z.comap (U z hz).ι).support : Set ↥(U z hz).toScheme))))
      (hJcomp : ∀ (z : ↥W) (hz : z ∈ Z.support) (Jz : (H z hz).subscheme.IdealSheafData),
        J z hz = some Jz → NonzeroOnComponents Jz)
      (hJloc : ∀ (z : ↥W) (hz : z ∈ Z.support) (Jz : (H z hz).subscheme.IdealSheafData),
        J z hz = some Jz →
        ∀ x : ↥(H z hz).subscheme,
          ((H z hz).subschemeι ≫ (U z hz).ι).base x ∉ Mem →
          ∃ V : (H z hz).subscheme.Opens, x ∈ V ∧
            Jz.comap V.ι =
              (((N.comap (U z hz).ι).comap (H z hz).subschemeι)).comap V.ι)
      (hJcert : ∀ (z : ↥W) (hz : z ∈ Z.support) (Jz : (H z hz).subscheme.IdealSheafData),
        J z hz = some Jz →
        Certificate .principalization (H z hz).subscheme
          ((H z hz).subschemeι ≫ (U z hz).ι ≫ p) Jz μ
          (((H z hz).subschemeι ≫ (U z hz).ι).base ⁻¹' Mem)
          ((Z.comap (U z hz).ι).comap (H z hz).subschemeι)) :
      Certificate .order W p N μ Mem Z

/-- A principalization certificate: `Certificate .principalization`. -/
def PrincipalizationCertificate {k : Type u} [Field k] (W : Scheme.{u})
    (p : W ⟶ Spec (CommRingCat.of k)) (I : W.IdealSheafData) (m : ℕ) (Mem : Set ↥W)
    (Z : W.IdealSheafData) : Prop :=
  Certificate .principalization W p I m Mem Z

/-- An order certificate: `Certificate .order`. -/
def OrderCertificate {k : Type u} [Field k] (W : Scheme.{u})
    (p : W ⟶ Spec (CommRingCat.of k)) (N : W.IdealSheafData) (μ : ℕ) (Mem : Set ↥W)
    (Z : W.IdealSheafData) : Prop :=
  Certificate .order W p N μ Mem Z

/-! ### The constructors of the former mutual block -/

theorem PrincipalizationCertificate.memory {k : Type u} [Field k] {W : Scheme.{u}}
    {p : W ⟶ Spec (CommRingCat.of k)} {I : W.IdealSheafData} {m : ℕ}
    {Mem : Set ↥W} {Z : W.IdealSheafData}
    (h : (Z.support : Set ↥W) ⊆ Mem) :
    PrincipalizationCertificate W p I m Mem Z :=
  Certificate.principalizationMemory h

theorem PrincipalizationCertificate.large {k : Type u} [Field k] {W : Scheme.{u}}
    {p : W ⟶ Spec (CommRingCat.of k)} {I : W.IdealSheafData} {m : ℕ}
    {Mem : Set ↥W} {Z : W.IdealSheafData}
    (hm : 2 ≤ m) :
    PrincipalizationCertificate W p I m Mem Z :=
  Certificate.principalizationLarge hm

theorem PrincipalizationCertificate.toOrder {k : Type u} [Field k] {W : Scheme.{u}}
    {p : W ⟶ Spec (CommRingCat.of k)} {I : W.IdealSheafData} {m : ℕ}
    {Mem : Set ↥W} {Z : W.IdealSheafData}
    (M N : W.IdealSheafData) (μ : ℕ)
    (hI : I = M * N)
    (hM : (M.support : Set ↥W) ⊆ Mem)
    (hmu : m ≤ μ)
    (hZ : (Z.support : Set ↥W) ⊆ orderAtLeastLocus N μ)
    (hcert : OrderCertificate W p N μ Mem Z) :
    PrincipalizationCertificate W p I m Mem Z :=
  Certificate.principalizationToOrder M N μ hI hM hmu hZ hcert

theorem PrincipalizationCertificate.localize {k : Type u} [Field k] {W : Scheme.{u}}
    {p : W ⟶ Spec (CommRingCat.of k)} {I : W.IdealSheafData} {m : ℕ}
    {Mem : Set ↥W} {Z : W.IdealSheafData}
    (U : ∀ z : ↥W, z ∈ Z.support → W.Opens)
    (hU : ∀ (z : ↥W) (hz : z ∈ Z.support), z ∈ U z hz)
    (hcert : ∀ (z : ↥W) (hz : z ∈ Z.support),
      PrincipalizationCertificate (U z hz).toScheme ((U z hz).ι ≫ p) (I.comap (U z hz).ι) m
        ((U z hz).ι.base ⁻¹' Mem) (Z.comap (U z hz).ι)) :
    PrincipalizationCertificate W p I m Mem Z :=
  Certificate.principalizationLocalize U hU hcert

theorem OrderCertificate.memory {k : Type u} [Field k] {W : Scheme.{u}}
    {p : W ⟶ Spec (CommRingCat.of k)} {N : W.IdealSheafData} {μ : ℕ}
    {Mem : Set ↥W} {Z : W.IdealSheafData}
    (h : (Z.support : Set ↥W) ⊆ Mem) :
    OrderCertificate W p N μ Mem Z :=
  Certificate.orderMemory h

theorem OrderCertificate.large {k : Type u} [Field k] {W : Scheme.{u}}
    {p : W ⟶ Spec (CommRingCat.of k)} {N : W.IdealSheafData} {μ : ℕ}
    {Mem : Set ↥W} {Z : W.IdealSheafData}
    (hmu : 2 ≤ μ) :
    OrderCertificate W p N μ Mem Z :=
  Certificate.orderLarge hmu

theorem OrderCertificate.localize {k : Type u} [Field k] {W : Scheme.{u}}
    {p : W ⟶ Spec (CommRingCat.of k)} {N : W.IdealSheafData} {μ : ℕ}
    {Mem : Set ↥W} {Z : W.IdealSheafData}
    (U : ∀ z : ↥W, z ∈ Z.support → W.Opens)
    (hU : ∀ (z : ↥W) (hz : z ∈ Z.support), z ∈ U z hz)
    (hcert : ∀ (z : ↥W) (hz : z ∈ Z.support),
      OrderCertificate (U z hz).toScheme ((U z hz).ι ≫ p) (N.comap (U z hz).ι) μ
        ((U z hz).ι.base ⁻¹' Mem) (Z.comap (U z hz).ι)) :
    OrderCertificate W p N μ Mem Z :=
  Certificate.orderLocalize U hU hcert

theorem OrderCertificate.descend {k : Type u} [Field k] {W : Scheme.{u}}
    {p : W ⟶ Spec (CommRingCat.of k)} {N : W.IdealSheafData} {μ : ℕ}
    {Mem : Set ↥W} {Z : W.IdealSheafData}
    (U : ∀ z : ↥W, z ∈ Z.support → W.Opens)
    (hU : ∀ (z : ↥W) (hz : z ∈ Z.support), z ∈ U z hz)
    (H : ∀ (z : ↥W) (hz : z ∈ Z.support), (U z hz).toScheme.IdealSheafData)
    (hH : ∀ (z : ↥W) (hz : z ∈ Z.support),
      IsSmoothDivisor ((U z hz).ι ≫ p) (H z hz))
    (hNsubH : ∀ (z : ↥W) (hz : z ∈ Z.support),
      (((N.comap (U z hz).ι).support : Set ↥(U z hz).toScheme)) ⊆
        ((H z hz).support : Set ↥(U z hz).toScheme))
    (hZH : ∀ (z : ↥W) (hz : z ∈ Z.support),
      (((Z.comap (U z hz).ι).support : Set ↥(U z hz).toScheme)) ⊆
        ((H z hz).support : Set ↥(U z hz).toScheme))
    (J : ∀ (z : ↥W) (hz : z ∈ Z.support), Option ((H z hz).subscheme.IdealSheafData))
    (hJnone : ∀ (z : ↥W) (hz : z ∈ Z.support), J z hz = none →
      IsOpen ((H z hz).subschemeι.base ⁻¹'
        (((Z.comap (U z hz).ι).support : Set ↥(U z hz).toScheme))))
    (hJcomp : ∀ (z : ↥W) (hz : z ∈ Z.support) (Jz : (H z hz).subscheme.IdealSheafData),
      J z hz = some Jz → NonzeroOnComponents Jz)
    (hJloc : ∀ (z : ↥W) (hz : z ∈ Z.support) (Jz : (H z hz).subscheme.IdealSheafData),
      J z hz = some Jz →
      ∀ x : ↥(H z hz).subscheme,
        ((H z hz).subschemeι ≫ (U z hz).ι).base x ∉ Mem →
        ∃ V : (H z hz).subscheme.Opens, x ∈ V ∧
          Jz.comap V.ι =
            (((N.comap (U z hz).ι).comap (H z hz).subschemeι)).comap V.ι)
    (hJcert : ∀ (z : ↥W) (hz : z ∈ Z.support) (Jz : (H z hz).subscheme.IdealSheafData),
      J z hz = some Jz →
      PrincipalizationCertificate (H z hz).subscheme ((H z hz).subschemeι ≫ (U z hz).ι ≫ p) Jz μ
        (((H z hz).subschemeι ≫ (U z hz).ι).base ⁻¹' Mem)
        ((Z.comap (U z hz).ι).comap (H z hz).subschemeι)) :
    OrderCertificate W p N μ Mem Z :=
  Certificate.orderDescend U hU H hH hNsubH hZH J hJnone hJcomp hJloc hJcert

/-! ### The recursors of the former mutual block

`PrincipalizationCertificate.rec` and `OrderCertificate.rec` have the types of the recursors
Lean generated for the mutual block: two motives, the eight minor premises in the same order,
then the major premise. Both follow from `Certificate.rec`, with `motive_1` or `motive_2`
chosen by the certificate's kind. -/

theorem PrincipalizationCertificate.rec {k : Type u} [Field k]
    {motive_1 : ∀ (W : Scheme.{u}) (a : W ⟶ Spec (CommRingCat.of k)) (a_1 : W.IdealSheafData)
      (a_2 : ℕ) (a_3 : Set ↥W) (a_4 : W.IdealSheafData),
      PrincipalizationCertificate W a a_1 a_2 a_3 a_4 → Prop}
    {motive_2 : ∀ (W : Scheme.{u}) (a : W ⟶ Spec (CommRingCat.of k)) (a_1 : W.IdealSheafData)
      (a_2 : ℕ) (a_3 : Set ↥W) (a_4 : W.IdealSheafData),
      OrderCertificate W a a_1 a_2 a_3 a_4 → Prop}
    (memory : ∀ {W : Scheme.{u}} {p : W ⟶ Spec (CommRingCat.of k)} {I : W.IdealSheafData}
      {m : ℕ} {Mem : Set ↥W} {Z : W.IdealSheafData} (h : (Z.support : Set ↥W) ⊆ Mem),
      motive_1 W p I m Mem Z (PrincipalizationCertificate.memory h))
    (large : ∀ {W : Scheme.{u}} {p : W ⟶ Spec (CommRingCat.of k)} {I : W.IdealSheafData}
      {m : ℕ} {Mem : Set ↥W} {Z : W.IdealSheafData} (hm : 2 ≤ m),
      motive_1 W p I m Mem Z (PrincipalizationCertificate.large hm))
    (toOrder : ∀ {W : Scheme.{u}} {p : W ⟶ Spec (CommRingCat.of k)} {I : W.IdealSheafData}
      {m : ℕ} {Mem : Set ↥W} {Z : W.IdealSheafData} (M N : W.IdealSheafData) (μ : ℕ)
      (hI : I = M * N) (hM : (M.support : Set ↥W) ⊆ Mem) (hmu : m ≤ μ)
      (hZ : (Z.support : Set ↥W) ⊆ orderAtLeastLocus N μ)
      (hcert : OrderCertificate W p N μ Mem Z),
      motive_2 W p N μ Mem Z hcert →
        motive_1 W p I m Mem Z (PrincipalizationCertificate.toOrder M N μ hI hM hmu hZ hcert))
    (localize : ∀ {W : Scheme.{u}} {p : W ⟶ Spec (CommRingCat.of k)} {I : W.IdealSheafData}
      {m : ℕ} {Mem : Set ↥W} {Z : W.IdealSheafData}
      (U : ∀ z : ↥W, z ∈ Z.support → W.Opens)
      (hU : ∀ (z : ↥W) (hz : z ∈ Z.support), z ∈ U z hz)
      (hcert : ∀ (z : ↥W) (hz : z ∈ Z.support),
        PrincipalizationCertificate (U z hz).toScheme ((U z hz).ι ≫ p) (I.comap (U z hz).ι) m
          ((U z hz).ι.base ⁻¹' Mem) (Z.comap (U z hz).ι)),
      (∀ (z : ↥W) (hz : z ∈ Z.support),
        motive_1 (U z hz).toScheme ((U z hz).ι ≫ p) (I.comap (U z hz).ι) m
          ((U z hz).ι.base ⁻¹' Mem) (Z.comap (U z hz).ι) (hcert z hz)) →
        motive_1 W p I m Mem Z (PrincipalizationCertificate.localize U hU hcert))
    (orderMemory : ∀ {W : Scheme.{u}} {p : W ⟶ Spec (CommRingCat.of k)} {N : W.IdealSheafData}
      {μ : ℕ} {Mem : Set ↥W} {Z : W.IdealSheafData} (h : (Z.support : Set ↥W) ⊆ Mem),
      motive_2 W p N μ Mem Z (OrderCertificate.memory h))
    (orderLarge : ∀ {W : Scheme.{u}} {p : W ⟶ Spec (CommRingCat.of k)} {N : W.IdealSheafData}
      {μ : ℕ} {Mem : Set ↥W} {Z : W.IdealSheafData} (hmu : 2 ≤ μ),
      motive_2 W p N μ Mem Z (OrderCertificate.large hmu))
    (orderLocalize : ∀ {W : Scheme.{u}} {p : W ⟶ Spec (CommRingCat.of k)}
      {N : W.IdealSheafData} {μ : ℕ} {Mem : Set ↥W} {Z : W.IdealSheafData}
      (U : ∀ z : ↥W, z ∈ Z.support → W.Opens)
      (hU : ∀ (z : ↥W) (hz : z ∈ Z.support), z ∈ U z hz)
      (hcert : ∀ (z : ↥W) (hz : z ∈ Z.support),
        OrderCertificate (U z hz).toScheme ((U z hz).ι ≫ p) (N.comap (U z hz).ι) μ
          ((U z hz).ι.base ⁻¹' Mem) (Z.comap (U z hz).ι)),
      (∀ (z : ↥W) (hz : z ∈ Z.support),
        motive_2 (U z hz).toScheme ((U z hz).ι ≫ p) (N.comap (U z hz).ι) μ
          ((U z hz).ι.base ⁻¹' Mem) (Z.comap (U z hz).ι) (hcert z hz)) →
        motive_2 W p N μ Mem Z (OrderCertificate.localize U hU hcert))
    (descend : ∀ {W : Scheme.{u}} {p : W ⟶ Spec (CommRingCat.of k)} {N : W.IdealSheafData}
      {μ : ℕ} {Mem : Set ↥W} {Z : W.IdealSheafData}
      (U : ∀ z : ↥W, z ∈ Z.support → W.Opens)
      (hU : ∀ (z : ↥W) (hz : z ∈ Z.support), z ∈ U z hz)
      (H : ∀ (z : ↥W) (hz : z ∈ Z.support), (U z hz).toScheme.IdealSheafData)
      (hH : ∀ (z : ↥W) (hz : z ∈ Z.support),
        IsSmoothDivisor ((U z hz).ι ≫ p) (H z hz))
      (hNsubH : ∀ (z : ↥W) (hz : z ∈ Z.support),
        (((N.comap (U z hz).ι).support : Set ↥(U z hz).toScheme)) ⊆
          ((H z hz).support : Set ↥(U z hz).toScheme))
      (hZH : ∀ (z : ↥W) (hz : z ∈ Z.support),
        (((Z.comap (U z hz).ι).support : Set ↥(U z hz).toScheme)) ⊆
          ((H z hz).support : Set ↥(U z hz).toScheme))
      (J : ∀ (z : ↥W) (hz : z ∈ Z.support), Option ((H z hz).subscheme.IdealSheafData))
      (hJnone : ∀ (z : ↥W) (hz : z ∈ Z.support), J z hz = none →
        IsOpen ((H z hz).subschemeι.base ⁻¹'
          (((Z.comap (U z hz).ι).support : Set ↥(U z hz).toScheme))))
      (hJcomp : ∀ (z : ↥W) (hz : z ∈ Z.support) (Jz : (H z hz).subscheme.IdealSheafData),
        J z hz = some Jz → NonzeroOnComponents Jz)
      (hJloc : ∀ (z : ↥W) (hz : z ∈ Z.support) (Jz : (H z hz).subscheme.IdealSheafData),
        J z hz = some Jz →
        ∀ x : ↥(H z hz).subscheme,
          ((H z hz).subschemeι ≫ (U z hz).ι).base x ∉ Mem →
          ∃ V : (H z hz).subscheme.Opens, x ∈ V ∧
            Jz.comap V.ι =
              (((N.comap (U z hz).ι).comap (H z hz).subschemeι)).comap V.ι)
      (hJcert : ∀ (z : ↥W) (hz : z ∈ Z.support) (Jz : (H z hz).subscheme.IdealSheafData),
        J z hz = some Jz →
        PrincipalizationCertificate (H z hz).subscheme
          ((H z hz).subschemeι ≫ (U z hz).ι ≫ p) Jz μ
          (((H z hz).subschemeι ≫ (U z hz).ι).base ⁻¹' Mem)
          ((Z.comap (U z hz).ι).comap (H z hz).subschemeι)),
      (∀ (z : ↥W) (hz : z ∈ Z.support) (Jz : (H z hz).subscheme.IdealSheafData)
          (a : J z hz = some Jz),
        motive_1 (H z hz).subscheme ((H z hz).subschemeι ≫ (U z hz).ι ≫ p) Jz μ
          (((H z hz).subschemeι ≫ (U z hz).ι).base ⁻¹' Mem)
          ((Z.comap (U z hz).ι).comap (H z hz).subschemeι) (hJcert z hz Jz a)) →
        motive_2 W p N μ Mem Z
          (OrderCertificate.descend U hU H hH hNsubH hZH J hJnone hJcomp hJloc hJcert))
    {W : Scheme.{u}} {a : W ⟶ Spec (CommRingCat.of k)} {a_1 : W.IdealSheafData} {a_2 : ℕ}
    {a_3 : Set ↥W} {a_4 : W.IdealSheafData}
    (t : PrincipalizationCertificate W a a_1 a_2 a_3 a_4) :
    motive_1 W a a_1 a_2 a_3 a_4 t := by
  suffices h : ∀ (c : CertificateKind) (W : Scheme.{u}) (a : W ⟶ Spec (CommRingCat.of k))
      (a_1 : W.IdealSheafData) (a_2 : ℕ) (a_3 : Set ↥W) (a_4 : W.IdealSheafData)
      (t : Certificate c W a a_1 a_2 a_3 a_4),
      CertificateKind.rec
        (motive := fun c => ∀ (W : Scheme.{u}) (a : W ⟶ Spec (CommRingCat.of k))
          (a_1 : W.IdealSheafData) (a_2 : ℕ) (a_3 : Set ↥W) (a_4 : W.IdealSheafData),
          Certificate c W a a_1 a_2 a_3 a_4 → Prop)
        motive_1 motive_2 c W a a_1 a_2 a_3 a_4 t from
    h .principalization W a a_1 a_2 a_3 a_4 t
  intro c W a a_1 a_2 a_3 a_4 t
  induction t with
  | principalizationMemory h => exact memory h
  | principalizationLarge hm => exact large hm
  | principalizationToOrder M N μ hI hM hmu hZ hcert ih =>
    exact toOrder M N μ hI hM hmu hZ hcert ih
  | principalizationLocalize U hU hcert ih => exact localize U hU hcert ih
  | orderMemory h => exact orderMemory h
  | orderLarge hmu => exact orderLarge hmu
  | orderLocalize U hU hcert ih => exact orderLocalize U hU hcert ih
  | orderDescend U hU H hH hNsubH hZH J hJnone hJcomp hJloc hJcert ih =>
    exact descend U hU H hH hNsubH hZH J hJnone hJcomp hJloc hJcert ih

theorem OrderCertificate.rec {k : Type u} [Field k]
    {motive_1 : ∀ (W : Scheme.{u}) (a : W ⟶ Spec (CommRingCat.of k)) (a_1 : W.IdealSheafData)
      (a_2 : ℕ) (a_3 : Set ↥W) (a_4 : W.IdealSheafData),
      PrincipalizationCertificate W a a_1 a_2 a_3 a_4 → Prop}
    {motive_2 : ∀ (W : Scheme.{u}) (a : W ⟶ Spec (CommRingCat.of k)) (a_1 : W.IdealSheafData)
      (a_2 : ℕ) (a_3 : Set ↥W) (a_4 : W.IdealSheafData),
      OrderCertificate W a a_1 a_2 a_3 a_4 → Prop}
    (memory : ∀ {W : Scheme.{u}} {p : W ⟶ Spec (CommRingCat.of k)} {I : W.IdealSheafData}
      {m : ℕ} {Mem : Set ↥W} {Z : W.IdealSheafData} (h : (Z.support : Set ↥W) ⊆ Mem),
      motive_1 W p I m Mem Z (PrincipalizationCertificate.memory h))
    (large : ∀ {W : Scheme.{u}} {p : W ⟶ Spec (CommRingCat.of k)} {I : W.IdealSheafData}
      {m : ℕ} {Mem : Set ↥W} {Z : W.IdealSheafData} (hm : 2 ≤ m),
      motive_1 W p I m Mem Z (PrincipalizationCertificate.large hm))
    (toOrder : ∀ {W : Scheme.{u}} {p : W ⟶ Spec (CommRingCat.of k)} {I : W.IdealSheafData}
      {m : ℕ} {Mem : Set ↥W} {Z : W.IdealSheafData} (M N : W.IdealSheafData) (μ : ℕ)
      (hI : I = M * N) (hM : (M.support : Set ↥W) ⊆ Mem) (hmu : m ≤ μ)
      (hZ : (Z.support : Set ↥W) ⊆ orderAtLeastLocus N μ)
      (hcert : OrderCertificate W p N μ Mem Z),
      motive_2 W p N μ Mem Z hcert →
        motive_1 W p I m Mem Z (PrincipalizationCertificate.toOrder M N μ hI hM hmu hZ hcert))
    (localize : ∀ {W : Scheme.{u}} {p : W ⟶ Spec (CommRingCat.of k)} {I : W.IdealSheafData}
      {m : ℕ} {Mem : Set ↥W} {Z : W.IdealSheafData}
      (U : ∀ z : ↥W, z ∈ Z.support → W.Opens)
      (hU : ∀ (z : ↥W) (hz : z ∈ Z.support), z ∈ U z hz)
      (hcert : ∀ (z : ↥W) (hz : z ∈ Z.support),
        PrincipalizationCertificate (U z hz).toScheme ((U z hz).ι ≫ p) (I.comap (U z hz).ι) m
          ((U z hz).ι.base ⁻¹' Mem) (Z.comap (U z hz).ι)),
      (∀ (z : ↥W) (hz : z ∈ Z.support),
        motive_1 (U z hz).toScheme ((U z hz).ι ≫ p) (I.comap (U z hz).ι) m
          ((U z hz).ι.base ⁻¹' Mem) (Z.comap (U z hz).ι) (hcert z hz)) →
        motive_1 W p I m Mem Z (PrincipalizationCertificate.localize U hU hcert))
    (orderMemory : ∀ {W : Scheme.{u}} {p : W ⟶ Spec (CommRingCat.of k)} {N : W.IdealSheafData}
      {μ : ℕ} {Mem : Set ↥W} {Z : W.IdealSheafData} (h : (Z.support : Set ↥W) ⊆ Mem),
      motive_2 W p N μ Mem Z (OrderCertificate.memory h))
    (orderLarge : ∀ {W : Scheme.{u}} {p : W ⟶ Spec (CommRingCat.of k)} {N : W.IdealSheafData}
      {μ : ℕ} {Mem : Set ↥W} {Z : W.IdealSheafData} (hmu : 2 ≤ μ),
      motive_2 W p N μ Mem Z (OrderCertificate.large hmu))
    (orderLocalize : ∀ {W : Scheme.{u}} {p : W ⟶ Spec (CommRingCat.of k)}
      {N : W.IdealSheafData} {μ : ℕ} {Mem : Set ↥W} {Z : W.IdealSheafData}
      (U : ∀ z : ↥W, z ∈ Z.support → W.Opens)
      (hU : ∀ (z : ↥W) (hz : z ∈ Z.support), z ∈ U z hz)
      (hcert : ∀ (z : ↥W) (hz : z ∈ Z.support),
        OrderCertificate (U z hz).toScheme ((U z hz).ι ≫ p) (N.comap (U z hz).ι) μ
          ((U z hz).ι.base ⁻¹' Mem) (Z.comap (U z hz).ι)),
      (∀ (z : ↥W) (hz : z ∈ Z.support),
        motive_2 (U z hz).toScheme ((U z hz).ι ≫ p) (N.comap (U z hz).ι) μ
          ((U z hz).ι.base ⁻¹' Mem) (Z.comap (U z hz).ι) (hcert z hz)) →
        motive_2 W p N μ Mem Z (OrderCertificate.localize U hU hcert))
    (descend : ∀ {W : Scheme.{u}} {p : W ⟶ Spec (CommRingCat.of k)} {N : W.IdealSheafData}
      {μ : ℕ} {Mem : Set ↥W} {Z : W.IdealSheafData}
      (U : ∀ z : ↥W, z ∈ Z.support → W.Opens)
      (hU : ∀ (z : ↥W) (hz : z ∈ Z.support), z ∈ U z hz)
      (H : ∀ (z : ↥W) (hz : z ∈ Z.support), (U z hz).toScheme.IdealSheafData)
      (hH : ∀ (z : ↥W) (hz : z ∈ Z.support),
        IsSmoothDivisor ((U z hz).ι ≫ p) (H z hz))
      (hNsubH : ∀ (z : ↥W) (hz : z ∈ Z.support),
        (((N.comap (U z hz).ι).support : Set ↥(U z hz).toScheme)) ⊆
          ((H z hz).support : Set ↥(U z hz).toScheme))
      (hZH : ∀ (z : ↥W) (hz : z ∈ Z.support),
        (((Z.comap (U z hz).ι).support : Set ↥(U z hz).toScheme)) ⊆
          ((H z hz).support : Set ↥(U z hz).toScheme))
      (J : ∀ (z : ↥W) (hz : z ∈ Z.support), Option ((H z hz).subscheme.IdealSheafData))
      (hJnone : ∀ (z : ↥W) (hz : z ∈ Z.support), J z hz = none →
        IsOpen ((H z hz).subschemeι.base ⁻¹'
          (((Z.comap (U z hz).ι).support : Set ↥(U z hz).toScheme))))
      (hJcomp : ∀ (z : ↥W) (hz : z ∈ Z.support) (Jz : (H z hz).subscheme.IdealSheafData),
        J z hz = some Jz → NonzeroOnComponents Jz)
      (hJloc : ∀ (z : ↥W) (hz : z ∈ Z.support) (Jz : (H z hz).subscheme.IdealSheafData),
        J z hz = some Jz →
        ∀ x : ↥(H z hz).subscheme,
          ((H z hz).subschemeι ≫ (U z hz).ι).base x ∉ Mem →
          ∃ V : (H z hz).subscheme.Opens, x ∈ V ∧
            Jz.comap V.ι =
              (((N.comap (U z hz).ι).comap (H z hz).subschemeι)).comap V.ι)
      (hJcert : ∀ (z : ↥W) (hz : z ∈ Z.support) (Jz : (H z hz).subscheme.IdealSheafData),
        J z hz = some Jz →
        PrincipalizationCertificate (H z hz).subscheme
          ((H z hz).subschemeι ≫ (U z hz).ι ≫ p) Jz μ
          (((H z hz).subschemeι ≫ (U z hz).ι).base ⁻¹' Mem)
          ((Z.comap (U z hz).ι).comap (H z hz).subschemeι)),
      (∀ (z : ↥W) (hz : z ∈ Z.support) (Jz : (H z hz).subscheme.IdealSheafData)
          (a : J z hz = some Jz),
        motive_1 (H z hz).subscheme ((H z hz).subschemeι ≫ (U z hz).ι ≫ p) Jz μ
          (((H z hz).subschemeι ≫ (U z hz).ι).base ⁻¹' Mem)
          ((Z.comap (U z hz).ι).comap (H z hz).subschemeι) (hJcert z hz Jz a)) →
        motive_2 W p N μ Mem Z
          (OrderCertificate.descend U hU H hH hNsubH hZH J hJnone hJcomp hJloc hJcert))
    {W : Scheme.{u}} {a : W ⟶ Spec (CommRingCat.of k)} {a_1 : W.IdealSheafData} {a_2 : ℕ}
    {a_3 : Set ↥W} {a_4 : W.IdealSheafData}
    (t : OrderCertificate W a a_1 a_2 a_3 a_4) :
    motive_2 W a a_1 a_2 a_3 a_4 t := by
  suffices h : ∀ (c : CertificateKind) (W : Scheme.{u}) (a : W ⟶ Spec (CommRingCat.of k))
      (a_1 : W.IdealSheafData) (a_2 : ℕ) (a_3 : Set ↥W) (a_4 : W.IdealSheafData)
      (t : Certificate c W a a_1 a_2 a_3 a_4),
      CertificateKind.rec
        (motive := fun c => ∀ (W : Scheme.{u}) (a : W ⟶ Spec (CommRingCat.of k))
          (a_1 : W.IdealSheafData) (a_2 : ℕ) (a_3 : Set ↥W) (a_4 : W.IdealSheafData),
          Certificate c W a a_1 a_2 a_3 a_4 → Prop)
        motive_1 motive_2 c W a a_1 a_2 a_3 a_4 t from
    h .order W a a_1 a_2 a_3 a_4 t
  intro c W a a_1 a_2 a_3 a_4 t
  induction t with
  | principalizationMemory h => exact memory h
  | principalizationLarge hm => exact large hm
  | principalizationToOrder M N μ hI hM hmu hZ hcert ih =>
    exact toOrder M N μ hI hM hmu hZ hcert ih
  | principalizationLocalize U hU hcert ih => exact localize U hU hcert ih
  | orderMemory h => exact orderMemory h
  | orderLarge hmu => exact orderLarge hmu
  | orderLocalize U hU hcert ih => exact orderLocalize U hU hcert ih
  | orderDescend U hU H hH hNsubH hZH J hJnone hJcomp hJloc hJcert ih =>
    exact descend U hU H hH hNsubH hZH J hJnone hJcomp hJloc hJcert ih

theorem PrincipalizationCertificate.of_two_le {k : Type u} [Field k] (W : Scheme.{u})
    (p : W ⟶ Spec (CommRingCat.of k)) (I : W.IdealSheafData) (m : ℕ) (Mem : Set ↥W)
    (Z : W.IdealSheafData) (hm : 2 ≤ m) :
    PrincipalizationCertificate W p I m Mem Z :=
  PrincipalizationCertificate.large hm

theorem OrderCertificate.of_two_le {k : Type u} [Field k] (W : Scheme.{u})
    (p : W ⟶ Spec (CommRingCat.of k)) (N : W.IdealSheafData) (μ : ℕ) (Mem : Set ↥W)
    (Z : W.IdealSheafData) (hmu : 2 ≤ μ) :
    OrderCertificate W p N μ Mem Z :=
  OrderCertificate.large hmu

end FunctorialResolution.EmbeddedResolution
