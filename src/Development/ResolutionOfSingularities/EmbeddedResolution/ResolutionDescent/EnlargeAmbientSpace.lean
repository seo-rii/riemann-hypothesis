module

public import Mathlib
public import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupExistence
public import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.BlowupSequenceRelations
public import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.ConstantCodimension
public import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.StrictNormalCrossings
public import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.ChartPushforward
public import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.InactiveTotalSpacePushforward
public import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.EmbeddedResolutionRule
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.FunctorialPrincipalization
public import Development.ResolutionOfSingularities.EmbeddedResolution.StrongResolution.EmbeddedBlowupSequence
public import Development.ResolutionOfSingularities.EmbeddedResolution.StrongResolution.EmbeddedStrictTransform
public import Development.ResolutionOfSingularities.EmbeddedResolution.StrongResolution.SequenceIsomorphism
public import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.BlowupSequenceBasic
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.IdealBlowupSequence
public import Development.ResolutionOfSingularities.EmbeddedResolution.StrongResolution.StrongResolution
public import Development.ResolutionOfSingularities.Foundations.BlowupUniversalProperty
public import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionOfSingularities

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

namespace EmbeddingDatum

variable {k : Type u} [Field k] [CharZero k] {Y : Scheme.{u}}
  {p : Y ⟶ Spec (CommRingCat.of k)}

theorem emb_comp_comp_eq_of_comp_eq (G : EmbeddingDatum k Y p) {A' : Scheme.{u}}
    (q : A' ⟶ Spec (CommRingCat.of k)) (τ : G.ambient ⟶ A')
    (hτ : τ ≫ q = G.ambientStruct) :
    (G.emb ≫ τ) ≫ q = p := by
  rw [Category.assoc, hτ, G.comp_eq]

def enlargeAmbient (G : EmbeddingDatum k Y p) (A' : Scheme.{u}) [AlgebraicGeometry.IsAffine A']
    (q : A' ⟶ Spec (CommRingCat.of k)) [AlgebraicGeometry.Smooth q]
    [AlgebraicGeometry.LocallyOfFiniteType q] [AlgebraicGeometry.QuasiCompact q]
    (τ : G.ambient ⟶ A') [AlgebraicGeometry.IsClosedImmersion τ]
    (hτ : τ ≫ q = G.ambientStruct)
    (hker : NonzeroOnComponents (G.emb ≫ τ).ker)
    (hsnc : InStrictNormalCrossingPosition q ([] : List A'.IdealSheafData)) :
    EmbeddingDatum k Y p :=
  embeddingDatumOfClosedImmersion A' q (G.emb ≫ τ) hker (emb_comp_comp_eq_of_comp_eq G q τ hτ) hsnc

private theorem imageIdealSheaf_ker_eq_ker_comp {Yc A A' : Scheme.{u}} (e : Yc ⟶ A)
    [AlgebraicGeometry.IsClosedImmersion e] (σ : A ⟶ A') :
    imageIdealSheaf σ (Scheme.Hom.ker e) = Scheme.Hom.ker (e ≫ σ) :=
  (Scheme.Hom.ker_comp e σ).symm

private theorem isPushforwardBlowupSeq_ambientBlowups_enlargeAmbient [AlgebraicGeometry.IsAffine Y]
    [AlgebraicGeometry.LocallyOfFiniteType p]
    (G : EmbeddingDatum k Y p) (Alg : PrincipalizationAlgorithm.{u}) (hAlg : IsFunctorialPrincipalization Alg)
    (A' : Scheme.{u}) [AlgebraicGeometry.IsAffine A']
    (q : A' ⟶ Spec (CommRingCat.of k)) [AlgebraicGeometry.Smooth q]
    [AlgebraicGeometry.LocallyOfFiniteType q] [AlgebraicGeometry.QuasiCompact q]
    (τ : G.ambient ⟶ A') [AlgebraicGeometry.IsClosedImmersion τ]
    (hτ : τ ≫ q = G.ambientStruct)
    (hker : NonzeroOnComponents (G.emb ≫ τ).ker)
    (hsnc : InStrictNormalCrossingPosition q ([] : List A'.IdealSheafData))
    (c : ℕ) (hc : 1 ≤ c) (hcodim : HasEtaleCoordCodim q τ c) :
    IsPushforwardBlowupSeq τ (G.toEmbeddedBlowupSequence Alg).ambientSeq
      ((G.enlargeAmbient A' q τ hτ hker hsnc).toEmbeddedBlowupSequence Alg).ambientSeq := by
  have himg : imageIdealSheaf τ (Scheme.Hom.ker G.emb) = Scheme.Hom.ker (G.emb ≫ τ) :=
    imageIdealSheaf_ker_eq_ker_comp G.emb τ
  have hJ : NonzeroOnComponents (imageIdealSheaf τ (Scheme.Hom.ker G.emb)) := by
    rw [himg]; exact hker
  have key : ∀ (J : A'.IdealSheafData) (hJ' : NonzeroOnComponents J),
      J = Scheme.Hom.ker (G.emb ≫ τ) →
      IsPushforwardBlowupSeq τ (G.toEmbeddedBlowupSequence Alg).ambientSeq
        (Alg k A' q J hJ' ([] : List A'.IdealSheafData) hsnc).toSequenceOfBlowups →
      IsPushforwardBlowupSeq τ (G.toEmbeddedBlowupSequence Alg).ambientSeq
        ((G.enlargeAmbient A' q τ hτ hker hsnc).toEmbeddedBlowupSequence Alg).ambientSeq := by
    rintro J hJ' rfl h
    exact h
  exact key _ hJ himg
    (hAlg.pushforward k G.ambient A' G.ambientStruct q τ hτ c hc hcodim
      (Scheme.Hom.ker G.emb) G.nonzeroOnComponents_ker hJ G.sncEmpty hsnc)

theorem isomorphic_embeddedResolutionRule_enlargeAmbient [AlgebraicGeometry.IsAffine Y]
    [AlgebraicGeometry.IsReduced Y] [AlgebraicGeometry.LocallyOfFiniteType p]
    [AlgebraicGeometry.QuasiCompact p]
    (G : EmbeddingDatum k Y p) (Alg : PrincipalizationAlgorithm.{u}) (hAlg : IsFunctorialPrincipalization Alg)
    (hw : TransitionsAreBlowupsForEmbeddings Alg)
    (A' : Scheme.{u}) [AlgebraicGeometry.IsAffine A']
    (q : A' ⟶ Spec (CommRingCat.of k)) [AlgebraicGeometry.Smooth q]
    [AlgebraicGeometry.LocallyOfFiniteType q] [AlgebraicGeometry.QuasiCompact q]
    (τ : G.ambient ⟶ A') [AlgebraicGeometry.IsClosedImmersion τ]
    (hτ : τ ≫ q = G.ambientStruct)
    (hker : NonzeroOnComponents (G.emb ≫ τ).ker)
    (hsnc : InStrictNormalCrossingPosition q ([] : List A'.IdealSheafData))
    (c : ℕ) (hc : 1 ≤ c) (hcodim : HasEtaleCoordCodim q τ c) :
    (embeddedResolutionRuleOfPrincipalization Alg hw k Y p G).Isomorphic
      (embeddedResolutionRuleOfPrincipalization Alg hw k Y p (G.enlargeAmbient A' q τ hτ hker hsnc)) := by
  have P : ChartPushforward (G.toEmbeddedBlowupSequence Alg)
      ((G.enlargeAmbient A' q τ hτ hker hsnc).toEmbeddedBlowupSequence Alg) :=
    @ChartPushforward.ofIsPushforwardSeq k _ _ Y _ p _ (G.toEmbeddedBlowupSequence Alg)
      ((G.enlargeAmbient A' q τ hτ hker hsnc).toEmbeddedBlowupSequence Alg) τ
      (inferInstanceAs (AlgebraicGeometry.IsClosedImmersion τ)) rfl
      (isPushforwardBlowupSeq_ambientBlowups_enlargeAmbient G Alg hAlg A' q τ hτ hker hsnc c hc hcodim)
  exact P.inducedBlowupsWithoutIso_isomorphic (hw k Y p G) (hw k Y p (G.enlargeAmbient A' q τ hτ hker hsnc))

end EmbeddingDatum

end FunctorialResolution.EmbeddedResolution

end
