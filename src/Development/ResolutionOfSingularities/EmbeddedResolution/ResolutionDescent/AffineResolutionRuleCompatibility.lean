module

public import Mathlib
public import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.AffineResolutionRule
public import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.SmoothPullbackLocalAmbientEmbedding
public import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.IndependenceOfEmbeddingHypotheses
public import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.EmbeddedResolutionRuleLocality
public import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.EmbeddedResolutionRule
public import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.EmbeddedResolutionRuleOfPrincipalization
public import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.GraphChartLocalAmbientEmbedding
public import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.SmoothPullbackGraphChart
public import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.PresentedSelection
public import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.PresentedSelectionCompatibility
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.FunctorialPrincipalization
public import Development.ResolutionOfSingularities.EmbeddedResolution.StrongResolution.EmbeddedBlowupSequence
public import Development.ResolutionOfSingularities.EmbeddedResolution.StrongResolution.EmbeddedStrictTransform
public import Development.ResolutionOfSingularities.Foundations.BlowupUniversalProperty
public import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionOfSingularities

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry

namespace FunctorialResolution.EmbeddedResolution

private theorem smoothPullbackHasLocalAmbientEmbedding_of_affineSpaceIsSmooth (hsm : AffineSpaceIsSmooth.{u}) :
    SmoothPullbackHasLocalAmbientEmbedding.{u} :=
  smoothPullbackHasLocalAmbientEmbedding_of_hasGraphChart hsm smoothPullbackHasGraphChart

private theorem isCompatibleWithOpenImmersions_affineResolutionRuleOfPrincipalization_of_smoothPullbackHasLocalAmbientEmbedding
    (A : PrincipalizationAlgorithm.{u})
    (hAlg : IsFunctorialPrincipalization A) (hw : TransitionsAreBlowupsForEmbeddings A)
    (hemb : AffineEmbedsIntoAffineSpace.{u}) (hsncE : NilIsStrictNormalCrossingsOnAffineSpace.{u})
    (hsm : AffineSpaceIsSmooth.{u}) (hex : EmbeddedPrincipalizationYieldsBlowups A hemb hsncE hsm)
    (hcmp : ClosedEmbeddingsRelatedByAutomorphism.{u}) (hS : SmoothPullbackHasLocalAmbientEmbedding.{u}) :
    IsCompatibleWithOpenImmersions (affineResolutionRuleOfPrincipalization A hemb hsncE hsm hex) := by
  have key := isCompatibleWithOpenImmersions_toAffineResolutionRule (embeddedResolutionRuleOfPrincipalization A hw)
    ({ sel := affineSpaceEmbeddingChoice hemb hsncE hsm
       pres := fun k _ _ Y p _ _ _ _ => affineSpaceChartPresentation hemb hsncE hsm k Y p
       basePres := fun k _ _ Y p _ _ _ _ K _ _ _ hker hsncK =>
         by
           let n := ULift.{u, 0} (Fin (hemb k Y p).choose)
           have hA : IsPullback (baseChangeProjection (affineSpaceIndexedByToSpec k n) K)
               (baseChangeToSpec (affineSpaceIndexedByToSpec k n) K) (affineSpaceIndexedByToSpec k n)
               (specMapAlgebraMap k K) := IsPullback.of_hasPullback _ _
           have hB : IsPullback (AlgebraicGeometry.AffineSpace.map n (specMapAlgebraMap k K))
               (affineSpaceIndexedByToSpec K n) (affineSpaceIndexedByToSpec k n) (specMapAlgebraMap k K) :=
             AlgebraicGeometry.AffineSpace.isPullback_map (n := n) _
           exact presentationOfAmbientIso hsm _ (hemb k Y p).choose
             (hA.isoIsPullback _ _ hB) (hA.isoIsPullback_hom_snd _ _ hB) } : PresentedSelection)
    (isIndependentOfPresentedEmbedding_embeddedResolutionRule A hAlg hw hsm hcmp)
    (embeddedResolutionRule_isCompatibleWithSmoothAmbientMaps A hAlg hw)
    (hasProperCenters_embeddedResolutionRuleOfPrincipalization A hw) hS hsm nilIsStrictNormalCrossingsOfSmooth
  change IsCompatibleWithOpenImmersions ((embeddedResolutionRuleOfPrincipalization A hw).toAffineResolutionRule
    (affineSpaceEmbeddingChoice hemb hsncE hsm)) at key
  rw [toAffineResolutionRule_embeddedResolutionRuleOfPrincipalization A hw hemb hsncE hsm hex] at key
  exact key

private theorem isCompatibleWithEtaleCovers_affineResolutionRuleOfPrincipalization_of_smoothPullbackHasLocalAmbientEmbedding
    (A : PrincipalizationAlgorithm.{u})
    (hAlg : IsFunctorialPrincipalization A) (hw : TransitionsAreBlowupsForEmbeddings A)
    (hemb : AffineEmbedsIntoAffineSpace.{u}) (hsncE : NilIsStrictNormalCrossingsOnAffineSpace.{u})
    (hsm : AffineSpaceIsSmooth.{u}) (hex : EmbeddedPrincipalizationYieldsBlowups A hemb hsncE hsm)
    (hcmp : ClosedEmbeddingsRelatedByAutomorphism.{u}) (hS : SmoothPullbackHasLocalAmbientEmbedding.{u}) :
    IsCompatibleWithEtaleCovers (affineResolutionRuleOfPrincipalization A hemb hsncE hsm hex) := by
  have key := isCompatibleWithEtaleCovers_toAffineResolutionRule (embeddedResolutionRuleOfPrincipalization A hw)
    ({ sel := affineSpaceEmbeddingChoice hemb hsncE hsm
       pres := fun k _ _ Y p _ _ _ _ => affineSpaceChartPresentation hemb hsncE hsm k Y p
       basePres := fun k _ _ Y p _ _ _ _ K _ _ _ hker hsncK =>
         by
           let n := ULift.{u, 0} (Fin (hemb k Y p).choose)
           have hA : IsPullback (baseChangeProjection (affineSpaceIndexedByToSpec k n) K)
               (baseChangeToSpec (affineSpaceIndexedByToSpec k n) K) (affineSpaceIndexedByToSpec k n)
               (specMapAlgebraMap k K) := IsPullback.of_hasPullback _ _
           have hB : IsPullback (AlgebraicGeometry.AffineSpace.map n (specMapAlgebraMap k K))
               (affineSpaceIndexedByToSpec K n) (affineSpaceIndexedByToSpec k n) (specMapAlgebraMap k K) :=
             AlgebraicGeometry.AffineSpace.isPullback_map (n := n) _
           exact presentationOfAmbientIso hsm _ (hemb k Y p).choose
             (hA.isoIsPullback _ _ hB) (hA.isoIsPullback_hom_snd _ _ hB) } : PresentedSelection)
    (isIndependentOfPresentedEmbedding_embeddedResolutionRule A hAlg hw hsm hcmp)
    (embeddedResolutionRule_isCompatibleWithSmoothAmbientMaps A hAlg hw)
    (hasProperCenters_embeddedResolutionRuleOfPrincipalization A hw) hS hsm nilIsStrictNormalCrossingsOfSmooth
  change IsCompatibleWithEtaleCovers ((embeddedResolutionRuleOfPrincipalization A hw).toAffineResolutionRule
    (affineSpaceEmbeddingChoice hemb hsncE hsm)) at key
  rw [toAffineResolutionRule_embeddedResolutionRuleOfPrincipalization A hw hemb hsncE hsm hex] at key
  exact key

theorem isCompatibleWithOpenImmersions_affineResolutionRuleOfPrincipalization (A : PrincipalizationAlgorithm.{u})
    (hAlg : IsFunctorialPrincipalization A) (hw : TransitionsAreBlowupsForEmbeddings A)
    (hemb : AffineEmbedsIntoAffineSpace.{u}) (hsncE : NilIsStrictNormalCrossingsOnAffineSpace.{u})
    (hsm : AffineSpaceIsSmooth.{u}) (hex : EmbeddedPrincipalizationYieldsBlowups A hemb hsncE hsm)
    (hcmp : ClosedEmbeddingsRelatedByAutomorphism.{u}) :
    IsCompatibleWithOpenImmersions (affineResolutionRuleOfPrincipalization A hemb hsncE hsm hex) :=
  isCompatibleWithOpenImmersions_affineResolutionRuleOfPrincipalization_of_smoothPullbackHasLocalAmbientEmbedding A hAlg hw hemb hsncE
    hsm hex hcmp (smoothPullbackHasLocalAmbientEmbedding_of_affineSpaceIsSmooth hsm)

theorem isCompatibleWithEtaleCovers_affineResolutionRuleOfPrincipalization (A : PrincipalizationAlgorithm.{u})
    (hAlg : IsFunctorialPrincipalization A) (hw : TransitionsAreBlowupsForEmbeddings A)
    (hemb : AffineEmbedsIntoAffineSpace.{u}) (hsncE : NilIsStrictNormalCrossingsOnAffineSpace.{u})
    (hsm : AffineSpaceIsSmooth.{u}) (hex : EmbeddedPrincipalizationYieldsBlowups A hemb hsncE hsm)
    (hcmp : ClosedEmbeddingsRelatedByAutomorphism.{u}) :
    IsCompatibleWithEtaleCovers (affineResolutionRuleOfPrincipalization A hemb hsncE hsm hex) :=
  isCompatibleWithEtaleCovers_affineResolutionRuleOfPrincipalization_of_smoothPullbackHasLocalAmbientEmbedding A hAlg hw hemb hsncE
    hsm hex hcmp (smoothPullbackHasLocalAmbientEmbedding_of_affineSpaceIsSmooth hsm)

theorem isCompatibleWithFieldBaseChange_affineResolutionRuleOfPrincipalization (A : PrincipalizationAlgorithm.{u})
    (hAlg : IsFunctorialPrincipalization A) (hw : TransitionsAreBlowupsForEmbeddings A)
    (hemb : AffineEmbedsIntoAffineSpace.{u}) (hsncE : NilIsStrictNormalCrossingsOnAffineSpace.{u})
    (hsm : AffineSpaceIsSmooth.{u}) (hex : EmbeddedPrincipalizationYieldsBlowups A hemb hsncE hsm)
    (hcmp : ClosedEmbeddingsRelatedByAutomorphism.{u}) :
    IsCompatibleWithFieldBaseChange (affineResolutionRuleOfPrincipalization A hemb hsncE hsm hex) := by
  have key := isCompatibleWithFieldBaseChange_toAffineResolutionRule (embeddedResolutionRuleOfPrincipalization A hw)
    ({ sel := affineSpaceEmbeddingChoice hemb hsncE hsm
       pres := fun k _ _ Y p _ _ _ _ => affineSpaceChartPresentation hemb hsncE hsm k Y p
       basePres := fun k _ _ Y p _ _ _ _ K _ _ _ hker hsncK =>
         by
           let n := ULift.{u, 0} (Fin (hemb k Y p).choose)
           have hA : IsPullback (baseChangeProjection (affineSpaceIndexedByToSpec k n) K)
               (baseChangeToSpec (affineSpaceIndexedByToSpec k n) K) (affineSpaceIndexedByToSpec k n)
               (specMapAlgebraMap k K) := IsPullback.of_hasPullback _ _
           have hB : IsPullback (AlgebraicGeometry.AffineSpace.map n (specMapAlgebraMap k K))
               (affineSpaceIndexedByToSpec K n) (affineSpaceIndexedByToSpec k n) (specMapAlgebraMap k K) :=
             AlgebraicGeometry.AffineSpace.isPullback_map (n := n) _
           exact presentationOfAmbientIso hsm _ (hemb k Y p).choose
             (hA.isoIsPullback _ _ hB) (hA.isoIsPullback_hom_snd _ _ hB) } : PresentedSelection)
    (isIndependentOfPresentedEmbedding_embeddedResolutionRule A hAlg hw hsm hcmp)
    (embeddedResolutionRule_isCompatibleWithFieldBaseChange A hAlg hw) nilIsStrictNormalCrossingsOfSmooth
  change IsCompatibleWithFieldBaseChange ((embeddedResolutionRuleOfPrincipalization A hw).toAffineResolutionRule
    (affineSpaceEmbeddingChoice hemb hsncE hsm)) at key
  rw [toAffineResolutionRule_embeddedResolutionRuleOfPrincipalization A hw hemb hsncE hsm hex] at key
  exact key

theorem isPullbackBlowupSequence_affineResolutionRuleOfPrincipalization_of_smooth (A : PrincipalizationAlgorithm.{u})
    (hAlg : IsFunctorialPrincipalization A) (hw : TransitionsAreBlowupsForEmbeddings A)
    (hemb : AffineEmbedsIntoAffineSpace.{u}) (hsncE : NilIsStrictNormalCrossingsOnAffineSpace.{u})
    (hsm : AffineSpaceIsSmooth.{u}) (hex : EmbeddedPrincipalizationYieldsBlowups A hemb hsncE hsm)
    (hcmp : ClosedEmbeddingsRelatedByAutomorphism.{u})
    (k : Type u) [Field k] [CharZero k] (Y V : Scheme.{u})
    (pY : Y ⟶ Spec (CommRingCat.of k)) (pV : V ⟶ Spec (CommRingCat.of k))
    [AlgebraicGeometry.IsAffine Y] [AlgebraicGeometry.IsAffine V]
    [AlgebraicGeometry.IsReduced Y] [AlgebraicGeometry.IsReduced V]
    [AlgebraicGeometry.LocallyOfFiniteType pY] [AlgebraicGeometry.QuasiCompact pY]
    [AlgebraicGeometry.LocallyOfFiniteType pV] [AlgebraicGeometry.QuasiCompact pV]
    (u : V ⟶ Y) (r : ℕ) [AlgebraicGeometry.SmoothOfRelativeDimension r u]
    (hu : u ≫ pY = pV) :
    IsPullbackBlowupSequence u (affineResolutionRuleOfPrincipalization A hemb hsncE hsm hex k V pV)
      (affineResolutionRuleOfPrincipalization A hemb hsncE hsm hex k Y pY) := by
  have key := isPullbackBlowupSequence_presentedSelection_of_smooth (embeddedResolutionRuleOfPrincipalization A hw)
    ({ sel := affineSpaceEmbeddingChoice hemb hsncE hsm
       pres := fun k _ _ Y p _ _ _ _ => affineSpaceChartPresentation hemb hsncE hsm k Y p
       basePres := fun k _ _ Y p _ _ _ _ K _ _ _ hker hsncK =>
         by
           let n := ULift.{u, 0} (Fin (hemb k Y p).choose)
           have hA : IsPullback (baseChangeProjection (affineSpaceIndexedByToSpec k n) K)
               (baseChangeToSpec (affineSpaceIndexedByToSpec k n) K) (affineSpaceIndexedByToSpec k n)
               (specMapAlgebraMap k K) := IsPullback.of_hasPullback _ _
           have hB : IsPullback (AlgebraicGeometry.AffineSpace.map n (specMapAlgebraMap k K))
               (affineSpaceIndexedByToSpec K n) (affineSpaceIndexedByToSpec k n) (specMapAlgebraMap k K) :=
             AlgebraicGeometry.AffineSpace.isPullback_map (n := n) _
           exact presentationOfAmbientIso hsm _ (hemb k Y p).choose
             (hA.isoIsPullback _ _ hB) (hA.isoIsPullback_hom_snd _ _ hB) } : PresentedSelection)
    (isIndependentOfPresentedEmbedding_embeddedResolutionRule A hAlg hw hsm hcmp)
    (embeddedResolutionRule_isCompatibleWithSmoothAmbientMaps A hAlg hw)
    (hasProperCenters_embeddedResolutionRuleOfPrincipalization A hw)
    (smoothPullbackHasLocalAmbientEmbedding_of_affineSpaceIsSmooth hsm) hsm nilIsStrictNormalCrossingsOfSmooth
    k Y V pY pV u r hu
  rw [← toAffineResolutionRule_embeddedResolutionRuleOfPrincipalization A hw hemb hsncE hsm hex,
    EmbeddedResolutionRule.toAffineResolutionRule_apply, EmbeddedResolutionRule.toAffineResolutionRule_apply]
  exact key

end FunctorialResolution.EmbeddedResolution
