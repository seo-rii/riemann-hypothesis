module

public import Mathlib
public import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.EtaleCoordinateCodimensionCriterion
public import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.AffineResolutionRule
public import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.AffineSpaceOrigin
public import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.IndependenceOfEmbedding
public import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.ClosedEmbeddingIntoAffineSpace
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.FunctorialPrincipalization
public import Development.ResolutionOfSingularities.EmbeddedResolution.StrongResolution.EmbeddedBlowupSequence

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

private theorem locallyConstCodimImpliesConstantCodim : LocallyConstCodimImpliesConstantCodim.{u} := by
  intro k _ X X' q _ τ _ c h
  exact hasEtaleCoordCodim_of_locally_smooth_over_affineSpace q τ c h

private theorem linearEmbeddingsHaveLocallyConstCodim_of_affineSpaceIsSmooth (hsm : AffineSpaceIsSmooth.{u}) :
    LinearEmbeddingsHaveLocallyConstCodim.{u} := by
  intro k _ n m
  exact ⟨hasSmoothCoordCodim_affineSpaceInl hsm k n m, hasSmoothCoordCodim_affineSpaceInrEmbedding hsm k n m⟩

theorem isIndependentOfPresentedEmbedding_embeddedResolutionRule (Alg : PrincipalizationAlgorithm.{u})
    (hAlg : IsFunctorialPrincipalization Alg) (hw : TransitionsAreBlowupsForEmbeddings Alg) (hsm : AffineSpaceIsSmooth.{u})
    (hcmp : ClosedEmbeddingsRelatedByAutomorphism.{u}) :
    (embeddedResolutionRuleOfPrincipalization Alg hw).IsIndependentOfPresentedEmbedding :=
  isIndependentOfPresentedEmbedding_of_locallyConstCodim Alg hAlg hw hsm hcmp
    locallyConstCodimImpliesConstantCodim (linearEmbeddingsHaveLocallyConstCodim_of_affineSpaceIsSmooth hsm)

end FunctorialResolution.EmbeddedResolution

end
