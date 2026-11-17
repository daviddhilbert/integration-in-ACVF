module

public import Integration7.UniformCellHeadFibres
public import Integration7.TranslatedRVHeadSaturation
public import Integration7.GammaRelativeTranslations
public import Integration7.NativeRelativeTranslationVolumes

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! Actual uniform vertical translations of the whole cell refinement.
They have original-Gamma graphs, are bijections onto head-saturated
images, and have VF Jacobian one almost everywhere. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section5 SpecialTransformations.Section9
open IntegrationInACVF.Section4

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {G : Base (M := M)} {S : Set M} {m : ℕ}
variable {A : DefSet (M := M) S 2 m}

namespace UniformMixedCellPresentation

def verticalTranslationImage (F : UniformMixedCellPresentation G (carrier A))
    (hNames : commonRealNames G ⊆ S) : DefSet (M := M) S 2 (m+F.arity) :=
  relativeTranslationImage (gammaRVGraphRefinement A F.parameters hNames) 0 (F.refinementCentreMap hNames)

def verticalTranslation (F : UniformMixedCellPresentation G (carrier A))
    (hNames : commonRealNames G ⊆ S) :
    Map (gammaRVGraphRefinement A F.parameters hNames) (F.verticalTranslationImage hNames) :=
  relativeTranslationToImage _ 0 (F.refinementCentreMap hNames)

theorem vertical_translation_bijective (F : UniformMixedCellPresentation G (carrier A))
    (hNames : commonRealNames G ⊆ S) : Function.Bijective (F.verticalTranslation hNames) :=
  relative_translation_to_image_bijective _ 0 (F.refinementCentreMap hNames) (F.refinement_centre_constant hNames)

theorem vertical_translation_graph_gamma (F : UniformMixedCellPresentation G (carrier A))
    (hNames : commonRealNames G ⊆ S) : GammaGraphDefinable G (pointMapGraph (F.verticalTranslation hNames)) :=
  gamma_relative_translation_to_image_graph _ 0 (F.refinementCentreMap hNames) (F.refinement_centre_gamma hNames)

theorem vertical_translation_image_gamma (F : UniformMixedCellPresentation G (carrier A))
    (hNames : commonRealNames G ⊆ S) : GammaSetDefinable G (carrier (F.verticalTranslationImage hNames)) :=
  gamma_relative_translation_image _ 0 (F.refinementCentreMap hNames) (F.refinement_centre_gamma hNames)

theorem vertical_translation_head_saturated (F : UniformMixedCellPresentation G (carrier A))
    (hNames : commonRealNames G ⊆ S) : HeadSaturated (carrier (F.verticalTranslationImage hNames)) :=
  translated_rv_head_saturated _ (F.refinementCentreMap hNames) (F.refinement_centre_constant hNames)
    (F.refinementParadigm hNames) (F.source_head_fibre hNames)

theorem vertical_translation_jacobian_one
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    {A₀ : DefSet (M := M) (C.base : Set M) 2 m} (F : UniformMixedCellPresentation G (carrier A₀))
    (hNames : commonRealNames G ⊆ (C.base : Set M)) :
    VFAlmostEverywhere (rawSpecialSet hc (gammaRVGraphRefinement A₀ F.parameters hNames))
      (fun p => HasMixedVFJacobianAt (rawSpecialMap hc (F.verticalTranslation hNames)) p 1) :=
  native_relative_translation_jacobian_one hc C (by decide) _ 0 (F.refinementCentreMap hNames)
    (F.refinement_centre_constant hNames)

end UniformMixedCellPresentation
end IntegrationInACVF.Section7
