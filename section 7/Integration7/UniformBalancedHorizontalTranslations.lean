module

public import Integration7.UniformBalancedHorizontalCentres
public import Integration7.GammaRelativeTranslations
public import Integration7.NativeRelativeTranslationVolumes

@[expose] public section

/-! The horizontal translation of the entire balanced-row family is
an actual original-Gamma bijection with VF Jacobian one almost everywhere,
including arbitrary carried RV parameters. -/
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

def horizontalTranslationImage (F : UniformMixedCellPresentation G (carrier A)) (hBalanced : F.BalancedRows)
    (hNames : commonRealNames G ⊆ S) : DefSet (M := M) S 2 (m+F.arity) :=
  relativeTranslationImage (gammaRVGraphRefinement A F.parameters hNames) 1 (F.horizontalCentreMap hBalanced hNames)

def horizontalTranslation (F : UniformMixedCellPresentation G (carrier A)) (hBalanced : F.BalancedRows)
    (hNames : commonRealNames G ⊆ S) :
    Map (gammaRVGraphRefinement A F.parameters hNames) (F.horizontalTranslationImage hBalanced hNames) :=
  relativeTranslationToImage _ 1 (F.horizontalCentreMap hBalanced hNames)

theorem horizontal_translation_bijective (F : UniformMixedCellPresentation G (carrier A)) (hBalanced : F.BalancedRows)
    (hNames : commonRealNames G ⊆ S) : Function.Bijective (F.horizontalTranslation hBalanced hNames) :=
  relative_translation_to_image_bijective _ 1 (F.horizontalCentreMap hBalanced hNames)
    (F.horizontal_centre_constant hBalanced hNames)

theorem horizontal_translation_graph_gamma (F : UniformMixedCellPresentation G (carrier A)) (hBalanced : F.BalancedRows)
    (hNames : commonRealNames G ⊆ S) : GammaGraphDefinable G (pointMapGraph (F.horizontalTranslation hBalanced hNames)) :=
  gamma_relative_translation_to_image_graph _ 1 (F.horizontalCentreMap hBalanced hNames)
    (F.horizontal_centre_graph_gamma hBalanced hNames)

theorem horizontal_translation_image_gamma (F : UniformMixedCellPresentation G (carrier A)) (hBalanced : F.BalancedRows)
    (hNames : commonRealNames G ⊆ S) : GammaSetDefinable G (carrier (F.horizontalTranslationImage hBalanced hNames)) :=
  gamma_relative_translation_image _ 1 (F.horizontalCentreMap hBalanced hNames)
    (F.horizontal_centre_graph_gamma hBalanced hNames)

theorem horizontal_translation_jacobian_one
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    {A₀ : DefSet (M := M) (C.base : Set M) 2 m} (F : UniformMixedCellPresentation G (carrier A₀))
    (hBalanced : F.BalancedRows) (hNames : commonRealNames G ⊆ (C.base : Set M)) :
    VFAlmostEverywhere (rawSpecialSet hc (gammaRVGraphRefinement A₀ F.parameters hNames))
      (fun p => HasMixedVFJacobianAt (rawSpecialMap hc (F.horizontalTranslation hBalanced hNames)) p 1) :=
  native_relative_translation_jacobian_one hc C (by decide) _ 1 (F.horizontalCentreMap hBalanced hNames)
    (F.horizontal_centre_constant hBalanced hNames)

end UniformMixedCellPresentation
end IntegrationInACVF.Section7
