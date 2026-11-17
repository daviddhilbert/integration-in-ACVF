module

public import Integration7.MatchingPreparedFamilyDomains
public import Integration7.UniformTranslatedRectangleFamilies

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! The actual matching family carries the original vertical and
horizontal centres. Its two translations are Gamma bijections with
full VF Jacobian one and retain every recorded prepared key. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section5 SpecialTransformations.Section9
open IntegrationInACVF.Section4 IntegrationInACVF.Section5

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

theorem gamma_scalar_precomposition {G : Base (M := M)} {S : Set M} {n m u w : ℕ}
    {A : DefSet (M := M) S n m} {B : DefSet (M := M) S u w}
    (f : Map A B) (hf : GammaGraphDefinable G (pointMapGraph f))
    (c : Map B (PresentedSet.univ (SpecialTransformations.Section4.vfSpace 1) S))
    (hc : GammaScalarGraphDefinable G (fun p z => ∃ b : B, b.val = p ∧ (c b).val 0 = z)) :
    GammaScalarGraphDefinable G (fun p z => ∃ a : A, a.val = p ∧ (Map.comp c f a).val 0 = z) := by
  apply GammaGraphDefinable.congr ((gammaLogicInput G).comp_graph hf hc)
  intro p z
  constructor
  · rintro ⟨x,⟨a,ha,hax⟩,b,hb,hbz⟩
    have he : b = f a := Subtype.ext (hb.trans hax.symm)
    rw [he] at hbz
    exact ⟨a,ha,hbz⟩
  · rintro ⟨a,ha,haz⟩
    exact ⟨(f a).val,⟨a,ha,rfl⟩,f a,rfl,haz⟩

namespace UniformBalancedPositionPreparation
variable {G : Base (M := M)} {m : ℕ} {C : BaseContext M}
variable {A : DefSet (M := M) (C.base : Set M) 2 m}
variable {F : UniformMixedCellPresentation G (carrier A)} {hBalanced : F.BalancedRows}
variable {hNames : commonRealNames G ⊆ (C.base : Set M)}

def matchingSubsetMap (P : UniformBalancedPositionPreparation G C F hBalanced hNames) :
    Map P.matchingNative (gammaRVGraphRefinement A F.parameters hNames) :=
  Map.inclusion (by rintro p ⟨q,hq,_⟩; exact hq ▸ q.property)

def matchingForgetMap (P : UniformBalancedPositionPreparation G C F hBalanced hNames) :
    Map P.matchingPreparedFamily (gammaRVGraphRefinement A F.parameters hNames) :=
  Map.comp P.matchingSubsetMap (Map.inverse
    (Map.toImage (gammaRVGraphRefinementMap P.matchingNative P.matchingKeyLabels hNames))
    (gamma_rv_graph_refinement_bijective P.matchingNative P.matchingKeyLabels hNames))

theorem matching_forget_value (P : UniformBalancedPositionPreparation G C F hBalanced hNames)
    (q : P.matchingPreparedFamily) :
    (P.matchingForgetMap q).val = retainVFLabels
      (Fin.castAdd ((1+P.sourceArity)+(1+P.targetArity))) q.val :=
  native_rv_graph_refinement_inverse_value P.matchingNative P.matchingKeyLabels hNames q

theorem matching_forget_graph_gamma (P : UniformBalancedPositionPreparation G C F hBalanced hNames) :
    GammaGraphDefinable G (pointMapGraph P.matchingForgetMap) :=
  gamma_composition_graph _ _
    (gamma_inverse_map_graph _ (gamma_rv_graph_refinement_bijective P.matchingNative P.matchingKeyLabels hNames)
      (gamma_rv_graph_refinement_map_gamma P.matchingNative P.matchingKeyLabels hNames))
    (gamma_identity_graph P.matchingNative P.matching_part_gamma)

def matchingVerticalCentre (P : UniformBalancedPositionPreparation G C F hBalanced hNames) :
    Map P.matchingPreparedFamily (PresentedSet.univ (SpecialTransformations.Section4.vfSpace 1) (C.base : Set M)) :=
  Map.comp (F.refinementCentreMap hNames) P.matchingForgetMap

def matchingHorizontalCentre (P : UniformBalancedPositionPreparation G C F hBalanced hNames) :
    Map P.matchingPreparedFamily (PresentedSet.univ (SpecialTransformations.Section4.vfSpace 1) (C.base : Set M)) :=
  Map.comp (F.horizontalCentreMap hBalanced hNames) P.matchingForgetMap

theorem matching_vertical_centre_constant (P : UniformBalancedPositionPreparation G C F hBalanced hNames)
    (p q : P.matchingPreparedFamily) (he : erase 0 p.val = erase 0 q.val) :
    (P.matchingVerticalCentre p).val 0 = (P.matchingVerticalCentre q).val 0 := by
  apply F.refinement_centre_constant hNames
  rw [P.matching_forget_value p,P.matching_forget_value q]
  exact congrArg (retainVFLabels (Fin.castAdd ((1+P.sourceArity)+(1+P.targetArity)))) he

theorem matching_horizontal_centre_constant (P : UniformBalancedPositionPreparation G C F hBalanced hNames)
    (p q : P.matchingPreparedFamily) (he : erase 1 p.val = erase 1 q.val) :
    (P.matchingHorizontalCentre p).val 0 = (P.matchingHorizontalCentre q).val 0 := by
  apply F.horizontal_centre_constant hBalanced hNames
  rw [P.matching_forget_value p,P.matching_forget_value q]
  exact congrArg (retainVFLabels (Fin.castAdd ((1+P.sourceArity)+(1+P.targetArity)))) he

theorem matching_vertical_centre_gamma (P : UniformBalancedPositionPreparation G C F hBalanced hNames) :
    GammaScalarGraphDefinable G (fun p z => ∃ q : P.matchingPreparedFamily,
      q.val = p ∧ (P.matchingVerticalCentre q).val 0 = z) :=
  gamma_scalar_precomposition _ P.matching_forget_graph_gamma _ (F.refinement_centre_gamma hNames)

theorem matching_horizontal_centre_gamma (P : UniformBalancedPositionPreparation G C F hBalanced hNames) :
    GammaScalarGraphDefinable G (fun p z => ∃ q : P.matchingPreparedFamily,
      q.val = p ∧ (P.matchingHorizontalCentre q).val 0 = z) :=
  gamma_scalar_precomposition _ P.matching_forget_graph_gamma _ (F.horizontal_centre_graph_gamma hBalanced hNames)

def matchingVerticalImage (P : UniformBalancedPositionPreparation G C F hBalanced hNames) :=
  relativeTranslationImage P.matchingPreparedFamily 0 P.matchingVerticalCentre

def matchingHorizontalImage (P : UniformBalancedPositionPreparation G C F hBalanced hNames) :=
  relativeTranslationImage P.matchingPreparedFamily 1 P.matchingHorizontalCentre

def matchingVerticalMap (P : UniformBalancedPositionPreparation G C F hBalanced hNames) :=
  relativeTranslationToImage P.matchingPreparedFamily 0 P.matchingVerticalCentre

def matchingHorizontalMap (P : UniformBalancedPositionPreparation G C F hBalanced hNames) :=
  relativeTranslationToImage P.matchingPreparedFamily 1 P.matchingHorizontalCentre

theorem matching_vertical_map_bijective (P : UniformBalancedPositionPreparation G C F hBalanced hNames) :
    Function.Bijective P.matchingVerticalMap :=
  relative_translation_to_image_bijective _ 0 _ P.matching_vertical_centre_constant

theorem matching_horizontal_map_bijective (P : UniformBalancedPositionPreparation G C F hBalanced hNames) :
    Function.Bijective P.matchingHorizontalMap :=
  relative_translation_to_image_bijective _ 1 _ P.matching_horizontal_centre_constant

theorem matching_vertical_map_gamma (P : UniformBalancedPositionPreparation G C F hBalanced hNames) :
    GammaGraphDefinable G (pointMapGraph P.matchingVerticalMap) :=
  gamma_relative_translation_to_image_graph _ 0 _ P.matching_vertical_centre_gamma

theorem matching_horizontal_map_gamma (P : UniformBalancedPositionPreparation G C F hBalanced hNames) :
    GammaGraphDefinable G (pointMapGraph P.matchingHorizontalMap) :=
  gamma_relative_translation_to_image_graph _ 1 _ P.matching_horizontal_centre_gamma

theorem matching_vertical_image_gamma (P : UniformBalancedPositionPreparation G C F hBalanced hNames) :
    GammaSetDefinable G (carrier P.matchingVerticalImage) :=
  gamma_relative_translation_image _ 0 _ P.matching_vertical_centre_gamma

theorem matching_horizontal_image_gamma (P : UniformBalancedPositionPreparation G C F hBalanced hNames) :
    GammaSetDefinable G (carrier P.matchingHorizontalImage) :=
  gamma_relative_translation_image _ 1 _ P.matching_horizontal_centre_gamma

theorem matching_vertical_jacobian_one (hc : CanonicalStructure.IsCanonical (M := M))
    (P : UniformBalancedPositionPreparation G C F hBalanced hNames) :
    VFAlmostEverywhere (rawSpecialSet hc P.matchingPreparedFamily)
      (fun p => HasMixedVFJacobianAt (rawSpecialMap hc P.matchingVerticalMap) p 1) :=
  native_relative_translation_jacobian_one hc C (by decide) _ 0 _ P.matching_vertical_centre_constant

theorem matching_horizontal_jacobian_one (hc : CanonicalStructure.IsCanonical (M := M))
    (P : UniformBalancedPositionPreparation G C F hBalanced hNames) :
    VFAlmostEverywhere (rawSpecialSet hc P.matchingPreparedFamily)
      (fun p => HasMixedVFJacobianAt (rawSpecialMap hc P.matchingHorizontalMap) p 1) :=
  native_relative_translation_jacobian_one hc C (by decide) _ 1 _ P.matching_horizontal_centre_constant

end UniformBalancedPositionPreparation
end IntegrationInACVF.Section7
