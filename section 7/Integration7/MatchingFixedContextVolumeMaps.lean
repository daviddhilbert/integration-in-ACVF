module

public import Integration7.PreparedRectangleVolumeConjugates
public import Integration7.MatchingPreparedNonzeroFibres

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! The actual two matching translations, presented in the original
small context used by both full preparations. Re-presentation keeps
their functions, Gamma graphs, labels and Jacobian-one statements. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.Section5
open IntegrationInACVF.Section4 IntegrationInACVF.Section5 IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7.UniformBalancedPositionPreparation
variable {M : Type} [sM : LRV.Structure M] [M ⊨ Axioms.ACVF]
local notation "N" => (@CanonicalStructure.normalize M sM)
variable {G : Base (M := M)} {m : ℕ} {C : BaseContext M}
variable {A : DefSet (M := M) (C.base : Set M) 2 m}
variable {F : UniformMixedCellPresentation G (carrier A)} {hBalanced : F.BalancedRows}
variable {hNames : commonRealNames G ⊆ (C.base : Set M)}

def matchingFixedVerticalMap (P : UniformBalancedPositionPreparation G C F hBalanced hNames) :
    Map (extendBase P.inFixedContext.matchingPreparedFamily P.inFixedContext.baseInclusion)
      (extendBase P.inFixedContext.matchingVerticalImage P.inFixedContext.baseInclusion) :=
  @SpecialTransformations.DefinableGeometry.Map.extend LRV M N _ _ _ _
    P.inFixedContext.matchingPreparedFamily P.inFixedContext.matchingVerticalImage
    P.inFixedContext.matchingVerticalMap P.inFixedContext.baseInclusion

def matchingFixedHorizontalMap (P : UniformBalancedPositionPreparation G C F hBalanced hNames) :
    Map (extendBase P.inFixedContext.matchingPreparedFamily P.inFixedContext.baseInclusion)
      (extendBase P.inFixedContext.matchingHorizontalImage P.inFixedContext.baseInclusion) :=
  @SpecialTransformations.DefinableGeometry.Map.extend LRV M N _ _ _ _
    P.inFixedContext.matchingPreparedFamily P.inFixedContext.matchingHorizontalImage
    P.inFixedContext.matchingHorizontalMap P.inFixedContext.baseInclusion

theorem matching_fixed_vertical_bijective
    (P : UniformBalancedPositionPreparation G C F hBalanced hNames) :
    Function.Bijective P.matchingFixedVerticalMap := P.inFixedContext.matching_vertical_map_bijective

theorem matching_fixed_horizontal_bijective
    (P : UniformBalancedPositionPreparation G C F hBalanced hNames) :
    Function.Bijective P.matchingFixedHorizontalMap := P.inFixedContext.matching_horizontal_map_bijective

theorem matching_fixed_vertical_gamma
    (P : UniformBalancedPositionPreparation G C F hBalanced hNames) :
    GammaGraphDefinable G (pointMapGraph P.matchingFixedVerticalMap) := P.inFixedContext.matching_vertical_map_gamma

theorem matching_fixed_horizontal_gamma
    (P : UniformBalancedPositionPreparation G C F hBalanced hNames) :
    GammaGraphDefinable G (pointMapGraph P.matchingFixedHorizontalMap) := P.inFixedContext.matching_horizontal_map_gamma

theorem matching_fixed_vertical_labels
    (P : UniformBalancedPositionPreparation G C F hBalanced hNames)
    (p : extendBase P.inFixedContext.matchingPreparedFamily P.inFixedContext.baseInclusion) :
    (P.matchingFixedVerticalMap p).val.2 = p.val.2 := rfl

theorem matching_fixed_horizontal_labels
    (P : UniformBalancedPositionPreparation G C F hBalanced hNames)
    (p : extendBase P.inFixedContext.matchingPreparedFamily P.inFixedContext.baseInclusion) :
    (P.matchingFixedHorizontalMap p).val.2 = p.val.2 := rfl

theorem matching_fixed_vertical_jacobian_one (hc : CanonicalStructure.IsCanonical (M := M))
    (P : UniformBalancedPositionPreparation G C F hBalanced hNames) :
    VFAlmostEverywhere (rawSpecialSet hc (extendBase P.inFixedContext.matchingPreparedFamily P.inFixedContext.baseInclusion))
      (fun p => HasMixedVFJacobianAt (rawSpecialMap hc P.matchingFixedVerticalMap) p 1) :=
  P.inFixedContext.matching_vertical_jacobian_one hc

theorem matching_fixed_horizontal_jacobian_one (hc : CanonicalStructure.IsCanonical (M := M))
    (P : UniformBalancedPositionPreparation G C F hBalanced hNames) :
    VFAlmostEverywhere (rawSpecialSet hc (extendBase P.inFixedContext.matchingPreparedFamily P.inFixedContext.baseInclusion))
      (fun p => HasMixedVFJacobianAt (rawSpecialMap hc P.matchingFixedHorizontalMap) p 1) :=
  P.inFixedContext.matching_horizontal_jacobian_one hc

end IntegrationInACVF.Section7.UniformBalancedPositionPreparation
