module

public import Integration7.MatchingProjectionCompleteness
public import Integration7.RectangleFamilyVolumePreparations
public import Integration7.SwappedRectangleProjectionDomains

@[expose] public section

/-! Actual full VF-two RV-pullback preparations of the two matching
translations, using the already chosen compatible unary preparations.
The standard rectangle preparation record supplies their full
Jacobian-one maps and all retained old labels. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section5
open IntegrationInACVF.Section4 IntegrationInACVF.Section5 IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

theorem native_tail_key_image_eq_projection {S : Set M} {l : ℕ} (H : DefSet (M := M) S 2 l) :
    VerticalOffsets.keyImage H = Map.image (coordinateProjectMap 1 H) := by
  apply defSet_eq_of_carrier_eq
  have hValue (p : H) : (VerticalOffsets.keyMap H p).val = (coordinateProjectMap 1 H p).val := by
    apply Prod.ext
    · funext i
      fin_cases i
      rfl
    · rfl
  ext q
  constructor
  · rintro ⟨p,hp⟩
    exact ⟨p,(hValue p).symm.trans hp⟩
  · rintro ⟨p,hp⟩
    exact ⟨p,(hValue p).trans hp⟩

namespace UniformBalancedPositionPreparation
variable {G : Base (M := M)} {m : ℕ} {C : BaseContext M}
variable {A : DefSet (M := M) (C.base : Set M) 2 m}
variable {F : UniformMixedCellPresentation G (carrier A)} {hBalanced : F.BalancedRows}
variable {hNames : commonRealNames G ⊆ (C.base : Set M)}

def matchingVerticalPullbackPreparation
    (P : UniformBalancedPositionPreparation G C F hBalanced hNames)
    (hNonzero : ∀ a : A, (F.vertical.projection a).val.2 F.vertical.paradigm_index ≠ rv (0 : VF (M := M)))
    (L : PreparedKeyLabelSpecialPreparation P.sourceSpecial
      (extendBase P.matchingVerticalTailDomain P.baseInclusion) P.matchingOldLabelIndex P.matchingTailKeyIndex
      (fun p hp => P.matching_vertical_tail_old_mem ⟨p,hp⟩) G) :
    RectangleFamilyPullbackPreparation G (extendBase P.matchingVerticalImage P.baseInclusion) := by
  let V := extendBase P.matchingVerticalImage P.baseInclusion
  let X := vfPermutationImage V (Equiv.swap 0 1)
  have hV : GammaSetDefinable G (carrier V) := P.matching_vertical_image_gamma
  have hX := gamma_vfPermutationImage V hV (Equiv.swap 0 1)
  have hRect : RectangularRVFibres (carrier V) := P.matching_vertical_image_rectangular hNonzero
  have hRectX := rectangular_rv_fibres_swap V hRect
  have hHead : HeadSaturated (carrier V) := P.matching_vertical_image_head_saturated hNonzero
  have hTailX := swapped_tail_saturated_of_head V hHead
  have hProjection : Map.image (coordinateProjectMap 0 X) =
      extendBase P.matchingVerticalTailDomain P.baseInclusion := by
    refine (swapped_rectangle_head_projection V).trans ((native_tail_key_image_eq_projection V).symm.trans ?_)
    exact defSet_eq_of_carrier_eq rfl
  let T := specialCastBoth L.special hProjection.symm rfl
  have hT : GammaChainDefinable G T.chain := gamma_special_cast_both _ _ _ L.gamma
  have hLT := P.matching_vertical_recorded_target_pullback hNonzero L
  let R := rectangleFamilyHeadPreparation X hRectX T hLT
  have hR := rectangle_family_head_preparation_map_gamma X hX hRectX T hT hLT
  have hZ := rectangle_family_head_preparation_target_gamma X hX hRectX T hT hLT
  have hSat := rectangle_family_prepared_target_tail_saturated X hRectX T hLT hTailX
  let I : HeadPreparation V := ⟨_,V,Map.id V,specialRelative_id V 0,hHead⟩
  exact ⟨I,R,gamma_identity_graph V hV,hV,hR,hZ,
    is_rv_pullback_of_two_coordinate_saturation R.saturated hSat⟩

def matchingHorizontalPullbackPreparation
    (P : UniformBalancedPositionPreparation G C F hBalanced hNames)
    (hNonzero : ∀ a : A, (F.vertical.projection a).val.2 F.vertical.paradigm_index ≠ rv (0 : VF (M := M)))
    (L : PreparedKeyLabelSpecialPreparation P.targetSpecial
      (extendBase P.matchingHorizontalHeadDomain P.baseInclusion) P.matchingOldLabelIndex P.matchingHeadKeyIndex
      (fun p hp => P.matching_horizontal_head_old_mem ⟨p,hp⟩) G) :
    RectangleFamilyPullbackPreparation G (extendBase P.matchingHorizontalImage P.baseInclusion) := by
  let H := extendBase P.matchingHorizontalImage P.baseInclusion
  have hH : GammaSetDefinable G (carrier H) := P.matching_horizontal_image_gamma
  have hRect : RectangularRVFibres (carrier H) := P.matching_horizontal_image_rectangular hNonzero
  have hTail : TailSaturated (carrier H) :=
    translated_rv_coordinate_saturated _ 1 _ P.matching_horizontal_centre_constant
      (P.matching_horizontal_source_fibre hNonzero)
  have hProjection : Map.image (coordinateProjectMap 0 H) =
      extendBase P.matchingHorizontalHeadDomain P.baseInclusion := defSet_eq_of_carrier_eq rfl
  let T := specialCastBoth L.special hProjection.symm rfl
  have hT : GammaChainDefinable G T.chain := gamma_special_cast_both _ _ _ L.gamma
  have hLT := P.matching_horizontal_recorded_target_pullback hNonzero L
  let R := rectangleFamilyHeadPreparation H hRect T hLT
  have hR := rectangle_family_head_preparation_map_gamma H hH hRect T hT hLT
  have hZ := rectangle_family_head_preparation_target_gamma H hH hRect T hT hLT
  have hSat := rectangle_family_prepared_target_tail_saturated H hRect T hLT hTail
  have hPullback := is_rv_pullback_of_two_coordinate_saturation R.saturated hSat
  let X := vfPermutationImage R.target (Equiv.swap 0 1)
  have hX := gamma_vfPermutationImage R.target hZ (Equiv.swap 0 1)
  have hXP := vf_permutation_image_pullback R.target hPullback (Equiv.swap 0 1)
  let I : HeadPreparation X := ⟨_,X,Map.id X,specialRelative_id X 0,headSaturated_of_pullback hXP⟩
  exact ⟨R,I,hR,hZ,gamma_identity_graph X hX,hX,hXP⟩

end UniformBalancedPositionPreparation
end IntegrationInACVF.Section7
