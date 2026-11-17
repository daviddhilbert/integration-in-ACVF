module

public import Integration7.MatchingFullPullbackPreparations
public import Integration7.RectanglePreparedLabelFibres

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! All RV fibres of the two actual full prepared matching targets
are determined by the original carried family labels. The canonical
retained-label selectors agree with the unary lifted suffix selectors. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section5
open IntegrationInACVF.Section4 IntegrationInACVF.Section5 IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

theorem rv_labels_determine_vf_permutation {S : Set M} {n m d : ℕ}
    (H : DefSet (M := M) S n m) (σ : Equiv.Perm (Fin n)) (ρ : Fin d → Fin m)
    (hH : ∀ p q : H, p.val.2 ∘ ρ = q.val.2 ∘ ρ → SameRV p.val q.val)
    (p q : vfPermutationImage H σ) (he : p.val.2 ∘ ρ = q.val.2 ∘ ρ) : SameRV p.val q.val := by
  obtain ⟨a,ha⟩ := p.property
  obtain ⟨b,hb⟩ := q.property
  have hLabels : a.val.2 ∘ ρ = b.val.2 ∘ ρ := by
    have hpa := congrArg (fun p : Point (M := M) n m => p.2 ∘ ρ) ha
    have hqb := congrArg (fun p : Point (M := M) n m => p.2 ∘ ρ) hb
    exact hpa.trans (he.trans hqb.symm)
  obtain ⟨hVF,hRV⟩ := (sameRV_iff _ _).mp (hH a b hLabels)
  have hSame : SameRV (vfPermutation σ a.val) (vfPermutation σ b.val) :=
    (sameRV_iff _ _).mpr ⟨fun i => hVF (σ i),hRV⟩
  exact Eq.mp (congrArg₂ SameRV ha hb) hSame

namespace UniformBalancedPositionPreparation
variable {G : Base (M := M)} {m : ℕ} {C : BaseContext M}
variable {A : DefSet (M := M) (C.base : Set M) 2 m}
variable {F : UniformMixedCellPresentation G (carrier A)} {hBalanced : F.BalancedRows}
variable {hNames : commonRealNames G ⊆ (C.base : Set M)}

theorem matching_vertical_image_tag_constant
    (P : UniformBalancedPositionPreparation G C F hBalanced hNames)
    (p q : P.matchingVerticalImage) (he : p.val.2 = q.val.2) :
    rv (vfAt p.val 0) = rv (vfAt q.val 0) := by
  obtain ⟨a,rfl⟩ := P.matching_vertical_map_bijective.2 p
  obtain ⟨b,rfl⟩ := P.matching_vertical_map_bijective.2 q
  exact (P.matching_vertical_head_tag a).trans
    ((F.refinement_paradigm_constant_on_labels hNames _ _ (P.matching_forget_labels_eq a b he)).trans
      (P.matching_vertical_head_tag b).symm)

theorem matching_horizontal_image_tag_constant
    (P : UniformBalancedPositionPreparation G C F hBalanced hNames)
    (p q : P.matchingHorizontalImage) (he : p.val.2 = q.val.2) :
    rv (vfAt p.val 1) = rv (vfAt q.val 1) := by
  obtain ⟨a,rfl⟩ := P.matching_horizontal_map_bijective.2 p
  obtain ⟨b,rfl⟩ := P.matching_horizontal_map_bijective.2 q
  exact (P.matching_horizontal_tail_tag a).trans
    ((F.horizontal_translation_tail_tag_constant hBalanced hNames _ _
      (P.matching_forget_labels_eq a b he)).trans (P.matching_horizontal_tail_tag b).symm)

theorem matching_vertical_preparation_old_index
    (P : UniformBalancedPositionPreparation G C F hBalanced hNames)
    (hNonzero : ∀ a : A, (F.vertical.projection a).val.2 F.vertical.paradigm_index ≠ rv (0 : VF (M := M)))
    (L : PreparedKeyLabelSpecialPreparation P.sourceSpecial
      (extendBase P.matchingVerticalTailDomain P.baseInclusion) P.matchingOldLabelIndex P.matchingTailKeyIndex
      (fun p hp => P.matching_vertical_tail_old_mem ⟨p,hp⟩) G)
    (i : Fin ((m+F.arity)+((1+P.sourceArity)+(1+P.targetArity)))) :
    (P.matchingVerticalPullbackPreparation hNonzero L).volumeLabelIndex i =
      suffixIndex (special_chain_rvArity_le L.special.chain) i := by
  apply Fin.ext
  change L.arity-((m+F.arity)+((1+P.sourceArity)+(1+P.targetArity)))+
    (((m+F.arity)+((1+P.sourceArity)+(1+P.targetArity)))-
      ((m+F.arity)+((1+P.sourceArity)+(1+P.targetArity)))+i.val) = _
  simp only [Nat.sub_self,zero_add]
  rfl

theorem matching_horizontal_preparation_old_index
    (P : UniformBalancedPositionPreparation G C F hBalanced hNames)
    (hNonzero : ∀ a : A, (F.vertical.projection a).val.2 F.vertical.paradigm_index ≠ rv (0 : VF (M := M)))
    (L : PreparedKeyLabelSpecialPreparation P.targetSpecial
      (extendBase P.matchingHorizontalHeadDomain P.baseInclusion) P.matchingOldLabelIndex P.matchingHeadKeyIndex
      (fun p hp => P.matching_horizontal_head_old_mem ⟨p,hp⟩) G)
    (i : Fin ((m+F.arity)+((1+P.sourceArity)+(1+P.targetArity)))) :
    (P.matchingHorizontalPullbackPreparation hNonzero L).volumeLabelIndex i =
      suffixIndex (special_chain_rvArity_le L.special.chain) i := by
  apply Fin.ext
  change L.arity-L.arity+
    (L.arity-((m+F.arity)+((1+P.sourceArity)+(1+P.targetArity)))+i.val) = _
  simp only [Nat.sub_self,zero_add]
  rfl

set_option maxHeartbeats 2000000 in
theorem matching_vertical_prepared_labels_determine
    (P : UniformBalancedPositionPreparation G C F hBalanced hNames)
    (hNonzero : ∀ a : A, (F.vertical.projection a).val.2 F.vertical.paradigm_index ≠ rv (0 : VF (M := M)))
    (L : PreparedKeyLabelSpecialPreparation P.sourceSpecial
      (extendBase P.matchingVerticalTailDomain P.baseInclusion) P.matchingOldLabelIndex P.matchingTailKeyIndex
      (fun p hp => P.matching_vertical_tail_old_mem ⟨p,hp⟩) G)
    (p q : (P.matchingVerticalPullbackPreparation hNonzero L).volumeTarget)
    (he : p.val.2 ∘ (P.matchingVerticalPullbackPreparation hNonzero L).volumeLabelIndex =
      q.val.2 ∘ (P.matchingVerticalPullbackPreparation hNonzero L).volumeLabelIndex) : SameRV p.val q.val := by
  let V := extendBase P.matchingVerticalImage P.baseInclusion
  let X := vfPermutationImage V (Equiv.swap 0 1)
  have hProjection : Map.image (coordinateProjectMap 0 X) =
      extendBase P.matchingVerticalTailDomain P.baseInclusion := by
    refine (swapped_rectangle_head_projection V).trans ((native_tail_key_image_eq_projection V).symm.trans ?_)
    exact defSet_eq_of_carrier_eq rfl
  let T := specialCastBoth L.special hProjection.symm rfl
  have hLT := P.matching_vertical_recorded_target_pullback hNonzero L
  have hRectV : RectangularRVFibres (carrier V) := P.matching_vertical_image_rectangular hNonzero
  have hRectX := rectangular_rv_fibres_swap V hRectV
  have hTag : ∀ a b : X, a.val.2=b.val.2 → rv (vfAt a.val 1)=rv (vfAt b.val 1) := by
    intro a b hab
    obtain ⟨a₀,ha⟩ := a.property
    obtain ⟨b₀,hb⟩ := b.property
    have hLabels := (congrArg (fun p : Point (M := M) 2
      ((m+F.arity)+((1+P.sourceArity)+(1+P.targetArity))) => p.2) ha).trans
      (hab.trans (congrArg (fun p : Point (M := M) 2
        ((m+F.arity)+((1+P.sourceArity)+(1+P.targetArity))) => p.2) hb).symm)
    have h := P.matching_vertical_image_tag_constant a₀ b₀ hLabels
    have hpa := congrArg (fun p : Point (M := M) 2
      ((m+F.arity)+((1+P.sourceArity)+(1+P.targetArity))) => rv (vfAt p 1)) ha
    have hqb := congrArg (fun p : Point (M := M) 2
      ((m+F.arity)+((1+P.sourceArity)+(1+P.targetArity))) => rv (vfAt p 1)) hb
    exact hpa.symm.trans (h.trans hqb)
  have hDet := rectangle_family_prepared_labels_determine X hRectX T hLT hTag
    (fun a b h => L.suffix_labels_determine a b h)
  apply rv_labels_determine_vf_permutation _ (Equiv.swap 0 1)
    (suffixIndex (special_chain_rvArity_le L.special.chain)) hDet p q
  funext i
  have h := congrFun he i
  dsimp only [Function.comp_apply] at h ⊢
  rw [P.matching_vertical_preparation_old_index hNonzero L i] at h
  exact h

set_option maxHeartbeats 2000000 in
theorem matching_horizontal_prepared_labels_determine
    (P : UniformBalancedPositionPreparation G C F hBalanced hNames)
    (hNonzero : ∀ a : A, (F.vertical.projection a).val.2 F.vertical.paradigm_index ≠ rv (0 : VF (M := M)))
    (L : PreparedKeyLabelSpecialPreparation P.targetSpecial
      (extendBase P.matchingHorizontalHeadDomain P.baseInclusion) P.matchingOldLabelIndex P.matchingHeadKeyIndex
      (fun p hp => P.matching_horizontal_head_old_mem ⟨p,hp⟩) G)
    (p q : (P.matchingHorizontalPullbackPreparation hNonzero L).volumeTarget)
    (he : p.val.2 ∘ (P.matchingHorizontalPullbackPreparation hNonzero L).volumeLabelIndex =
      q.val.2 ∘ (P.matchingHorizontalPullbackPreparation hNonzero L).volumeLabelIndex) : SameRV p.val q.val := by
  let H := extendBase P.matchingHorizontalImage P.baseInclusion
  have hProjection : Map.image (coordinateProjectMap 0 H) =
      extendBase P.matchingHorizontalHeadDomain P.baseInclusion := defSet_eq_of_carrier_eq rfl
  let T := specialCastBoth L.special hProjection.symm rfl
  have hLT := P.matching_horizontal_recorded_target_pullback hNonzero L
  have hRect : RectangularRVFibres (carrier H) := P.matching_horizontal_image_rectangular hNonzero
  have hDet := rectangle_family_prepared_labels_determine H hRect T hLT
    P.matching_horizontal_image_tag_constant (fun a b h => L.suffix_labels_determine a b h)
  have hOnce := rv_labels_determine_vf_permutation _ (Equiv.swap 0 1)
    (suffixIndex (special_chain_rvArity_le L.special.chain)) hDet
  apply rv_labels_determine_vf_permutation _ (Equiv.swap 0 1)
    (suffixIndex (special_chain_rvArity_le L.special.chain)) hOnce p q
  funext i
  have h := congrFun he i
  dsimp only [Function.comp_apply] at h ⊢
  rw [P.matching_horizontal_preparation_old_index hNonzero L i] at h
  exact h

end UniformBalancedPositionPreparation
end IntegrationInACVF.Section7
