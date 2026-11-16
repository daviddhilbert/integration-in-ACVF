module

public import Integration7.MatchingHorizontalFibreGeometry

@[expose] public section

/-! Both actual matching-family translations are rectangles over all
recorded labels. Their translated coordinate RV tags remain fixed even
though the other coordinate is prepared later. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section5
open IntegrationInACVF.Section4 IntegrationInACVF.Section5

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {G : Base (M := M)} {m : ℕ}

namespace UniformMixedCellPresentation
variable {S : Set M} {A : DefSet (M := M) S 2 m}

theorem horizontal_translation_tail_tag_constant
    (F : UniformMixedCellPresentation G (carrier A)) (hBalanced : F.BalancedRows)
    (hNames : commonRealNames G ⊆ S)
    (p q : gammaRVGraphRefinement A F.parameters hNames) (hRV : p.val.2 = q.val.2) :
    rv (vfAt (F.horizontalTranslation hBalanced hNames p).val 1) =
      rv (vfAt (F.horizontalTranslation hBalanced hNames q).val 1) := by
  obtain ⟨a,rfl⟩ := (gamma_rv_graph_refinement_bijective A F.parameters hNames).2 p
  obtain ⟨b,rfl⟩ := (gamma_rv_graph_refinement_bijective A F.parameters hNames).2 q
  have hP : F.parameters.toFun b = F.parameters.toFun a := by
    funext i
    have hi := congrFun hRV (Fin.natAdd m i)
    change Fin.append a.val.2 (F.parameters.toFun a) (Fin.natAdd m i) =
      Fin.append b.val.2 (F.parameters.toFun b) (Fin.natAdd m i) at hi
    simpa only [Fin.append_right] using hi.symm
  obtain ⟨r,hBal⟩ := hBalanced a
  exact (F.horizontal_translation_tail_paradigm hBalanced hNames a r hBal a rfl).trans
    (F.horizontal_translation_tail_paradigm hBalanced hNames a r hBal b hP).symm

end UniformMixedCellPresentation

namespace UniformBalancedPositionPreparation
variable {C : BaseContext M} {A : DefSet (M := M) (C.base : Set M) 2 m}
variable {F : UniformMixedCellPresentation G (carrier A)} {hBalanced : F.BalancedRows}
variable {hNames : commonRealNames G ⊆ (C.base : Set M)}

theorem matching_forget_labels_eq (P : UniformBalancedPositionPreparation G C F hBalanced hNames)
    (p q : P.matchingPreparedFamily) (he : p.val.2 = q.val.2) :
    (P.matchingForgetMap p).val.2 = (P.matchingForgetMap q).val.2 := by
  have hp := congrArg (fun p : Point (M := M) 2 (m+F.arity) => p.2) (P.matching_forget_value p)
  have hq := congrArg (fun p : Point (M := M) 2 (m+F.arity) => p.2) (P.matching_forget_value q)
  exact hp.trans ((congrArg (fun r => r ∘ Fin.castAdd ((1+P.sourceArity)+(1+P.targetArity))) he).trans hq.symm)

theorem matching_vertical_head_tag (P : UniformBalancedPositionPreparation G C F hBalanced hNames)
    (q : P.matchingPreparedFamily) :
    rv (vfAt (P.matchingVerticalMap q).val 0) = F.refinementParadigm hNames (P.matchingForgetMap q) := by
  have h := F.vertical_translation_head_paradigm hNames (P.matchingForgetMap q)
  have hv := congrArg (fun p : Point (M := M) 2 (m+F.arity) => vfAt p 0) (P.matching_forget_value q)
  change rv (vfAt (P.matchingForgetMap q).val 0-
    (show VF (M := M) from (F.refinementCentreMap hNames (P.matchingForgetMap q)).val 0)) = _ at h
  rw [hv] at h
  exact h

theorem matching_horizontal_tail_tag (P : UniformBalancedPositionPreparation G C F hBalanced hNames)
    (q : P.matchingPreparedFamily) :
    rv (vfAt (P.matchingHorizontalMap q).val 1) =
      rv (vfAt (F.horizontalTranslation hBalanced hNames (P.matchingForgetMap q)).val 1) := by
  have hv := congrArg (fun p : Point (M := M) 2 (m+F.arity) => vfAt p 1) (P.matching_forget_value q)
  change rv (vfAt q.val 1-(show VF (M := M) from
    (F.horizontalCentreMap hBalanced hNames (P.matchingForgetMap q)).val 0)) =
    rv (vfAt (P.matchingForgetMap q).val 1-(show VF (M := M) from
    (F.horizontalCentreMap hBalanced hNames (P.matchingForgetMap q)).val 0))
  exact congrArg (fun x : VF (M := M) => rv (x-(show VF (M := M) from
    (F.horizontalCentreMap hBalanced hNames (P.matchingForgetMap q)).val 0))) hv.symm

theorem matching_vertical_image_rectangular
    (P : UniformBalancedPositionPreparation G C F hBalanced hNames)
    (hNonzero : ∀ a : A, (F.vertical.projection a).val.2 F.vertical.paradigm_index ≠ rv (0 : VF (M := M))) :
    RectangularRVFibres (carrier P.matchingVerticalImage) := by
  apply rectangular_rv_fibres_of_head_saturation _ (P.matching_vertical_image_head_saturated hNonzero)
  intro p q hRV
  obtain ⟨a,rfl⟩ := P.matching_vertical_map_bijective.2 p
  obtain ⟨b,rfl⟩ := P.matching_vertical_map_bijective.2 q
  exact (P.matching_vertical_head_tag a).trans
    ((F.refinement_paradigm_constant_on_labels hNames _ _ (P.matching_forget_labels_eq a b hRV)).trans
      (P.matching_vertical_head_tag b).symm)

theorem matching_horizontal_image_rectangular
    (P : UniformBalancedPositionPreparation G C F hBalanced hNames)
    (hNonzero : ∀ a : A, (F.vertical.projection a).val.2 F.vertical.paradigm_index ≠ rv (0 : VF (M := M))) :
    RectangularRVFibres (carrier P.matchingHorizontalImage) := by
  apply rectangular_rv_fibres_of_tail_saturation _
    (translated_rv_coordinate_saturated _ 1 _ P.matching_horizontal_centre_constant
      (P.matching_horizontal_source_fibre hNonzero))
  intro p q hRV
  obtain ⟨a,rfl⟩ := P.matching_horizontal_map_bijective.2 p
  obtain ⟨b,rfl⟩ := P.matching_horizontal_map_bijective.2 q
  exact (P.matching_horizontal_tail_tag a).trans
    ((F.horizontal_translation_tail_tag_constant hBalanced hNames _ _
      (P.matching_forget_labels_eq a b hRV)).trans (P.matching_horizontal_tail_tag b).symm)

end UniformBalancedPositionPreparation
end IntegrationInACVF.Section7
