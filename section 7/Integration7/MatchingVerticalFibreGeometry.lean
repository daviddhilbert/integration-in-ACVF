module

public import Integration7.MatchingFamilyTranslationMaps
public import Integration7.BalancedTranslationProductImages

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! Complete vertical fibres of the actual matching refinement. The
recorded keys remain frozen throughout the translated RV class. -/
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

theorem refinement_centre_on_label_fibre (F : UniformMixedCellPresentation G (carrier A))
    (hNames : commonRealNames G ⊆ S) (a : A)
    (q : gammaRVGraphRefinement A F.parameters hNames)
    (hLabels : q.val.2 = Fin.append a.val.2 (F.parameters.toFun a)) :
    (F.refinementCentreMap hNames q).val 0 = F.localPosition a (vfAt q.val 1) := by
  obtain ⟨b,rfl⟩ := (gamma_rv_graph_refinement_bijective A F.parameters hNames).2 q
  have hP : F.parameters.toFun b = F.parameters.toFun a := by
    funext i
    have hi := congrFun hLabels (Fin.natAdd m i)
    change Fin.append b.val.2 (F.parameters.toFun b) (Fin.natAdd m i) =
      Fin.append a.val.2 (F.parameters.toFun a) (Fin.natAdd m i) at hi
    simpa only [Fin.append_right] using hi
  change F.centre (Map.inverse (Map.toImage (gammaRVGraphRefinementMap A F.parameters hNames))
    (gamma_rv_graph_refinement_bijective A F.parameters hNames)
    (Map.toImage (gammaRVGraphRefinementMap A F.parameters hNames) b)) = _
  rw [Map.inverse_apply]
  exact F.centre_eq_local_position a b hP

end UniformMixedCellPresentation

namespace UniformBalancedPositionPreparation
variable {C : BaseContext M} {A : DefSet (M := M) (C.base : Set M) 2 m}
variable {F : UniformMixedCellPresentation G (carrier A)} {hBalanced : F.BalancedRows}
variable {hNames : commonRealNames G ⊆ (C.base : Set M)}

theorem matching_vertical_centre_on_old_label
    (P : UniformBalancedPositionPreparation G C F hBalanced hNames) (a : A)
    (q : P.matchingPreparedFamily)
    (hOld : q.val.2 ∘ Fin.castAdd ((1+P.sourceArity)+(1+P.targetArity)) =
      Fin.append a.val.2 (F.parameters.toFun a)) :
    (P.matchingVerticalCentre q).val 0 = F.localPosition a (vfAt q.val 1) := by
  have hLabels := (congrArg (fun p : Point (M := M) 2 (m+F.arity) => p.2)
    (P.matching_forget_value q)).trans hOld
  have hCentre := F.refinement_centre_on_label_fibre hNames a (P.matchingForgetMap q) hLabels
  have hVF := congrArg (fun p : Point (M := M) 2 (m+F.arity) => vfAt p 1) (P.matching_forget_value q)
  exact hCentre.trans (congrArg (F.localPosition a) hVF)

set_option maxHeartbeats 1800000 in
theorem matching_vertical_source_fibre_on_graph
    (P : UniformBalancedPositionPreparation G C F hBalanced hNames) (a : A)
    (hMatch : (Map.toImage (gammaRVGraphRefinementMap A F.parameters hNames) a).val ∈ P.matchingPart)
    (ht : (F.vertical.projection a).val.2 F.vertical.paradigm_index ≠ rv (0 : VF (M := M))) :
    let p : P.matchingNative := ⟨(Map.toImage (gammaRVGraphRefinementMap A F.parameters hNames) a).val,hMatch⟩
    let q := Map.toImage (gammaRVGraphRefinementMap P.matchingNative P.matchingKeyLabels hNames) p
    {x : VF (M := M) | replace 0 q.val x ∈ carrier P.matchingPreparedFamily} =
      BalancedFibres.translatedRV ((F.vertical.projection a).val.2 F.vertical.paradigm_index)
        ((P.matchingVerticalCentre q).val 0) := by
  intro p q
  obtain ⟨r,hB,hE,hR⟩ := P.matching_prepared_family_row_geometry a hMatch ht
  have hOwn := ((P.pair_key_labels_iff_bodies
    (Map.toImage (gammaRVGraphRefinementMap A F.parameters hNames) a)
    (Map.toImage (gammaRVGraphRefinementMap A F.parameters hNames) a)).mp rfl).2.1
  have hCentre := P.matching_vertical_centre_on_old_label a q (by
    funext i
    exact Fin.append_left _ _ i)
  ext x
  have hPoint : replace 0 q.val x = ((pairPoint (vfAt a.val 1) x).1,q.val.2) := by
    apply Prod.ext
    · funext i
      fin_cases i <;> rfl
    · rfl
  change replace 0 q.val x ∈ carrier P.matchingPreparedFamily ↔
    rv (x-(show VF (M := M) from (P.matchingVerticalCentre q).val 0)) =
      (F.vertical.projection a).val.2 F.vertical.paradigm_index
  rw [hPoint]
  change (vfAt a.val 1,x) ∈ ParameterizedCells.twoFibre (carrier P.matchingPreparedFamily) q.val.2 ↔ _
  rw [hCentre]
  exact Set.ext_iff.mp (hR.vertical (vfAt a.val 1) hOwn) x

theorem matching_vertical_source_fibre
    (P : UniformBalancedPositionPreparation G C F hBalanced hNames)
    (hNonzero : ∀ a : A, (F.vertical.projection a).val.2 F.vertical.paradigm_index ≠ rv (0 : VF (M := M)))
    (q : P.matchingPreparedFamily) :
    ∃ t : RV (M := M), {x : VF (M := M) | replace 0 q.val x ∈ carrier P.matchingPreparedFamily} =
      BalancedFibres.translatedRV t ((P.matchingVerticalCentre q).val 0) := by
  obtain ⟨p,rfl⟩ := (gamma_rv_graph_refinement_bijective P.matchingNative P.matchingKeyLabels hNames).2 q
  let p₀ := P.matchingSubsetMap p
  obtain ⟨a,ha⟩ := (gamma_rv_graph_refinement_bijective A F.parameters hNames).2 p₀
  have hMatch : (Map.toImage (gammaRVGraphRefinementMap A F.parameters hNames) a).val ∈ P.matchingPart := by
    have he := congrArg Subtype.val ha
    exact Eq.mp (congrArg (fun z : Point (M := M) 2 (m+F.arity) => z ∈ P.matchingPart) he.symm) p.property
  let p' : P.matchingNative := ⟨(Map.toImage (gammaRVGraphRefinementMap A F.parameters hNames) a).val,hMatch⟩
  have hp : p = p' := Subtype.ext (congrArg Subtype.val ha).symm
  subst p
  exact ⟨_,P.matching_vertical_source_fibre_on_graph a hMatch (hNonzero a)⟩

theorem matching_vertical_image_head_saturated
    (P : UniformBalancedPositionPreparation G C F hBalanced hNames)
    (hNonzero : ∀ a : A, (F.vertical.projection a).val.2 F.vertical.paradigm_index ≠ rv (0 : VF (M := M))) :
    HeadSaturated (carrier P.matchingVerticalImage) :=
  translated_rv_coordinate_saturated _ 0 _ P.matching_vertical_centre_constant
    (P.matching_vertical_source_fibre hNonzero)

end UniformBalancedPositionPreparation
end IntegrationInACVF.Section7
