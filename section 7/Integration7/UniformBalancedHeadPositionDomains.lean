module

public import Integration7.UniformBalancedHorizontalCentreValues

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! The mixed positioning image is exactly the full labelled head
projection of the balanced family, including every refinement parameter. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section5
open IntegrationInACVF.Section4 IntegrationInACVF.Section5

namespace IntegrationInACVF.Section7.UniformMixedCellPresentation
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {G : Base (M := M)} {S : Set M} {m : ℕ}
variable {A : DefSet (M := M) S 2 m}

theorem balanced_centre_in_head_projection (F : UniformMixedCellPresentation G (carrier A))
    (hBalanced : F.BalancedRows) (a : A) :
    ∃ b : A, F.parameters.toFun b = F.parameters.toFun a ∧ vfAt b.val 0 = F.centre a := by
  obtain ⟨r,hBal⟩ := hBalanced a
  have haR : (vfAt a.val 1,vfAt a.val 0) ∈ mixedPairFibre F.parameters a := by
    refine ⟨a,?_,rfl⟩
    funext i
    fin_cases i <;> rfl
  have haD : vfAt a.val 1 ∈ Cells.first (mixedPairFibre F.parameters a) := ⟨_,haR,rfl⟩
  have hE := hBal.2.2.1.bijective.1 haD
  obtain ⟨p,⟨b,hb,hP⟩,hp⟩ := hE
  have hHead : vfAt b.val 0 = F.localPosition a (vfAt a.val 1) := (congrFun hb 0).trans hp
  exact ⟨b,hP,hHead.trans (F.centre_eq_local_position a a rfl).symm⟩

set_option maxHeartbeats 1200000 in
theorem head_to_position_image_surjective (F : UniformMixedCellPresentation G (carrier A))
    (hBalanced : F.BalancedRows) (hNames : commonRealNames G ⊆ S) :
    Function.Surjective (F.headToPositionImage hBalanced hNames) := by
  rintro ⟨z,k,hk⟩
  obtain ⟨q,hq⟩ := k.property
  obtain ⟨a,rfl⟩ := (gamma_rv_graph_refinement_bijective A F.parameters hNames).2 q
  have hk' : k = VerticalOffsets.toKey _ (Map.toImage (gammaRVGraphRefinementMap A F.parameters hNames) a) :=
    Subtype.ext hq.symm
  subst k
  obtain ⟨b,hP,hHead⟩ := F.balanced_centre_in_head_projection hBalanced a
  have hOld := ((sameRV_iff _ _).mp (F.parameters_reflect_same_rv b a hP)).2
  refine ⟨Map.toImage (gammaRVGraphRefinementMap A F.parameters hNames) b,?_⟩
  apply Subtype.ext
  refine Eq.trans ?_ ((F.position_map_on_graph hNames a).symm.trans hk)
  change (fun _ : Fin 1 => vfAt b.val 0,Fin.append b.val.2 (F.parameters.toFun b)) =
    (fun _ : Fin 1 => F.centre a,Fin.append a.val.2 (F.parameters.toFun a))
  apply Prod.ext
  · funext i
    exact hHead
  · exact congrArg₂ Fin.append hOld hP

theorem position_image_eq_head_projection (F : UniformMixedCellPresentation G (carrier A))
    (hBalanced : F.BalancedRows) (hNames : commonRealNames G ⊆ S) :
    F.positionImage hNames = Map.image (coordinateProjectMap 0 (gammaRVGraphRefinement A F.parameters hNames)) := by
  apply PresentedSet.eq_of_carrier_eq
  ext z
  constructor
  · intro hz
    obtain ⟨q,hq⟩ := F.head_to_position_image_surjective hBalanced hNames ⟨z,hz⟩
    exact ⟨q,congrArg Subtype.val hq⟩
  · rintro ⟨q,rfl⟩
    exact F.position_image_covers_head hBalanced hNames q

end IntegrationInACVF.Section7.UniformMixedCellPresentation
