import Integration7.MatchingVerticalFibreGeometry

/-! Complete horizontal fibres of the actual matching refinement.
The centre is the original positioning inverse, and lies in the matching
source inverse-special ball. All prepared keys stay fixed. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section5
open IntegrationInACVF.Section4 IntegrationInACVF.Section5 IntegrationInACVF.Section3ACVF

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {G : Base (M := M)} {m : ℕ}

theorem balanced_horizontal_fibre_at_inverse
    {D E : Set (VF (M := M))} {R : Set (VF (M := M) × VF (M := M))}
    {f : VF (M := M) → VF (M := M)} {r t : RV (M := M)}
    (hR : BalancedFibres.HasBalancedFibres D E R f r t)
    (hD : PaperBalls.IsOpenBall (Cells.rawSet D)) (u x : VF (M := M)) (hu : u ∈ D) (hux : f u = x) :
    {y : VF (M := M) | (y,x) ∈ R} = BalancedFibres.translatedRV r u := by
  ext y
  constructor
  · intro hy
    have hyD := (hR.subset hy).1
    apply (Set.ext_iff.mp (hR.horizontal y hyD) u).mp
    exact ⟨hu,by change (y,f u) ∈ R; rwa [hux]⟩
  · intro hy
    have hyD := BalancedBallClasses.positive_class_subset hR hD u hu hy
    have h := ((Set.ext_iff.mp (hR.horizontal y hyD) u).mpr hy).2
    change (y,f u) ∈ R at h
    rwa [hux] at h

namespace UniformBalancedPositionPreparation
variable {C : BaseContext M} {A : DefSet (M := M) (C.base : Set M) 2 m}
variable {F : UniformMixedCellPresentation G (carrier A)} {hBalanced : F.BalancedRows}
variable {hNames : commonRealNames G ⊆ (C.base : Set M)}

set_option maxHeartbeats 2000000 in
theorem matching_horizontal_inverse_in_source_ball
    (P : UniformBalancedPositionPreparation G C F hBalanced hNames) (a : A)
    (hMatch : (Map.toImage (gammaRVGraphRefinementMap A F.parameters hNames) a).val ∈ P.matchingPart) :
    let q := Map.toImage (gammaRVGraphRefinementMap A F.parameters hNames) a
    let y := (F.horizontalCentreMap hBalanced hNames q).val 0
    y ∈ InverseOneCells.typedBody P.sourceSpecial (P.preparedTailMap q) ∧
      F.localPosition a y = vfAt a.val 0 := by
  intro q y
  let f := Map.toImage (F.positionMap hNames)
  let hf := F.position_to_image_bijective hBalanced hNames
  let u := Map.inverse f hf (F.headToPositionImage hBalanced hNames q)
  have hInv := congrArg Subtype.val (Map.apply_inverse f hf (F.headToPositionImage hBalanced hNames q))
  have hLabels := congrArg (fun p : Point (M := M) 1 (m+F.arity) => p.2) hInv
  change u.val.2 = Fin.append a.val.2 (F.parameters.toFun a) at hLabels
  have hHead := congrArg (fun p : Point (M := M) 1 (m+F.arity) => vfAt p 0) hInv
  change vfAt (F.positionMap hNames u).val 0 = vfAt a.val 0 at hHead
  have hRow := F.position_map_on_label_fibre hNames a u hLabels
  have hPosition : F.localPosition a (vfAt u.val 0) = vfAt a.val 0 := hRow.1.symm.trans hHead
  have hSame := (P.matching_part_mem q).mp hMatch
  have hBodies : InverseOneCells.typedBody P.targetSpecial (P.conjugateMap (P.preparedTailMap q)) =
      InverseOneCells.typedBody P.targetSpecial (P.preparedHeadMap q) := by
    ext x
    exact Set.ext_iff.mp (InverseBodies.body_sameRV P.targetSpecial _ _ hSame.symm) x.val
  have hImage := (P.inverse_tail_body_position_image a).trans hBodies
  have hOwn := ((P.pair_key_labels_iff_bodies q q).mp rfl).2.2
  obtain ⟨b,hb,hbx⟩ := (Set.ext_iff.mp hImage (vfAt a.val 0)).mpr hOwn
  obtain ⟨r,hBal⟩ := hBalanced a
  have hbu : b = vfAt u.val 0 := hBal.2.2.1.bijective.2.1
    (P.inverse_tail_body_in_row a hb) hRow.2 (hbx.trans hPosition.symm)
  have hMember : vfAt u.val 0 ∈ InverseOneCells.typedBody P.sourceSpecial (P.preparedTailMap q) := by
    rw [← hbu]
    exact hb
  exact ⟨hMember,hPosition⟩

set_option maxHeartbeats 2000000 in
theorem matching_horizontal_source_fibre_on_graph
    (P : UniformBalancedPositionPreparation G C F hBalanced hNames) (a : A)
    (hMatch : (Map.toImage (gammaRVGraphRefinementMap A F.parameters hNames) a).val ∈ P.matchingPart)
    (ht : (F.vertical.projection a).val.2 F.vertical.paradigm_index ≠ rv (0 : VF (M := M))) :
    let p : P.matchingNative := ⟨(Map.toImage (gammaRVGraphRefinementMap A F.parameters hNames) a).val,hMatch⟩
    let q := Map.toImage (gammaRVGraphRefinementMap P.matchingNative P.matchingKeyLabels hNames) p
    ∃ r : RV (M := M), {x : VF (M := M) | replace 1 q.val x ∈ carrier P.matchingPreparedFamily} =
      BalancedFibres.translatedRV r ((P.matchingHorizontalCentre q).val 0) := by
  intro p q
  let q₀ := Map.toImage (gammaRVGraphRefinementMap A F.parameters hNames) a
  obtain ⟨r,hB,hE,hR⟩ := P.matching_prepared_family_row_geometry a hMatch ht
  have hInverse := P.matching_horizontal_inverse_in_source_ball a hMatch
  have hForget : P.matchingForgetMap q = q₀ := by
    apply Subtype.ext
    have h := P.matching_forget_value q
    refine h.trans ?_
    exact Prod.ext rfl (funext fun i => Fin.append_left _ _ i)
  have hCentre : (P.matchingHorizontalCentre q).val 0 =
      (F.horizontalCentreMap hBalanced hNames q₀).val 0 := by
    change (F.horizontalCentreMap hBalanced hNames (P.matchingForgetMap q)).val 0 = _
    rw [hForget]
  have hFibre := balanced_horizontal_fibre_at_inverse hR hB _ _ hInverse.1 hInverse.2
  refine ⟨r,?_⟩
  ext x
  have hPoint : replace 1 q.val x = ((pairPoint x (vfAt a.val 0)).1,q.val.2) := by
    apply Prod.ext
    · funext i
      fin_cases i <;> rfl
    · rfl
  change replace 1 q.val x ∈ carrier P.matchingPreparedFamily ↔
    rv (x-(show VF (M := M) from (P.matchingHorizontalCentre q).val 0)) = r
  rw [hPoint,hCentre]
  exact Set.ext_iff.mp hFibre x

theorem matching_horizontal_source_fibre
    (P : UniformBalancedPositionPreparation G C F hBalanced hNames)
    (hNonzero : ∀ a : A, (F.vertical.projection a).val.2 F.vertical.paradigm_index ≠ rv (0 : VF (M := M)))
    (q : P.matchingPreparedFamily) :
    ∃ r : RV (M := M), {x : VF (M := M) | replace 1 q.val x ∈ carrier P.matchingPreparedFamily} =
      BalancedFibres.translatedRV r ((P.matchingHorizontalCentre q).val 0) := by
  obtain ⟨p,rfl⟩ := (gamma_rv_graph_refinement_bijective P.matchingNative P.matchingKeyLabels hNames).2 q
  let p₀ := P.matchingSubsetMap p
  obtain ⟨a,ha⟩ := (gamma_rv_graph_refinement_bijective A F.parameters hNames).2 p₀
  have hMatch : (Map.toImage (gammaRVGraphRefinementMap A F.parameters hNames) a).val ∈ P.matchingPart := by
    have he := congrArg Subtype.val ha
    exact Eq.mp (congrArg (fun z : Point (M := M) 2 (m+F.arity) => z ∈ P.matchingPart) he.symm) p.property
  let p' : P.matchingNative := ⟨(Map.toImage (gammaRVGraphRefinementMap A F.parameters hNames) a).val,hMatch⟩
  have hp : p = p' := Subtype.ext (congrArg Subtype.val ha).symm
  subst p
  exact P.matching_horizontal_source_fibre_on_graph a hMatch (hNonzero a)

theorem matching_horizontal_image_swapped_head_saturated
    (P : UniformBalancedPositionPreparation G C F hBalanced hNames)
    (hNonzero : ∀ a : A, (F.vertical.projection a).val.2 F.vertical.paradigm_index ≠ rv (0 : VF (M := M))) :
    HeadSaturated (carrier (vfPermutationImage P.matchingHorizontalImage (Equiv.swap 0 1))) :=
  swapped_horizontal_saturated _ (translated_rv_coordinate_saturated _ 1 _
    P.matching_horizontal_centre_constant (P.matching_horizontal_source_fibre hNonzero))

end UniformBalancedPositionPreparation
end IntegrationInACVF.Section7
