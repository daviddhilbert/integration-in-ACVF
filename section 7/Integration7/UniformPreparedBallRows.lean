module

public import Integration7.UniformPreparedPairKeys
public import Integration7.PreparedBallRectangleGeometry

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! The prepared inverse balls sit in the actual original balanced
rows. Their positioning images are the matching target inverse balls;
different target keys therefore give actual rectangle row pieces. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section5
open IntegrationInACVF.Section4 IntegrationInACVF.Section5

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {G : Base (M := M)} {m : ℕ}

namespace UniformMixedCellPresentation
variable {S : Set M} {A : DefSet (M := M) S 2 m}

theorem position_map_on_label_fibre (F : UniformMixedCellPresentation G (carrier A))
    (hNames : commonRealNames G ⊆ S) (a : A)
    (u : VerticalOffsets.keyImage (gammaRVGraphRefinement A F.parameters hNames))
    (hLabels : u.val.2 = Fin.append a.val.2 (F.parameters.toFun a)) :
    vfAt (F.positionMap hNames u).val 0 = F.localPosition a (vfAt u.val 0) ∧
      vfAt u.val 0 ∈ Cells.first (mixedPairFibre F.parameters a) := by
  obtain ⟨b,rfl⟩ := F.tail_key_source hNames u
  have hP : F.parameters.toFun b = F.parameters.toFun a := by
    funext i
    have hi := congrFun hLabels (Fin.natAdd m i)
    change Fin.append b.val.2 (F.parameters.toFun b) (Fin.natAdd m i) =
      Fin.append a.val.2 (F.parameters.toFun a) (Fin.natAdd m i) at hi
    simpa only [Fin.append_right] using hi
  constructor
  · have h := congrArg (fun z : Point (M := M) 1 (m+F.arity) => vfAt z 0)
      (F.position_map_on_graph hNames b)
    exact h.trans (F.centre_eq_local_position a b hP)
  · refine ⟨(vfAt b.val 1,vfAt b.val 0),⟨b,?_,hP⟩,rfl⟩
    funext i
    fin_cases i <;> rfl

end UniformMixedCellPresentation

namespace UniformBalancedPositionPreparation
variable {C : BaseContext M} {A : DefSet (M := M) (C.base : Set M) 2 m}
variable {F : UniformMixedCellPresentation G (carrier A)} {hBalanced : F.BalancedRows}
variable {hNames : commonRealNames G ⊆ (C.base : Set M)}

theorem prepared_tail_inverse_labels (P : UniformBalancedPositionPreparation G C F hBalanced hNames)
    (q : gammaRVGraphRefinement A F.parameters hNames) :
    (P.sourceSpecial.inverseMap (P.preparedTailMap q)).val.2 = q.val.2 := by
  change (P.sourceSpecial.inverseMap (P.sourceSpecial.toMap _)).val.2 = _
  rw [P.sourceSpecial.inverse_apply]
  rfl

theorem prepared_head_inverse_labels (P : UniformBalancedPositionPreparation G C F hBalanced hNames)
    (q : gammaRVGraphRefinement A F.parameters hNames) :
    (P.targetSpecial.inverseMap (P.preparedHeadMap q)).val.2 = q.val.2 := by
  change (P.targetSpecial.inverseMap (P.targetSpecial.toMap _)).val.2 = _
  rw [P.targetSpecial.inverse_apply]
  rfl

theorem prepared_position_inverse_labels (P : UniformBalancedPositionPreparation G C F hBalanced hNames)
    (q : gammaRVGraphRefinement A F.parameters hNames) :
    (P.targetSpecial.inverseMap (P.conjugateMap (P.preparedTailMap q))).val.2 = q.val.2 := by
  change (P.targetSpecial.inverseMap (P.targetSpecial.toMap
    (F.positionMapExtended hNames P.baseInclusion
      (P.sourceSpecial.inverseMap (P.preparedTailMap q))))).val.2 = _
  rw [P.targetSpecial.inverse_apply]
  exact P.prepared_tail_inverse_labels q

theorem position_on_inverse_tail_fibre (P : UniformBalancedPositionPreparation G C F hBalanced hNames)
    (a : A)
    (u : extendBase (VerticalOffsets.keyImage (gammaRVGraphRefinement A F.parameters hNames)) P.baseInclusion)
    (hu : u.val ∈ P.sourceSpecial.inverseFibre
      (P.preparedTailMap (Map.toImage (gammaRVGraphRefinementMap A F.parameters hNames) a))) :
    vfAt (F.positionMapExtended hNames P.baseInclusion u).val 0 =
      F.localPosition a (vfAt u.val 0) ∧
    vfAt u.val 0 ∈ Cells.first (mixedPairFibre F.parameters a) := by
  have hl := (unary_inverse_fibre_labels P.sourceSpecial _ u.val hu).trans
    (P.prepared_tail_inverse_labels (Map.toImage (gammaRVGraphRefinementMap A F.parameters hNames) a))
  exact F.position_map_on_label_fibre hNames a ⟨u.val,u.property⟩ hl

theorem inverse_tail_body_in_row (P : UniformBalancedPositionPreparation G C F hBalanced hNames)
    (a : A) :
    InverseOneCells.typedBody P.sourceSpecial
      (P.preparedTailMap (Map.toImage (gammaRVGraphRefinementMap A F.parameters hNames) a)) ⊆
        Cells.first (mixedPairFibre F.parameters a) := by
  rintro x ⟨u,hu,hup⟩
  have h := (P.position_on_inverse_tail_fibre a u ⟨u,rfl,hup⟩).2
  have he : vfAt u.val 0 = x := Subtype.ext hu
  exact he ▸ h

theorem inverse_tail_body_position_image (P : UniformBalancedPositionPreparation G C F hBalanced hNames)
    (a : A) :
    F.localPosition a '' InverseOneCells.typedBody P.sourceSpecial
      (P.preparedTailMap (Map.toImage (gammaRVGraphRefinementMap A F.parameters hNames) a)) =
    InverseOneCells.typedBody P.targetSpecial (P.conjugateMap
      (P.preparedTailMap (Map.toImage (gammaRVGraphRefinementMap A F.parameters hNames) a))) :=
  prepared_unary_body_image P.sourceSpecial P.targetSpecial _
    (F.position_to_image_bijective hBalanced hNames) P.forwardContractible P.backwardContractible _
    (F.localPosition a) (fun u hu => (P.position_on_inverse_tail_fibre a u hu).1)

theorem different_prepared_row_rectangular (P : UniformBalancedPositionPreparation G C F hBalanced hNames)
    (a : A)
    (hDifferent : (Map.toImage (gammaRVGraphRefinementMap A F.parameters hNames) a).val ∈ P.differentPart) :
    let q := Map.toImage (gammaRVGraphRefinementMap A F.parameters hNames) a
    let B := InverseOneCells.typedBody P.sourceSpecial (P.preparedTailMap q)
    let E := InverseOneCells.typedBody P.targetSpecial (P.preparedHeadMap q)
    let R := mixedPairFibre F.parameters a ∩ (B ×ˢ E)
    R = Cells.first R ×ˢ Cells.second R := by
  intro q B E R
  obtain ⟨r,hBal⟩ := hBalanced a
  have hNot : ¬ SameRV (P.conjugateMap (P.preparedTailMap q)).val (P.preparedHeadMap q).val := by
    intro h
    exact hDifferent.2 ((P.matching_part_mem q).mpr h.symm)
  have hOld := (P.prepared_position_inverse_labels q).trans (P.prepared_head_inverse_labels q).symm
  exact relation_on_disjoint_image_balls_rectangle hBal.2.2.1 (P.inverse_tail_body_in_row a)
    (P.inverse_tail_body_position_image a)
    (InverseOneCells.one_cell _ P.targetPullback _)
    (InverseOneCells.one_cell _ P.targetPullback _)
    (inverse_special_bodies_disjoint P.targetSpecial _ _ hOld hNot)

end UniformBalancedPositionPreparation
end IntegrationInACVF.Section7
