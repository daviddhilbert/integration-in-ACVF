module

public import Integration7.UniformPreparedKeyFibres
public import Integration7.MatchedBalancedBallRestrictions

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! The matching-key part retains complete balanced fibres on the two
actual inverse-special balls. Special preparations preserve its centred
VF differences exactly, including the residue information. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section5
open IntegrationInACVF.Section4 IntegrationInACVF.Section5
open IntegrationInACVF.Section3ACVF

namespace IntegrationInACVF.Section7.UniformBalancedPositionPreparation
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {G : Base (M := M)} {m : ℕ} {C : BaseContext M}
variable {A : DefSet (M := M) (C.base : Set M) 2 m}
variable {F : UniformMixedCellPresentation G (carrier A)} {hBalanced : F.BalancedRows}
variable {hNames : commonRealNames G ⊆ (C.base : Set M)}

theorem matching_prepared_row_balanced_fibres
    (P : UniformBalancedPositionPreparation G C F hBalanced hNames) (a : A)
    (hMatch : (Map.toImage (gammaRVGraphRefinementMap A F.parameters hNames) a).val ∈ P.matchingPart)
    (ht : (F.vertical.projection a).val.2 F.vertical.paradigm_index ≠ rv (0 : VF (M := M))) :
    let q := Map.toImage (gammaRVGraphRefinementMap A F.parameters hNames) a
    let B := InverseOneCells.typedBody P.sourceSpecial (P.preparedTailMap q)
    let E := InverseOneCells.typedBody P.targetSpecial (P.preparedHeadMap q)
    let R := mixedPairFibre F.parameters a ∩ (B ×ˢ E)
    ∃ r : RV (M := M), PaperBalls.IsOpenBall (Cells.rawSet B) ∧
      PaperBalls.IsOpenBall (Cells.rawSet E) ∧
      BalancedFibres.HasBalancedFibres B E R (F.localPosition a) r
        ((F.vertical.projection a).val.2 F.vertical.paradigm_index) := by
  intro q B E R
  obtain ⟨r,hBal⟩ := hBalanced a
  have hSame := (P.matching_part_mem q).mp hMatch
  have hBodies : InverseOneCells.typedBody P.targetSpecial (P.conjugateMap (P.preparedTailMap q)) = E := by
    ext x
    exact Set.ext_iff.mp (InverseBodies.body_sameRV P.targetSpecial _ _ hSame.symm) x.val
  have hImage := (P.inverse_tail_body_position_image a).trans hBodies
  have hOwn : (vfAt a.val 1,vfAt a.val 0) ∈ mixedPairFibre F.parameters a := by
    refine ⟨a,?_,rfl⟩
    funext i
    fin_cases i <;> rfl
  have hBody := ((P.pair_key_labels_iff_bodies q q).mp rfl).2
  exact ⟨r,balanced_fibres_restrict_matching_one_cells hBal.2.2.1
    (P.inverse_tail_body_in_row a) hImage
    (InverseOneCells.one_cell _ P.sourcePullback _) (InverseOneCells.one_cell _ P.targetPullback _)
    ht ⟨(vfAt a.val 1,vfAt a.val 0),hOwn,hBody⟩⟩

theorem matching_vertical_prepared_difference
    (P : UniformBalancedPositionPreparation G C F hBalanced hNames)
    (q : gammaRVGraphRefinement A F.parameters hNames) (hMatch : q.val ∈ P.matchingPart) :
    vfAt (P.preparedHeadMap q).val 0 - vfAt (P.conjugateMap (P.preparedTailMap q)).val 0 =
      vfAt q.val 0 - vfAt (F.positionMapExtended hNames P.baseInclusion
        (P.sourceSpecial.inverseMap (P.preparedTailMap q))).val 0 := by
  let x := P.targetSpecial.inverseMap (P.preparedHeadMap q)
  let y := F.positionMapExtended hNames P.baseInclusion (P.sourceSpecial.inverseMap (P.preparedTailMap q))
  have hX : P.targetSpecial.toMap x = P.preparedHeadMap q := P.targetSpecial.apply_inverse _
  have hY : P.targetSpecial.toMap y = P.conjugateMap (P.preparedTailMap q) := rfl
  have hl : (P.targetSpecial.toMap x).val.2 = (P.targetSpecial.toMap y).val.2 := by
    rw [hX,hY]
    exact ((sameRV_iff _ _).mp ((P.matching_part_mem q).mp hMatch)).2
  have h := P.targetSpecial.chain.unary_sub x y hl
  change vfAt (P.targetSpecial.toMap x).val 0 - vfAt (P.targetSpecial.toMap y).val 0 =
    vfAt x.val 0 - vfAt y.val 0 at h
  rw [hX,hY] at h
  have hx : vfAt x.val 0 = vfAt q.val 0 := by
    change vfAt (P.targetSpecial.inverseMap (P.targetSpecial.toMap _)).val 0 = _
    rw [P.targetSpecial.inverse_apply]
    rfl
  exact h.trans (congrArg (fun z => z-vfAt y.val 0) hx)

def matchingKeyLabels (P : UniformBalancedPositionPreparation G C F hBalanced hNames) :
    GammaRVMap G P.matchingPart ((1+P.sourceArity)+(1+P.targetArity)) :=
  P.pairKeyLabels.restrict P.matchingPart
    (by rintro p ⟨a,ha,_⟩; exact ha ▸ a.property) P.matching_part_gamma

theorem matching_key_fibre_eq (P : UniformBalancedPositionPreparation G C F hBalanced hNames)
    (p : P.matchingPart) :
    mixedPairFibre P.matchingKeyLabels p = mixedPairFibre P.pairKeyLabels
      ⟨p.val,by obtain ⟨a,ha,_⟩ := p.property; exact ha ▸ a.property⟩ := by
  let p₀ : gammaRVGraphRefinement A F.parameters hNames :=
    ⟨p.val,by obtain ⟨a,ha,_⟩ := p.property; exact ha ▸ a.property⟩
  ext z
  constructor
  · rintro ⟨q,hVF,hKey⟩
    exact ⟨⟨q.val,by obtain ⟨a,ha,_⟩ := q.property; exact ha ▸ a.property⟩,hVF,hKey⟩
  · rintro ⟨q,hVF,hKey⟩
    have hMatch : q.val ∈ P.matchingPart :=
      (P.matching_constant_on_pair_keys q p₀ hKey).mpr p.property
    exact ⟨⟨q.val,hMatch⟩,hVF,hKey⟩

end IntegrationInACVF.Section7.UniformBalancedPositionPreparation
