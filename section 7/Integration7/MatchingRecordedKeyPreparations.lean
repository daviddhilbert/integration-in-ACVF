module

public import Integration7.MatchingPreparedProjectionKeys

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! Actual Gamma special-chain lifts on the two unchanged labelled
unary projections of the matching translations. Each records the full
chosen unary prepared key and retains every carried family label. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section5
open IntegrationInACVF.Section4 IntegrationInACVF.Section5

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {G : Base (M := M)}

theorem gamma_native_map_image {S : Set M} {n a u b : ℕ}
    {A : DefSet (M := M) S n a} {B : DefSet (M := M) S u b}
    (f : Map A B) (hf : GammaGraphDefinable G (pointMapGraph f)) :
    GammaSetDefinable G (carrier (Map.image f)) := by
  have h := (gammaLogicInput G).image_graph hf
  convert h using 1
  ext q
  constructor
  · rintro ⟨a,ha⟩
    exact ⟨a.val,a,rfl,ha⟩
  · rintro ⟨p,a,rfl,ha⟩
    exact ⟨a,ha⟩

namespace UniformBalancedPositionPreparation
variable {m : ℕ} {C : BaseContext M} {A : DefSet (M := M) (C.base : Set M) 2 m}
variable {F : UniformMixedCellPresentation G (carrier A)} {hBalanced : F.BalancedRows}
variable {hNames : commonRealNames G ⊆ (C.base : Set M)}

theorem matching_vertical_tail_domain_gamma
    (P : UniformBalancedPositionPreparation G C F hBalanced hNames) :
    GammaSetDefinable G (carrier P.matchingVerticalTailDomain) :=
  gamma_native_map_image _ (gamma_native_tail_key_graph _ P.matching_vertical_image_gamma)

theorem matching_horizontal_head_domain_gamma
    (P : UniformBalancedPositionPreparation G C F hBalanced hNames) :
    GammaSetDefinable G (carrier P.matchingHorizontalHeadDomain) :=
  gamma_native_head_projection _ P.matching_horizontal_image_gamma

theorem matching_vertical_tail_recorded_key
    (P : UniformBalancedPositionPreparation G C F hBalanced hNames) (p : P.matchingVerticalTailDomain) :
    Fin.append (fun i : Fin 1 => rv (vfAt (P.sourceSpecial.toMap
      ⟨retainVFLabels P.matchingOldLabelIndex p.val,P.matching_vertical_tail_old_mem p⟩).val i))
      (P.sourceSpecial.toMap
        ⟨retainVFLabels P.matchingOldLabelIndex p.val,P.matching_vertical_tail_old_mem p⟩).val.2 =
      p.val.2 ∘ P.matchingTailKeyIndex := by
  obtain ⟨q,hq⟩ := P.matching_vertical_tail_preimage p
  let u : extendBase (VerticalOffsets.keyImage (gammaRVGraphRefinement A F.parameters hNames)) P.baseInclusion :=
    ⟨(VerticalOffsets.toKey _ (P.matchingForgetMap q)).val,(VerticalOffsets.toKey _ (P.matchingForgetMap q)).property⟩
  have hInput : (⟨retainVFLabels P.matchingOldLabelIndex p.val,P.matching_vertical_tail_old_mem p⟩ :
      extendBase (VerticalOffsets.keyImage (gammaRVGraphRefinement A F.parameters hNames)) P.baseInclusion) = u := by
    apply Subtype.ext
    change retainVFLabels P.matchingOldLabelIndex p.val = u.val
    rw [hq]
    have hForget := P.matching_forget_value q
    have hVF := congrArg (fun p : Point (M := M) 2 (m+F.arity) => vfAt p 1) hForget
    have hRV := congrArg (fun p : Point (M := M) 2 (m+F.arity) => p.2) hForget
    apply Prod.ext
    · funext i
      fin_cases i
      exact hVF.symm
    · exact hRV.symm
  rw [hInput]
  have hRecord := P.matching_tail_key_record q
  have hLabels := congrArg (fun p : Point (M := M) 1
    ((m+F.arity)+((1+P.sourceArity)+(1+P.targetArity))) => p.2) hq
  exact hRecord.trans (congrArg (fun t => t ∘ P.matchingTailKeyIndex) hLabels.symm)

theorem matching_horizontal_head_recorded_key
    (P : UniformBalancedPositionPreparation G C F hBalanced hNames) (p : P.matchingHorizontalHeadDomain) :
    Fin.append (fun i : Fin 1 => rv (vfAt (P.targetSpecial.toMap
      ⟨retainVFLabels P.matchingOldLabelIndex p.val,P.matching_horizontal_head_old_mem p⟩).val i))
      (P.targetSpecial.toMap
        ⟨retainVFLabels P.matchingOldLabelIndex p.val,P.matching_horizontal_head_old_mem p⟩).val.2 =
      p.val.2 ∘ P.matchingHeadKeyIndex := by
  obtain ⟨q,hq⟩ := P.matching_horizontal_head_preimage p
  let u : extendBase (F.positionImage hNames) P.baseInclusion :=
    ⟨(F.headToPositionImage hBalanced hNames (P.matchingForgetMap q)).val,
      (F.headToPositionImage hBalanced hNames (P.matchingForgetMap q)).property⟩
  have hInput : (⟨retainVFLabels P.matchingOldLabelIndex p.val,P.matching_horizontal_head_old_mem p⟩ :
      extendBase (F.positionImage hNames) P.baseInclusion) = u := by
    apply Subtype.ext
    change retainVFLabels P.matchingOldLabelIndex p.val = u.val
    rw [hq]
    have hForget := P.matching_forget_value q
    have hVF := congrArg (fun p : Point (M := M) 2 (m+F.arity) => fun _ : Fin 1 => vfAt p 0) hForget
    have hRV := congrArg (fun p : Point (M := M) 2 (m+F.arity) => p.2) hForget
    exact Prod.ext hVF.symm hRV.symm
  rw [hInput]
  have hRecord := P.matching_head_key_record q
  have hLabels := congrArg (fun p : Point (M := M) 1
    ((m+F.arity)+((1+P.sourceArity)+(1+P.targetArity))) => p.2) hq
  exact hRecord.trans (congrArg (fun t => t ∘ P.matchingHeadKeyIndex) hLabels.symm)

theorem matching_vertical_recorded_preparation_exists
    (P : UniformBalancedPositionPreparation G C F hBalanced hNames) :
    Nonempty (PreparedKeyLabelSpecialPreparation P.sourceSpecial
      (extendBase P.matchingVerticalTailDomain P.baseInclusion)
      P.matchingOldLabelIndex P.matchingTailKeyIndex
      (fun p hp => P.matching_vertical_tail_old_mem ⟨p,hp⟩) G) :=
  prepared_key_label_special_preparation_exists P.sourceSpecial P.sourceGamma _
    P.matching_vertical_tail_domain_gamma _ _ _ P.matching_vertical_tail_recorded_key

theorem matching_horizontal_recorded_preparation_exists
    (P : UniformBalancedPositionPreparation G C F hBalanced hNames) :
    Nonempty (PreparedKeyLabelSpecialPreparation P.targetSpecial
      (extendBase P.matchingHorizontalHeadDomain P.baseInclusion)
      P.matchingOldLabelIndex P.matchingHeadKeyIndex
      (fun p hp => P.matching_horizontal_head_old_mem ⟨p,hp⟩) G) :=
  prepared_key_label_special_preparation_exists P.targetSpecial P.targetGamma _
    P.matching_horizontal_head_domain_gamma _ _ _ P.matching_horizontal_head_recorded_key

end UniformBalancedPositionPreparation
end IntegrationInACVF.Section7
