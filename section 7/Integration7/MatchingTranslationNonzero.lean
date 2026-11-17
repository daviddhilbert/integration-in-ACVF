module

public import Integration7.MatchingPreparedLabelFibres
public import Integration7.RectanglePreparedNonzeroFibres

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! The actual matching prepared keys and translated offsets are
nonzero. This follows from the proved open inverse cells and the two
nondegenerate paradigms of the same balanced row. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section5
open IntegrationInACVF.Section4 IntegrationInACVF.Section5 IntegrationInACVF.Section3ACVF

namespace IntegrationInACVF.Section7.UniformBalancedPositionPreparation
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {G : Base (M := M)} {m : ℕ} {C : BaseContext M}
variable {A : DefSet (M := M) (C.base : Set M) 2 m}
variable {F : UniformMixedCellPresentation G (carrier A)} {hBalanced : F.BalancedRows}
variable {hNames : commonRealNames G ⊆ (C.base : Set M)}

theorem matching_prepared_keys_nonzero
    (P : UniformBalancedPositionPreparation G C F hBalanced hNames)
    (γ : Values.Gamma (M := M)) (hγ : 1 < γ)
    (hNonzero : ∀ a : A, (F.vertical.projection a).val.2 F.vertical.paradigm_index ≠ rv (0 : VF (M := M)))
    (q : P.matchingPreparedFamily) :
    vfAt (P.preparedTailMap (P.matchingForgetMap q)).val 0 ≠ 0 ∧
      vfAt (P.preparedHeadMap (P.matchingForgetMap q)).val 0 ≠ 0 := by
  obtain ⟨a,hMatch,rfl⟩ := P.matching_point_anchor q
  rw [P.matching_forget_on_graph]
  obtain ⟨r,hB,hE,_⟩ := P.matching_prepared_row_balanced_fibres a hMatch (hNonzero a)
  exact ⟨inverse_special_open_head_nonzero C.model00 γ hγ _ _ hB,
    inverse_special_open_head_nonzero C.model00 γ hγ _ _ hE⟩

theorem matching_vertical_offset_nonzero
    (P : UniformBalancedPositionPreparation G C F hBalanced hNames)
    (hNonzero : ∀ a : A, (F.vertical.projection a).val.2 F.vertical.paradigm_index ≠ rv (0 : VF (M := M)))
    (q : P.matchingVerticalImage) : vfAt q.val 0 ≠ 0 := by
  obtain ⟨p,rfl⟩ := P.matching_vertical_map_bijective.2 q
  have ht := P.matching_vertical_head_tag p
  obtain ⟨a,hMatch,rfl⟩ := P.matching_point_anchor p
  rw [P.matching_forget_on_graph] at ht
  have hp := F.refinement_paradigm_on_graph hNames a
  intro he
  apply hNonzero a
  exact hp.symm.trans (ht.symm.trans (congrArg rv he))

theorem matching_horizontal_offset_nonzero
    (P : UniformBalancedPositionPreparation G C F hBalanced hNames)
    (hNonzero : ∀ a : A, (F.vertical.projection a).val.2 F.vertical.paradigm_index ≠ rv (0 : VF (M := M)))
    (q : P.matchingHorizontalImage) : vfAt q.val 1 ≠ 0 := by
  obtain ⟨p,rfl⟩ := P.matching_horizontal_map_bijective.2 q
  have ht := P.matching_horizontal_tail_tag p
  obtain ⟨a,hMatch,rfl⟩ := P.matching_point_anchor p
  rw [P.matching_forget_on_graph] at ht
  obtain ⟨r,hBal⟩ := hBalanced a
  have hD : vfAt a.val 1 ∈ Cells.first (mixedPairFibre F.parameters a) := by
    refine ⟨(vfAt a.val 1,vfAt a.val 0),⟨a,?_,rfl⟩,rfl⟩
    funext i
    fin_cases i <;> rfl
  have hr : r ≠ rv (0 : VF (M := M)) := fun he =>
    hNonzero a ((BalancedFibres.paradigms_degenerate_together hBal.2.2.1 _ hD).mp he)
  have hTag := F.horizontal_translation_tail_paradigm hBalanced hNames a r hBal a rfl
  intro he
  apply hr
  exact hTag.symm.trans (ht.symm.trans (congrArg rv he))

theorem matching_vertical_unary_prepared_nonzero
    (P : UniformBalancedPositionPreparation G C F hBalanced hNames)
    (γ : Values.Gamma (M := M)) (hγ : 1 < γ)
    (hNonzero : ∀ a : A, (F.vertical.projection a).val.2 F.vertical.paradigm_index ≠ rv (0 : VF (M := M)))
    (L : PreparedKeyLabelSpecialPreparation P.sourceSpecial
      (extendBase P.matchingVerticalTailDomain P.baseInclusion) P.matchingOldLabelIndex P.matchingTailKeyIndex
      (fun p hp => P.matching_vertical_tail_old_mem ⟨p,hp⟩) G)
    (q : L.target) : vfAt q.val 0 ≠ 0 := by
  apply L.head_nonzero _ q
  intro p
  obtain ⟨a,ha⟩ := P.matching_vertical_tail_preimage ⟨p.val,p.property⟩
  have hKey := (P.matching_vertical_tail_recorded_key ⟨p.val,p.property⟩).trans
    ((congrArg (fun r => r ∘ P.matchingTailKeyIndex)
      (congrArg (fun p : Point (M := M) 1
        ((m+F.arity)+((1+P.sourceArity)+(1+P.targetArity))) => p.2) ha)).trans
      (P.matching_tail_key_record a).symm)
  have hTag := congrFun hKey (Fin.castAdd P.sourceArity (0 : Fin 1))
  simp only [Fin.append_left] at hTag
  intro he
  apply (P.matching_prepared_keys_nonzero γ hγ hNonzero a).1
  apply (rv_eq_zero_iff _).mp
  exact hTag.symm.trans (congrArg rv he)

theorem matching_horizontal_unary_prepared_nonzero
    (P : UniformBalancedPositionPreparation G C F hBalanced hNames)
    (γ : Values.Gamma (M := M)) (hγ : 1 < γ)
    (hNonzero : ∀ a : A, (F.vertical.projection a).val.2 F.vertical.paradigm_index ≠ rv (0 : VF (M := M)))
    (L : PreparedKeyLabelSpecialPreparation P.targetSpecial
      (extendBase P.matchingHorizontalHeadDomain P.baseInclusion) P.matchingOldLabelIndex P.matchingHeadKeyIndex
      (fun p hp => P.matching_horizontal_head_old_mem ⟨p,hp⟩) G)
    (q : L.target) : vfAt q.val 0 ≠ 0 := by
  apply L.head_nonzero _ q
  intro p
  obtain ⟨a,ha⟩ := P.matching_horizontal_head_preimage ⟨p.val,p.property⟩
  have hKey := (P.matching_horizontal_head_recorded_key ⟨p.val,p.property⟩).trans
    ((congrArg (fun r => r ∘ P.matchingHeadKeyIndex)
      (congrArg (fun p : Point (M := M) 1
        ((m+F.arity)+((1+P.sourceArity)+(1+P.targetArity))) => p.2) ha)).trans
      (P.matching_head_key_record a).symm)
  have hTag := congrFun hKey (Fin.castAdd P.targetArity (0 : Fin 1))
  simp only [Fin.append_left] at hTag
  intro he
  apply (P.matching_prepared_keys_nonzero γ hγ hNonzero a).2
  apply (rv_eq_zero_iff _).mp
  exact hTag.symm.trans (congrArg rv he)

end IntegrationInACVF.Section7.UniformBalancedPositionPreparation
