module

public import Integration7.MatchingRecordedKeyPreparations

@[expose] public section

/-! The unchanged-coordinate projections contain whole inverse fibres
of the chosen unary preparations. Their actual recorded-key lifts are
therefore RV pullbacks, with no additional preparation hypothesis. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section5
open IntegrationInACVF.Section4 IntegrationInACVF.Section5

namespace IntegrationInACVF.Section7.UniformBalancedPositionPreparation
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {G : Base (M := M)} {m : ℕ} {C : BaseContext M}
variable {A : DefSet (M := M) (C.base : Set M) 2 m}
variable {F : UniformMixedCellPresentation G (carrier A)} {hBalanced : F.BalancedRows}
variable {hNames : commonRealNames G ⊆ (C.base : Set M)}

theorem matching_point_anchor (P : UniformBalancedPositionPreparation G C F hBalanced hNames)
    (q : P.matchingPreparedFamily) :
    ∃ a : A, ∃ hMatch : (Map.toImage (gammaRVGraphRefinementMap A F.parameters hNames) a).val ∈ P.matchingPart,
      q = Map.toImage (gammaRVGraphRefinementMap P.matchingNative P.matchingKeyLabels hNames)
        ⟨(Map.toImage (gammaRVGraphRefinementMap A F.parameters hNames) a).val,hMatch⟩ := by
  obtain ⟨p,rfl⟩ := (gamma_rv_graph_refinement_bijective P.matchingNative P.matchingKeyLabels hNames).2 q
  obtain ⟨a,ha⟩ := (gamma_rv_graph_refinement_bijective A F.parameters hNames).2 (P.matchingSubsetMap p)
  have hMatch : (Map.toImage (gammaRVGraphRefinementMap A F.parameters hNames) a).val ∈ P.matchingPart := by
    exact Eq.mp (congrArg (fun z : Point (M := M) 2 (m+F.arity) => z ∈ P.matchingPart)
      (congrArg Subtype.val ha).symm) p.property
  refine ⟨a,hMatch,?_⟩
  apply congrArg
  exact Subtype.ext (congrArg Subtype.val ha).symm

set_option maxHeartbeats 2000000 in
theorem matching_vertical_tail_complete
    (P : UniformBalancedPositionPreparation G C F hBalanced hNames)
    (hNonzero : ∀ a : A, (F.vertical.projection a).val.2 F.vertical.paradigm_index ≠ rv (0 : VF (M := M)))
    (p : extendBase P.matchingVerticalTailDomain P.baseInclusion)
    (u : extendBase (VerticalOffsets.keyImage (gammaRVGraphRefinement A F.parameters hNames)) P.baseInclusion)
    (hSame : SameRV (P.sourceSpecial.toMap u).val (P.sourceSpecial.toMap
      ⟨retainVFLabels P.matchingOldLabelIndex p.val,P.matching_vertical_tail_old_mem ⟨p.val,p.property⟩⟩).val) :
    (u.val.1,p.val.2) ∈ carrier (extendBase P.matchingVerticalTailDomain P.baseInclusion) := by
  obtain ⟨q,hp⟩ := P.matching_vertical_tail_preimage ⟨p.val,p.property⟩
  obtain ⟨a,hMatch,rfl⟩ := P.matching_point_anchor q
  let q₀ := Map.toImage (gammaRVGraphRefinementMap A F.parameters hNames) a
  let p₀ : P.matchingNative := ⟨q₀.val,hMatch⟩
  let q₁ := Map.toImage (gammaRVGraphRefinementMap P.matchingNative P.matchingKeyLabels hNames) p₀
  change p.val = (fun _ : Fin 1 => vfAt a.val 1,q₁.val.2) at hp
  let k : extendBase (VerticalOffsets.keyImage (gammaRVGraphRefinement A F.parameters hNames)) P.baseInclusion :=
    ⟨(VerticalOffsets.toKey _ q₀).val,(VerticalOffsets.toKey _ q₀).property⟩
  have hInput : (⟨retainVFLabels P.matchingOldLabelIndex p.val,
      P.matching_vertical_tail_old_mem ⟨p.val,p.property⟩⟩ :
      extendBase (VerticalOffsets.keyImage (gammaRVGraphRefinement A F.parameters hNames)) P.baseInclusion) = k := by
    apply Subtype.ext
    change retainVFLabels P.matchingOldLabelIndex p.val = k.val
    rw [hp]
    apply Prod.ext
    · funext i
      fin_cases i
      rfl
    · funext i
      exact Fin.append_left _ _ i
  have hKey : SameRV (P.sourceSpecial.toMap u).val (P.preparedTailMap q₀).val := by
    rw [hInput] at hSame
    exact hSame
  have hu : vfAt u.val 0 ∈ InverseOneCells.typedBody P.sourceSpecial (P.preparedTailMap q₀) := ⟨u,rfl,hKey⟩
  obtain ⟨r,hB,hE,hR⟩ := P.matching_prepared_family_row_geometry a hMatch (hNonzero a)
  obtain ⟨x,hx⟩ := BalancedFibres.translatedRV_nonempty
    ((F.vertical.projection a).val.2 F.vertical.paradigm_index) (F.localPosition a (vfAt u.val 0))
  have hRel := (Set.ext_iff.mp (hR.vertical (vfAt u.val 0) hu) x).mpr hx
  let w : P.matchingPreparedFamily := ⟨((pairPoint (vfAt u.val 0) x).1,q₁.val.2),hRel⟩
  let v := P.matchingVerticalMap w
  refine ⟨v,?_⟩
  apply Prod.ext
  · funext i
    fin_cases i
    rfl
  · exact (congrArg (fun p : Point (M := M) 1
      ((m+F.arity)+((1+P.sourceArity)+(1+P.targetArity))) => p.2) hp).symm

set_option maxHeartbeats 2000000 in
theorem matching_horizontal_head_complete
    (P : UniformBalancedPositionPreparation G C F hBalanced hNames)
    (hNonzero : ∀ a : A, (F.vertical.projection a).val.2 F.vertical.paradigm_index ≠ rv (0 : VF (M := M)))
    (p : extendBase P.matchingHorizontalHeadDomain P.baseInclusion)
    (u : extendBase (F.positionImage hNames) P.baseInclusion)
    (hSame : SameRV (P.targetSpecial.toMap u).val (P.targetSpecial.toMap
      ⟨retainVFLabels P.matchingOldLabelIndex p.val,P.matching_horizontal_head_old_mem ⟨p.val,p.property⟩⟩).val) :
    (u.val.1,p.val.2) ∈ carrier (extendBase P.matchingHorizontalHeadDomain P.baseInclusion) := by
  obtain ⟨q,hp⟩ := P.matching_horizontal_head_preimage ⟨p.val,p.property⟩
  obtain ⟨a,hMatch,rfl⟩ := P.matching_point_anchor q
  let q₀ := Map.toImage (gammaRVGraphRefinementMap A F.parameters hNames) a
  let p₀ : P.matchingNative := ⟨q₀.val,hMatch⟩
  let q₁ := Map.toImage (gammaRVGraphRefinementMap P.matchingNative P.matchingKeyLabels hNames) p₀
  change p.val = (fun _ : Fin 1 => vfAt a.val 0,q₁.val.2) at hp
  let k : extendBase (F.positionImage hNames) P.baseInclusion :=
    ⟨(F.headToPositionImage hBalanced hNames q₀).val,(F.headToPositionImage hBalanced hNames q₀).property⟩
  have hInput : (⟨retainVFLabels P.matchingOldLabelIndex p.val,
      P.matching_horizontal_head_old_mem ⟨p.val,p.property⟩⟩ :
      extendBase (F.positionImage hNames) P.baseInclusion) = k := by
    apply Subtype.ext
    change retainVFLabels P.matchingOldLabelIndex p.val = k.val
    rw [hp]
    apply Prod.ext
    · rfl
    · funext i
      exact Fin.append_left _ _ i
  have hKey : SameRV (P.targetSpecial.toMap u).val (P.preparedHeadMap q₀).val := by
    rw [hInput] at hSame
    exact hSame
  have hu : vfAt u.val 0 ∈ InverseOneCells.typedBody P.targetSpecial (P.preparedHeadMap q₀) := ⟨u,rfl,hKey⟩
  obtain ⟨r,hB,hE,hR⟩ := P.matching_prepared_family_row_geometry a hMatch (hNonzero a)
  obtain ⟨b,hb,hbx⟩ := hR.bijective.2.2 hu
  have hFibre := balanced_horizontal_fibre_at_inverse hR hB b (vfAt u.val 0) hb hbx
  obtain ⟨y,hy⟩ := BalancedFibres.translatedRV_nonempty r b
  have hRel := (Set.ext_iff.mp hFibre y).mpr hy
  let w : P.matchingPreparedFamily := ⟨((pairPoint y (vfAt u.val 0)).1,q₁.val.2),hRel⟩
  let v := P.matchingHorizontalMap w
  refine ⟨v,?_⟩
  apply Prod.ext
  · funext i
    fin_cases i
    rfl
  · exact (congrArg (fun p : Point (M := M) 1
      ((m+F.arity)+((1+P.sourceArity)+(1+P.targetArity))) => p.2) hp).symm

theorem matching_vertical_recorded_target_pullback
    (P : UniformBalancedPositionPreparation G C F hBalanced hNames)
    (hNonzero : ∀ a : A, (F.vertical.projection a).val.2 F.vertical.paradigm_index ≠ rv (0 : VF (M := M)))
    (L : PreparedKeyLabelSpecialPreparation P.sourceSpecial
      (extendBase P.matchingVerticalTailDomain P.baseInclusion) P.matchingOldLabelIndex P.matchingTailKeyIndex
      (fun p hp => P.matching_vertical_tail_old_mem ⟨p,hp⟩) G) : IsRVPullback (carrier L.target) :=
  L.target_pullback P.sourcePullback (P.matching_vertical_tail_complete hNonzero)

theorem matching_horizontal_recorded_target_pullback
    (P : UniformBalancedPositionPreparation G C F hBalanced hNames)
    (hNonzero : ∀ a : A, (F.vertical.projection a).val.2 F.vertical.paradigm_index ≠ rv (0 : VF (M := M)))
    (L : PreparedKeyLabelSpecialPreparation P.targetSpecial
      (extendBase P.matchingHorizontalHeadDomain P.baseInclusion) P.matchingOldLabelIndex P.matchingHeadKeyIndex
      (fun p hp => P.matching_horizontal_head_old_mem ⟨p,hp⟩) G) : IsRVPullback (carrier L.target) :=
  L.target_pullback P.targetPullback (P.matching_horizontal_head_complete hNonzero)

end IntegrationInACVF.Section7.UniformBalancedPositionPreparation
