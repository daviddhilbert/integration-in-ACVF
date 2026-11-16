module

public import Integration7.MatchingTranslationRectangles
public import Integration7.PreparedKeyLabelSpecialPreparations
public import Integration7.FixedContextBalancedPreparations

@[expose] public section

/-! The unchanged coordinate of each matching translation carries its
entire original prepared unary key as literal selected RV labels. These
are the source data for the recorded-key special-chain lift. -/
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

def matchingOldLabelIndex (P : UniformBalancedPositionPreparation G C F hBalanced hNames) :
    Fin (m+F.arity) → Fin ((m+F.arity)+((1+P.sourceArity)+(1+P.targetArity))) :=
  Fin.castAdd ((1+P.sourceArity)+(1+P.targetArity))

def matchingTailKeyIndex (P : UniformBalancedPositionPreparation G C F hBalanced hNames) :
    Fin (1+P.sourceArity) → Fin ((m+F.arity)+((1+P.sourceArity)+(1+P.targetArity))) :=
  Fin.natAdd (m+F.arity) ∘ Fin.castAdd (1+P.targetArity)

def matchingHeadKeyIndex (P : UniformBalancedPositionPreparation G C F hBalanced hNames) :
    Fin (1+P.targetArity) → Fin ((m+F.arity)+((1+P.sourceArity)+(1+P.targetArity))) :=
  Fin.natAdd (m+F.arity) ∘ Fin.natAdd (1+P.sourceArity)

theorem matching_forget_on_graph (P : UniformBalancedPositionPreparation G C F hBalanced hNames)
    (p : P.matchingNative) :
    P.matchingForgetMap (Map.toImage (gammaRVGraphRefinementMap P.matchingNative P.matchingKeyLabels hNames) p) =
      P.matchingSubsetMap p := by
  change P.matchingSubsetMap (Map.inverse
    (Map.toImage (gammaRVGraphRefinementMap P.matchingNative P.matchingKeyLabels hNames))
    (gamma_rv_graph_refinement_bijective P.matchingNative P.matchingKeyLabels hNames)
    (Map.toImage (gammaRVGraphRefinementMap P.matchingNative P.matchingKeyLabels hNames) p)) = _
  rw [Map.inverse_apply]

theorem matching_tail_key_record (P : UniformBalancedPositionPreparation G C F hBalanced hNames)
    (q : P.matchingPreparedFamily) :
    Fin.append (fun i : Fin 1 => rv (vfAt (P.preparedTailMap (P.matchingForgetMap q)).val i))
      (P.preparedTailMap (P.matchingForgetMap q)).val.2 = q.val.2 ∘ P.matchingTailKeyIndex := by
  obtain ⟨p,rfl⟩ := (gamma_rv_graph_refinement_bijective P.matchingNative P.matchingKeyLabels hNames).2 q
  rw [P.matching_forget_on_graph p]
  have h := gamma_rv_keys_of_map_value P.preparedTailMap P.prepared_tail_graph_gamma (P.matchingSubsetMap p)
  refine h.symm.trans ?_
  funext i
  change P.tailKeyLabels.toFun (P.matchingSubsetMap p) i =
    Fin.append p.val.2 (Fin.append (P.tailKeyLabels.toFun (P.matchingSubsetMap p))
      (P.headKeyLabels.toFun (P.matchingSubsetMap p)))
        (Fin.natAdd (m+F.arity) (Fin.castAdd (1+P.targetArity) i))
  rw [Fin.append_right,Fin.append_left]

theorem matching_head_key_record (P : UniformBalancedPositionPreparation G C F hBalanced hNames)
    (q : P.matchingPreparedFamily) :
    Fin.append (fun i : Fin 1 => rv (vfAt (P.preparedHeadMap (P.matchingForgetMap q)).val i))
      (P.preparedHeadMap (P.matchingForgetMap q)).val.2 = q.val.2 ∘ P.matchingHeadKeyIndex := by
  obtain ⟨p,rfl⟩ := (gamma_rv_graph_refinement_bijective P.matchingNative P.matchingKeyLabels hNames).2 q
  rw [P.matching_forget_on_graph p]
  have h := gamma_rv_keys_of_map_value P.preparedHeadMap P.prepared_head_graph_gamma (P.matchingSubsetMap p)
  refine h.symm.trans ?_
  funext i
  change P.headKeyLabels.toFun (P.matchingSubsetMap p) i =
    Fin.append p.val.2 (Fin.append (P.tailKeyLabels.toFun (P.matchingSubsetMap p))
      (P.headKeyLabels.toFun (P.matchingSubsetMap p)))
        (Fin.natAdd (m+F.arity) (Fin.natAdd (1+P.sourceArity) i))
  rw [Fin.append_right,Fin.append_right]

def matchingVerticalTailDomain (P : UniformBalancedPositionPreparation G C F hBalanced hNames) :=
  VerticalOffsets.keyImage P.matchingVerticalImage

def matchingHorizontalHeadDomain (P : UniformBalancedPositionPreparation G C F hBalanced hNames) :=
  Map.image (coordinateProjectMap 0 P.matchingHorizontalImage)

theorem matching_vertical_tail_preimage (P : UniformBalancedPositionPreparation G C F hBalanced hNames)
    (p : P.matchingVerticalTailDomain) :
    ∃ q : P.matchingPreparedFamily, p.val = (fun _ : Fin 1 => vfAt q.val 1,q.val.2) := by
  obtain ⟨v,hv⟩ := p.property
  obtain ⟨q,rfl⟩ := P.matching_vertical_map_bijective.2 v
  refine ⟨q,hv.symm.trans ?_⟩
  apply Prod.ext
  · funext i
    fin_cases i
    rfl
  · rfl

theorem matching_horizontal_head_preimage (P : UniformBalancedPositionPreparation G C F hBalanced hNames)
    (p : P.matchingHorizontalHeadDomain) :
    ∃ q : P.matchingPreparedFamily, p.val = (fun _ : Fin 1 => vfAt q.val 0,q.val.2) := by
  obtain ⟨v,hv⟩ := p.property
  obtain ⟨q,rfl⟩ := P.matching_horizontal_map_bijective.2 v
  exact ⟨q,hv.symm⟩

theorem matching_vertical_tail_old_mem
    (P : UniformBalancedPositionPreparation G C F hBalanced hNames) (p : P.matchingVerticalTailDomain) :
    retainVFLabels P.matchingOldLabelIndex p.val ∈ carrier
      (extendBase (VerticalOffsets.keyImage (gammaRVGraphRefinement A F.parameters hNames)) P.baseInclusion) := by
  obtain ⟨q,hq⟩ := P.matching_vertical_tail_preimage p
  have hForget := P.matching_forget_value q
  have hPoint : retainVFLabels P.matchingOldLabelIndex p.val =
      (VerticalOffsets.toKey _ (P.matchingForgetMap q)).val := by
    rw [hq]
    have hVF := congrArg (fun p : Point (M := M) 2 (m+F.arity) => vfAt p 1) hForget
    have hRV := congrArg (fun p : Point (M := M) 2 (m+F.arity) => p.2) hForget
    apply Prod.ext
    · funext i
      fin_cases i
      exact hVF.symm
    · exact hRV.symm
  exact Eq.mp (congrArg (fun p : Point (M := M) 1 (m+F.arity) =>
    p ∈ carrier (VerticalOffsets.keyImage (gammaRVGraphRefinement A F.parameters hNames))) hPoint.symm)
      (VerticalOffsets.toKey _ (P.matchingForgetMap q)).property

theorem matching_horizontal_head_old_mem
    (P : UniformBalancedPositionPreparation G C F hBalanced hNames) (p : P.matchingHorizontalHeadDomain) :
    retainVFLabels P.matchingOldLabelIndex p.val ∈ carrier (extendBase (F.positionImage hNames) P.baseInclusion) := by
  obtain ⟨q,hq⟩ := P.matching_horizontal_head_preimage p
  have hForget := P.matching_forget_value q
  have hPoint : retainVFLabels P.matchingOldLabelIndex p.val =
      (F.headToPositionImage hBalanced hNames (P.matchingForgetMap q)).val := by
    rw [hq]
    have hVF := congrArg (fun p : Point (M := M) 2 (m+F.arity) => fun _ : Fin 1 => vfAt p 0) hForget
    have hRV := congrArg (fun p : Point (M := M) 2 (m+F.arity) => p.2) hForget
    exact Prod.ext hVF.symm hRV.symm
  exact Eq.mp (congrArg (fun p : Point (M := M) 1 (m+F.arity) => p ∈ carrier (F.positionImage hNames)) hPoint.symm)
    (F.headToPositionImage hBalanced hNames (P.matchingForgetMap q)).property

end IntegrationInACVF.Section7.UniformBalancedPositionPreparation
