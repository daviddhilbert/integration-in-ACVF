module

public import Integration7.UniformPreparedBallRows

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! Exact fibres of the two prepared-key labels on the original graph.
Each fibre is the original row restricted to its two inverse-special
balls. The different-key part consequently has rectangular fibres. -/
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

theorem prepared_tail_same_iff_body (P : UniformBalancedPositionPreparation G C F hBalanced hNames)
    (p q : gammaRVGraphRefinement A F.parameters hNames) (hRV : q.val.2 = p.val.2) :
    SameRV (P.preparedTailMap q).val (P.preparedTailMap p).val ↔
      vfAt q.val 1 ∈ InverseOneCells.typedBody P.sourceSpecial (P.preparedTailMap p) := by
  let v : extendBase (VerticalOffsets.keyImage (gammaRVGraphRefinement A F.parameters hNames)) P.baseInclusion :=
    ⟨(VerticalOffsets.toKey _ q).val,(VerticalOffsets.toKey _ q).property⟩
  constructor
  · intro h
    exact ⟨v,rfl,h⟩
  · rintro ⟨u,hu,he⟩
    have hl := (unary_inverse_fibre_labels P.sourceSpecial _ u.val ⟨u,rfl,he⟩).trans
      ((P.prepared_tail_inverse_labels p).trans hRV.symm)
    have huv : u = v := by
      apply Subtype.ext
      refine Prod.ext ?_ hl
      funext i
      have hi : i = 0 := Subsingleton.elim _ _
      subst i
      exact Subtype.ext hu
    rw [huv] at he
    exact he

theorem prepared_head_same_iff_body (P : UniformBalancedPositionPreparation G C F hBalanced hNames)
    (p q : gammaRVGraphRefinement A F.parameters hNames) (hRV : q.val.2 = p.val.2) :
    SameRV (P.preparedHeadMap q).val (P.preparedHeadMap p).val ↔
      vfAt q.val 0 ∈ InverseOneCells.typedBody P.targetSpecial (P.preparedHeadMap p) := by
  let v : extendBase (F.positionImage hNames) P.baseInclusion :=
    ⟨(F.headToPositionImage hBalanced hNames q).val,(F.headToPositionImage hBalanced hNames q).property⟩
  constructor
  · intro h
    exact ⟨v,rfl,h⟩
  · rintro ⟨u,hu,he⟩
    have hl := (unary_inverse_fibre_labels P.targetSpecial _ u.val ⟨u,rfl,he⟩).trans
      ((P.prepared_head_inverse_labels p).trans hRV.symm)
    have huv : u = v := by
      apply Subtype.ext
      refine Prod.ext ?_ hl
      funext i
      have hi : i = 0 := Subsingleton.elim _ _
      subst i
      exact Subtype.ext hu
    rw [huv] at he
    exact he

theorem pair_key_labels_iff_bodies (P : UniformBalancedPositionPreparation G C F hBalanced hNames)
    (p q : gammaRVGraphRefinement A F.parameters hNames) :
    P.pairKeyLabels.toFun q = P.pairKeyLabels.toFun p ↔
      q.val.2 = p.val.2 ∧
      vfAt q.val 1 ∈ InverseOneCells.typedBody P.sourceSpecial (P.preparedTailMap p) ∧
      vfAt q.val 0 ∈ InverseOneCells.typedBody P.targetSpecial (P.preparedHeadMap p) := by
  constructor
  · intro he
    obtain ⟨hT,hH⟩ := P.pair_key_labels_same q p he
    have hOld := ((sameRV_iff _ _).mp
      (P.sourceSpecial.inverse_contractible _ _ hT)).2
    have hRV := (P.prepared_tail_inverse_labels q).symm.trans
      (hOld.trans (P.prepared_tail_inverse_labels p))
    exact ⟨hRV,(P.prepared_tail_same_iff_body p q hRV).mp hT,
      (P.prepared_head_same_iff_body p q hRV).mp hH⟩
  · rintro ⟨hRV,hT,hH⟩
    have hT' := (flattened_key_eq_iff_same_rv _ _).mpr ((P.prepared_tail_same_iff_body p q hRV).mpr hT)
    have hH' := (flattened_key_eq_iff_same_rv _ _).mpr ((P.prepared_head_same_iff_body p q hRV).mpr hH)
    exact congrArg₂ Fin.append hT' hH'

set_option maxHeartbeats 1500000 in
theorem pair_key_fibre (P : UniformBalancedPositionPreparation G C F hBalanced hNames) (a : A) :
    let p := Map.toImage (gammaRVGraphRefinementMap A F.parameters hNames) a
    mixedPairFibre P.pairKeyLabels p = mixedPairFibre F.parameters a ∩
      (InverseOneCells.typedBody P.sourceSpecial (P.preparedTailMap p) ×ˢ
       InverseOneCells.typedBody P.targetSpecial (P.preparedHeadMap p)) := by
  intro p
  ext z
  constructor
  · rintro ⟨q,hVF,hKey⟩
    obtain ⟨hRV,hB,hE⟩ := (P.pair_key_labels_iff_bodies p q).mp hKey
    obtain ⟨b,rfl⟩ := (gamma_rv_graph_refinement_bijective A F.parameters hNames).2 q
    have hP : F.parameters.toFun b = F.parameters.toFun a := by
      funext i
      have hi := congrFun hRV (Fin.natAdd m i)
      change Fin.append b.val.2 (F.parameters.toFun b) (Fin.natAdd m i) =
        Fin.append a.val.2 (F.parameters.toFun a) (Fin.natAdd m i) at hi
      simpa only [Fin.append_right] using hi
    refine ⟨⟨b,hVF,hP⟩,?_,?_⟩
    · have he : vfAt b.val 1 = z.1 := congrFun hVF 1
      exact he ▸ hB
    · have he : vfAt b.val 0 = z.2 := congrFun hVF 0
      exact he ▸ hE
  · rintro ⟨⟨b,hVF,hP⟩,hB,hE⟩
    let q := Map.toImage (gammaRVGraphRefinementMap A F.parameters hNames) b
    have hOld := ((sameRV_iff _ _).mp (F.parameters_reflect_same_rv b a hP)).2
    have hRV : q.val.2 = p.val.2 := congrArg₂ Fin.append hOld hP
    refine ⟨q,hVF,(P.pair_key_labels_iff_bodies p q).mpr ⟨hRV,?_,?_⟩⟩
    · have he : vfAt b.val 1 = z.1 := congrFun hVF 1
      exact he.symm ▸ hB
    · have he : vfAt b.val 0 = z.2 := congrFun hVF 0
      exact he.symm ▸ hE

def differentKeyLabels (P : UniformBalancedPositionPreparation G C F hBalanced hNames) :
    GammaRVMap G P.differentPart ((1+P.sourceArity)+(1+P.targetArity)) :=
  P.pairKeyLabels.restrict P.differentPart Set.sdiff_subset P.different_part_gamma

theorem different_key_fibre_eq (P : UniformBalancedPositionPreparation G C F hBalanced hNames)
    (p : P.differentPart) :
    mixedPairFibre P.differentKeyLabels p = mixedPairFibre P.pairKeyLabels ⟨p.val,p.property.1⟩ := by
  ext z
  constructor
  · rintro ⟨q,hVF,hKey⟩
    exact ⟨⟨q.val,q.property.1⟩,hVF,hKey⟩
  · rintro ⟨q,hVF,hKey⟩
    have hNot : q.val ∉ P.matchingPart := by
      intro h
      exact p.property.2 ((P.matching_constant_on_pair_keys q ⟨p.val,p.property.1⟩ hKey).mp h)
    exact ⟨⟨q.val,q.property,hNot⟩,hVF,hKey⟩

theorem different_key_fibre_rectangular (P : UniformBalancedPositionPreparation G C F hBalanced hNames)
    (p : P.differentPart) :
    mixedPairFibre P.differentKeyLabels p =
      Cells.first (mixedPairFibre P.differentKeyLabels p) ×ˢ
        Cells.second (mixedPairFibre P.differentKeyLabels p) := by
  obtain ⟨a,ha⟩ := (gamma_rv_graph_refinement_bijective A F.parameters hNames).2 ⟨p.val,p.property.1⟩
  rw [P.different_key_fibre_eq p]
  have he : (⟨p.val,p.property.1⟩ : gammaRVGraphRefinement A F.parameters hNames) =
      Map.toImage (gammaRVGraphRefinementMap A F.parameters hNames) a := ha.symm
  rw [he,P.pair_key_fibre a]
  exact P.different_prepared_row_rectangular a (by
    exact Eq.mp (congrArg (fun q : gammaRVGraphRefinement A F.parameters hNames => q.val ∈ P.differentPart) ha.symm)
      p.property)

end IntegrationInACVF.Section7.UniformBalancedPositionPreparation
