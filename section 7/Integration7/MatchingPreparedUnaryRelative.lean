module

public import Integration7.MatchingFullPullbackPreparations

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! The full matching preparations each change just one VF coordinate.
The permutations used to construct them restore the original VF order. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section5
open IntegrationInACVF.Section5 IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7.UniformBalancedPositionPreparation
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {G : Base (M := M)} {m : ℕ} {C : BaseContext M}
variable {A : DefSet (M := M) (C.base : Set M) 2 m}
variable {F : UniformMixedCellPresentation G (carrier A)} {hBalanced : F.BalancedRows}
variable {hNames : commonRealNames G ⊆ (C.base : Set M)}

theorem matching_vertical_prepared_unary_relative
    (P : UniformBalancedPositionPreparation G C F hBalanced hNames)
    (hNonzero : ∀ a : A, (F.vertical.projection a).val.2 F.vertical.paradigm_index ≠ rv (0 : VF (M := M)))
    (L : PreparedKeyLabelSpecialPreparation P.sourceSpecial
      (extendBase P.matchingVerticalTailDomain P.baseInclusion) P.matchingOldLabelIndex P.matchingTailKeyIndex
      (fun p hp => P.matching_vertical_tail_old_mem ⟨p,hp⟩) G) :
    UnaryRelative (P.matchingVerticalPullbackPreparation hNonzero L).volumeMap 1 := by
  intro p j hj
  fin_cases j
  · rfl
  · exact (hj rfl).elim

theorem matching_horizontal_prepared_unary_relative
    (P : UniformBalancedPositionPreparation G C F hBalanced hNames)
    (hNonzero : ∀ a : A, (F.vertical.projection a).val.2 F.vertical.paradigm_index ≠ rv (0 : VF (M := M)))
    (L : PreparedKeyLabelSpecialPreparation P.targetSpecial
      (extendBase P.matchingHorizontalHeadDomain P.baseInclusion) P.matchingOldLabelIndex P.matchingHeadKeyIndex
      (fun p hp => P.matching_horizontal_head_old_mem ⟨p,hp⟩) G) :
    UnaryRelative (P.matchingHorizontalPullbackPreparation hNonzero L).volumeMap 0 := by
  intro p j hj
  fin_cases j
  · exact (hj rfl).elim
  · rfl

end IntegrationInACVF.Section7.UniformBalancedPositionPreparation
