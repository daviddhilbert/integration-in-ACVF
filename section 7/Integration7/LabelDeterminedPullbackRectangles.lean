module

public import Integration7.MatchingPreparedLabelFibres

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! A full VF-two pullback whose shared labels determine RV fibres
is a rectangle over each full RV label tuple. This permits the proved
rectangle comparison to choose either contraction order. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section5
open IntegrationInACVF.Section5 IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

theorem label_determined_pullback_rectangular {S : Set M} {m d : ℕ}
    (H : DefSet (M := M) S 2 m) (hH : IsRVPullback (carrier H)) (ρ : Fin d → Fin m)
    (hDet : ∀ p q : H, p.val.2 ∘ ρ = q.val.2 ∘ ρ → SameRV p.val q.val) :
    RectangularRVFibres (carrier H) := by
  apply rectangular_rv_fibres_of_mix
  intro p q he
  have hSame := (sameRV_iff _ _).mp (hDet p q (congrArg (fun r => r ∘ ρ) he))
  apply (isRVPullback_iff _).mp hH p.val p.property
    (![vfAt p.val 0,vfAt q.val 1],p.val.2)
  apply (sameRV_iff _ _).mpr
  refine ⟨?_,rfl⟩
  intro i
  fin_cases i
  · rfl
  · exact hSame.1 1

namespace UniformBalancedPositionPreparation
variable {G : Base (M := M)} {m : ℕ} {C : BaseContext M}
variable {A : DefSet (M := M) (C.base : Set M) 2 m}
variable {F : UniformMixedCellPresentation G (carrier A)} {hBalanced : F.BalancedRows}
variable {hNames : commonRealNames G ⊆ (C.base : Set M)}

theorem matching_vertical_prepared_rectangular
    (P : UniformBalancedPositionPreparation G C F hBalanced hNames)
    (hNonzero : ∀ a : A, (F.vertical.projection a).val.2 F.vertical.paradigm_index ≠ rv (0 : VF (M := M)))
    (L : PreparedKeyLabelSpecialPreparation P.sourceSpecial
      (extendBase P.matchingVerticalTailDomain P.baseInclusion) P.matchingOldLabelIndex P.matchingTailKeyIndex
      (fun p hp => P.matching_vertical_tail_old_mem ⟨p,hp⟩) G) :
    RectangularRVFibres (carrier (P.matchingVerticalPullbackPreparation hNonzero L).volumeTarget) :=
  label_determined_pullback_rectangular _
    (P.matchingVerticalPullbackPreparation hNonzero L).volume_target_pullback _
    (P.matching_vertical_prepared_labels_determine hNonzero L)

theorem matching_horizontal_prepared_rectangular
    (P : UniformBalancedPositionPreparation G C F hBalanced hNames)
    (hNonzero : ∀ a : A, (F.vertical.projection a).val.2 F.vertical.paradigm_index ≠ rv (0 : VF (M := M)))
    (L : PreparedKeyLabelSpecialPreparation P.targetSpecial
      (extendBase P.matchingHorizontalHeadDomain P.baseInclusion) P.matchingOldLabelIndex P.matchingHeadKeyIndex
      (fun p hp => P.matching_horizontal_head_old_mem ⟨p,hp⟩) G) :
    RectangularRVFibres (carrier (P.matchingHorizontalPullbackPreparation hNonzero L).volumeTarget) :=
  label_determined_pullback_rectangular _
    (P.matchingHorizontalPullbackPreparation hNonzero L).volume_target_pullback _
    (P.matching_horizontal_prepared_labels_determine hNonzero L)

end UniformBalancedPositionPreparation
end IntegrationInACVF.Section7
