module

public import Integration7.MatchingTranslationNonzero

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! Both coordinates of the actual full prepared matching targets
are nonzero. The chosen unary preparations have open inverse cells;
the other coordinate is the nonzero balanced translation offset. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section5
open IntegrationInACVF.Section4 IntegrationInACVF.Section5 IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7.UniformBalancedPositionPreparation
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {G : Base (M := M)} {m : ℕ} {C : BaseContext M}
variable {A : DefSet (M := M) (C.base : Set M) 2 m}
variable {F : UniformMixedCellPresentation G (carrier A)} {hBalanced : F.BalancedRows}
variable {hNames : commonRealNames G ⊆ (C.base : Set M)}

set_option maxHeartbeats 2000000 in
theorem matching_vertical_prepared_nonzero
    (P : UniformBalancedPositionPreparation G C F hBalanced hNames)
    (γ : Values.Gamma (M := M)) (hγ : 1 < γ)
    (hNonzero : ∀ a : A, (F.vertical.projection a).val.2 F.vertical.paradigm_index ≠ rv (0 : VF (M := M)))
    (L : PreparedKeyLabelSpecialPreparation P.sourceSpecial
      (extendBase P.matchingVerticalTailDomain P.baseInclusion) P.matchingOldLabelIndex P.matchingTailKeyIndex
      (fun p hp => P.matching_vertical_tail_old_mem ⟨p,hp⟩) G)
    (p : (P.matchingVerticalPullbackPreparation hNonzero L).volumeTarget) (i : Fin 2) :
    vfAt p.val i ≠ 0 := by
  let V := extendBase P.matchingVerticalImage P.baseInclusion
  let X := vfPermutationImage V (Equiv.swap 0 1)
  have hProjection : Map.image (coordinateProjectMap 0 X) =
      extendBase P.matchingVerticalTailDomain P.baseInclusion := by
    refine (swapped_rectangle_head_projection V).trans ((native_tail_key_image_eq_projection V).symm.trans ?_)
    exact defSet_eq_of_carrier_eq rfl
  let T := specialCastBoth L.special hProjection.symm rfl
  have hLT := P.matching_vertical_recorded_target_pullback hNonzero L
  have hRectV : RectangularRVFibres (carrier V) := P.matching_vertical_image_rectangular hNonzero
  have hRectX := rectangular_rv_fibres_swap V hRectV
  have hTail : ∀ q : X, vfAt q.val 1 ≠ 0 := by
    intro q
    obtain ⟨a,ha⟩ := q.property
    have he := congrArg (fun p : Point (M := M) 2
      ((m+F.arity)+((1+P.sourceArity)+(1+P.targetArity))) => vfAt p 1) ha
    exact he ▸ P.matching_vertical_offset_nonzero hNonzero a
  have hAll := rectangle_family_prepared_nonzero X hRectX T hLT
    (P.matching_vertical_unary_prepared_nonzero γ hγ hNonzero L) hTail
  exact nonzero_vf_permutation _ (Equiv.swap 0 1) hAll p i

set_option maxHeartbeats 2000000 in
theorem matching_horizontal_prepared_nonzero
    (P : UniformBalancedPositionPreparation G C F hBalanced hNames)
    (γ : Values.Gamma (M := M)) (hγ : 1 < γ)
    (hNonzero : ∀ a : A, (F.vertical.projection a).val.2 F.vertical.paradigm_index ≠ rv (0 : VF (M := M)))
    (L : PreparedKeyLabelSpecialPreparation P.targetSpecial
      (extendBase P.matchingHorizontalHeadDomain P.baseInclusion) P.matchingOldLabelIndex P.matchingHeadKeyIndex
      (fun p hp => P.matching_horizontal_head_old_mem ⟨p,hp⟩) G)
    (p : (P.matchingHorizontalPullbackPreparation hNonzero L).volumeTarget) (i : Fin 2) :
    vfAt p.val i ≠ 0 := by
  let H := extendBase P.matchingHorizontalImage P.baseInclusion
  have hProjection : Map.image (coordinateProjectMap 0 H) =
      extendBase P.matchingHorizontalHeadDomain P.baseInclusion := defSet_eq_of_carrier_eq rfl
  let T := specialCastBoth L.special hProjection.symm rfl
  have hLT := P.matching_horizontal_recorded_target_pullback hNonzero L
  have hRect : RectangularRVFibres (carrier H) := P.matching_horizontal_image_rectangular hNonzero
  have hAll := rectangle_family_prepared_nonzero H hRect T hLT
    (P.matching_horizontal_unary_prepared_nonzero γ hγ hNonzero L)
    (P.matching_horizontal_offset_nonzero hNonzero)
  have hOnce := nonzero_vf_permutation _ (Equiv.swap 0 1) hAll
  exact nonzero_vf_permutation _ (Equiv.swap 0 1) hOnce p i

end IntegrationInACVF.Section7.UniformBalancedPositionPreparation
