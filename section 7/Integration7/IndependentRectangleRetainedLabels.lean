module

public import Integration7.IndependentRectangleFamilyContractions
public import Integration7.RVLabelConstraintHeadCoordinates

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! Every original rectangle label is recovered from the complete
first-factor key. These equalities do not require a constant density. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3.GammaParameters SpecialTransformations.Section5
open IntegrationInACVF.Section5 IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {G : Base (M := M)} {S : Set M} {m r b : ℕ}

theorem rectangle_head_contraction_old_labels
    (H : DefSet (M := M) S 2 m) (hRect : RectangularRVFibres (carrier H))
    {D : DefSet (M := M) S 1 r} (T : SpecialBijection (Map.image (coordinateProjectMap 0 H)) D)
    (hD : IsRVPullback (carrier D)) (p : H) (i : Fin m) :
    ((rectangleFamilyHeadPreparation H hRect T hD).contractionMap p).val.2
      (rectangleHeadOldLabelIndex T i) = p.val.2 i := by
  let P := rectangleFamilyHeadPreparation H hRect T hD
  have h := congrArg (fun z : Point (M := M) 1 (1+r) => z.2 (rectangleHeadOldLabelIndex T i))
    (headKeyMap_apply P.target (P.map p))
  have hAppend : (headKey (P.map p).val).2 (rectangleHeadOldLabelIndex T i) =
      (P.map p).val.2 (suffixIndex (specialRelative_rvArity_le P.special) i) := by
    change Fin.append (fun _ : Fin 1 => rv (vfAt (P.map p).val 0)) (P.map p).val.2
      (Fin.natAdd 1 (suffixIndex (special_chain_rvArity_le T.chain) i)) =
        (P.map p).val.2 (suffixIndex (special_chain_rvArity_le T.chain) i)
    exact Fin.append_right _ _ _
  exact h.trans (hAppend.trans (specialRelative_oldLabels P.special p i))

theorem independent_rectangle_label_in_head_parameters
    (H : DefSet (M := M) S 2 m) (hRect : RectangularRVFibres (carrier H))
    {D : DefSet (M := M) S 1 r} (T : SpecialBijection (Map.image (coordinateProjectMap 0 H)) D)
    (hD : IsRVPullback (carrier D))
    {E : DefSet (M := M) S 1 b} {W : SpecialBijection (Map.image (coordinateProjectMap 1 H)) E}
    (L : RVLabelConstraintSpecialPreparation W
      (rectangleFamilyHeadPreparation H hRect T hD).contractedSet (headImage D)
      (rectangleHeadOldLabelIndex T) G)
    (q : headImage L.target) (i : Fin m) :
    q.val.2 (suffixIndex (independentRectangleFamilyProgram H hRect T hD L).rvArity_le i) =
      q.val.2 (L.headParameters (rectangleHeadOldLabelIndex T i)) := by
  let P := rectangleFamilyHeadPreparation H hRect T hD
  let Q := independentRectangleFamilyProgram H hRect T hD L
  obtain ⟨p,hp⟩ := Q.surjective q
  subst q
  have hOld := Q.oldLabels p i
  have hKey := congrArg (fun z : Point (M := M) 0 (1+L.arity) =>
    z.2 (L.headParameters (rectangleHeadOldLabelIndex T i)))
      (headKeyMap_apply L.target (L.special.toMap (P.contractionMap p)))
  have hParam := hKey.trans (L.head_parameter_value (P.contractionMap p) (rectangleHeadOldLabelIndex T i))
  exact hOld.trans (hParam.trans (rectangle_head_contraction_old_labels H hRect T hD p i)).symm

namespace IndependentRectangleFamilyPreparations
variable {H : DefSet (M := M) S 2 m} {hRect : RectangularRVFibres (carrier H)}

theorem head_retained_label (F : IndependentRectangleFamilyPreparations G H hRect)
    (p : headImage F.headLift.target) (i : Fin m) :
    p.val.2 (suffixIndex F.headContraction.program.rvArity_le i) =
      p.val.2 (F.headLift.headParameters (rectangleHeadOldLabelIndex F.headSpecial i)) :=
  independent_rectangle_label_in_head_parameters H hRect F.headSpecial F.headPullback F.headLift p i

theorem tail_retained_label (F : IndependentRectangleFamilyPreparations G H hRect)
    (p : headImage F.tailLift.target) (i : Fin m) :
    p.val.2 (suffixIndex F.tailContraction.program.rvArity_le i) =
      p.val.2 (F.tailLift.headParameters (rectangleHeadOldLabelIndex (swappedRectangleHeadSpecial F.tailSpecial) i)) :=
  independent_rectangle_label_in_head_parameters _ (rectangular_rv_fibres_swap H hRect)
    (swappedRectangleHeadSpecial F.tailSpecial) F.tailPullback F.tailLift p i

end IndependentRectangleFamilyPreparations
end IntegrationInACVF.Section7
