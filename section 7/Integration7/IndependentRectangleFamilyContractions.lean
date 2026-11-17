module

public import Integration7.IndependentRectangleFamilyPreparations
public import Integration7.RVClassProductContractionValues

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! The independently prepared rectangle family has actual standard
contractions in both orders and the expected two VF-volume selectors. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.DefinableGeometry.Space.prod
  SpecialTransformations.Section4.realSpace SpecialTransformations.Milestone0.sortEval
  SpecialTransformations.Section4.vfSpace SpecialTransformations.Section4.rvSpace
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section5
open IntegrationInACVF.Section5 IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7.IndependentRectangleFamilyPreparations
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {G : Base (M := M)} {S : Set M} {m : ℕ}
variable {H : DefSet (M := M) S 2 m} {hRect : RectangularRVFibres (carrier H)}

def headContraction (F : IndependentRectangleFamilyPreparations G H hRect) : StandardContraction H (Equiv.refl _) :=
  independentRectangleFamilyContraction H hRect F.headSpecial F.headPullback F.headLift

def tailContraction (F : IndependentRectangleFamilyPreparations G H hRect) : StandardContraction H (Equiv.swap 0 1) :=
  standardFromProgram H (Equiv.swap 0 1)
    (independentRectangleFamilyProgram (vfPermutationImage H (Equiv.swap 0 1))
      (rectangular_rv_fibres_swap H hRect) (swappedRectangleHeadSpecial F.tailSpecial) F.tailPullback F.tailLift) rfl

theorem head_contraction_gamma (F : IndependentRectangleFamilyPreparations G H hRect)
    (hH : GammaSetDefinable G (carrier H)) : GammaProgramDefinable G F.headContraction.program :=
  gamma_independent_rectangle_family_contraction H hH hRect F.headSpecial F.headGamma F.headPullback F.headLift

theorem tail_contraction_gamma (F : IndependentRectangleFamilyPreparations G H hRect)
    (hH : GammaSetDefinable G (carrier H)) : GammaProgramDefinable G F.tailContraction.program :=
  gamma_standardFromProgram _ _ _ _ (gamma_independent_rectangle_family_program _
    (gamma_vfPermutationImage H hH (Equiv.swap 0 1)) (rectangular_rv_fibres_swap H hRect)
    (swappedRectangleHeadSpecial F.tailSpecial) (gamma_special_cast_both F.tailSpecial _ _ F.tailGamma)
    F.tailPullback F.tailLift)

theorem head_volume_first (F : IndependentRectangleFamilyPreparations G H hRect)
    (q : headImage F.headLift.target) :
    q.val.2 (F.headContraction.volumeIndex 0) = q.val.2 (F.headLift.headParameters 0) := by
  have hi : F.headContraction.volumeIndex =
      (independentRectangleFamilyProgram H hRect F.headSpecial F.headPullback F.headLift).volumeIndex :=
    orderedCastSource_volumeIndex _ _
  rw [hi]
  obtain ⟨p,hp⟩ := F.headLift.program.surjective q
  subst q
  change (F.headLift.program.toMap p).val.2
    (suffixIndex F.headLift.program.rvArity_le 0) =
      (F.headLift.program.toMap p).val.2 (Fin.natAdd 1 (F.headLift.carried 0))
  rw [F.headLift.program.oldLabels]
  change p.val.2 0 = (headKeyMap F.headLift.target (F.headLift.special.toMap p)).val.2
    (Fin.natAdd 1 (F.headLift.carried 0))
  rw [headKeyMap_apply]
  simpa only [headKey,Fin.append_right,Function.comp_apply] using (congrFun (F.headLift.parameters p) 0).symm

theorem head_volume_second (F : IndependentRectangleFamilyPreparations G H hRect) :
    F.headContraction.volumeIndex 1 = (0 : Fin (1+F.headLift.arity)) := by
  have hi : F.headContraction.volumeIndex =
      (independentRectangleFamilyProgram H hRect F.headSpecial F.headPullback F.headLift).volumeIndex :=
    orderedCastSource_volumeIndex _ _
  rw [hi]
  apply Fin.ext
  change (1+F.headLift.arity)-(1+F.headLift.arity)+0=0
  omega

theorem tail_volume_first (F : IndependentRectangleFamilyPreparations G H hRect) :
    F.tailContraction.volumeIndex 0 = (0 : Fin (1+F.tailLift.arity)) := by
  apply Fin.ext
  change (1+F.tailLift.arity)-(1+F.tailLift.arity)+0=0
  omega

theorem tail_volume_second (F : IndependentRectangleFamilyPreparations G H hRect)
    (q : headImage F.tailLift.target) :
    q.val.2 (F.tailContraction.volumeIndex 1) = q.val.2 (F.tailLift.headParameters 0) := by
  obtain ⟨p,hp⟩ := F.tailLift.program.surjective q
  subst q
  change (F.tailLift.program.toMap p).val.2
    (suffixIndex F.tailLift.program.rvArity_le 0) =
      (F.tailLift.program.toMap p).val.2 (Fin.natAdd 1 (F.tailLift.carried 0))
  rw [F.tailLift.program.oldLabels]
  change p.val.2 0 = (headKeyMap F.tailLift.target (F.tailLift.special.toMap p)).val.2
    (Fin.natAdd 1 (F.tailLift.carried 0))
  rw [headKeyMap_apply]
  simpa only [headKey,Fin.append_right,Function.comp_apply] using (congrFun (F.tailLift.parameters p) 0).symm

end IntegrationInACVF.Section7.IndependentRectangleFamilyPreparations
