import Integration7.RectangleFamilyHeadImageCarriers
import Integration7.RVLabelConstraintSpecialPreparations
import Integration7.GammaRectangleFamilyHeadPreparations

/-! An independently chosen preparation of the original labelled tail
lifts through the head contraction of the whole rectangle family. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section5
open IntegrationInACVF.Section5 IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {G : Base (M := M)} {S : Set M} {m r b : ℕ}

theorem gamma_rectangle_family_second_stage_preparation_exists
    (H : DefSet (M := M) S 2 m) (hH : GammaSetDefinable G (carrier H))
    (hRect : RectangularRVFibres (carrier H))
    {D : DefSet (M := M) S 1 r} (T : SpecialBijection (Map.image (coordinateProjectMap 0 H)) D)
    (hT : GammaChainDefinable G T.chain) (hD : IsRVPullback (carrier D))
    {E : DefSet (M := M) S 1 b} (W : SpecialBijection (Map.image (coordinateProjectMap 1 H)) E)
    (hW : GammaChainDefinable G W.chain) (hE : IsRVPullback (carrier E)) :
    Nonempty (RVLabelConstraintSpecialPreparation W
      (rectangleFamilyHeadPreparation H hRect T hD).contractedSet (headImage D)
      (rectangleHeadOldLabelIndex T) G) := by
  apply gamma_rv_label_constraint_special_preparation_exists W hW hE _
    (gamma_headImage _ (rectangle_family_head_preparation_target_gamma H hH hRect T hT hD)) _ _
  exact rectangle_family_head_image_carrier H hRect T hD

def independentRectangleFamilyProgram
    (H : DefSet (M := M) S 2 m) (hRect : RectangularRVFibres (carrier H))
    {D : DefSet (M := M) S 1 r} (T : SpecialBijection (Map.image (coordinateProjectMap 0 H)) D)
    (hD : IsRVPullback (carrier D))
    {E : DefSet (M := M) S 1 b} {W : SpecialBijection (Map.image (coordinateProjectMap 1 H)) E}
    (L : RVLabelConstraintSpecialPreparation W
      (rectangleFamilyHeadPreparation H hRect T hD).contractedSet (headImage D)
      (rectangleHeadOldLabelIndex T) G) :
    OrderedContractionProgram S H L.head.contractedSet :=
  .step (rectangleFamilyHeadPreparation H hRect T hD) L.program

theorem gamma_independent_rectangle_family_program
    (H : DefSet (M := M) S 2 m) (hH : GammaSetDefinable G (carrier H))
    (hRect : RectangularRVFibres (carrier H))
    {D : DefSet (M := M) S 1 r} (T : SpecialBijection (Map.image (coordinateProjectMap 0 H)) D)
    (hT : GammaChainDefinable G T.chain) (hD : IsRVPullback (carrier D))
    {E : DefSet (M := M) S 1 b} {W : SpecialBijection (Map.image (coordinateProjectMap 1 H)) E}
    (L : RVLabelConstraintSpecialPreparation W
      (rectangleFamilyHeadPreparation H hRect T hD).contractedSet (headImage D)
      (rectangleHeadOldLabelIndex T) G) :
    GammaProgramDefinable G (independentRectangleFamilyProgram H hRect T hD L) :=
  ⟨rectangle_family_head_preparation_map_gamma H hH hRect T hT hD,
    rectangle_family_head_preparation_target_gamma H hH hRect T hT hD,L.program_gamma⟩

def independentRectangleFamilyContraction
    (H : DefSet (M := M) S 2 m) (hRect : RectangularRVFibres (carrier H))
    {D : DefSet (M := M) S 1 r} (T : SpecialBijection (Map.image (coordinateProjectMap 0 H)) D)
    (hD : IsRVPullback (carrier D))
    {E : DefSet (M := M) S 1 b} {W : SpecialBijection (Map.image (coordinateProjectMap 1 H)) E}
    (L : RVLabelConstraintSpecialPreparation W
      (rectangleFamilyHeadPreparation H hRect T hD).contractedSet (headImage D)
      (rectangleHeadOldLabelIndex T) G) : StandardContraction H (Equiv.refl _) :=
  standardFromProgram H (Equiv.refl _) (independentRectangleFamilyProgram H hRect T hD L)
    (IntegrationInACVF.Section6.vfPermutationImage_id_eq H).symm

theorem gamma_independent_rectangle_family_contraction
    (H : DefSet (M := M) S 2 m) (hH : GammaSetDefinable G (carrier H))
    (hRect : RectangularRVFibres (carrier H))
    {D : DefSet (M := M) S 1 r} (T : SpecialBijection (Map.image (coordinateProjectMap 0 H)) D)
    (hT : GammaChainDefinable G T.chain) (hD : IsRVPullback (carrier D))
    {E : DefSet (M := M) S 1 b} {W : SpecialBijection (Map.image (coordinateProjectMap 1 H)) E}
    (L : RVLabelConstraintSpecialPreparation W
      (rectangleFamilyHeadPreparation H hRect T hD).contractedSet (headImage D)
      (rectangleHeadOldLabelIndex T) G) :
    GammaProgramDefinable G (independentRectangleFamilyContraction H hRect T hD L).program :=
  gamma_standardFromProgram _ _ _ _ (gamma_independent_rectangle_family_program H hH hRect T hT hD L)

end IntegrationInACVF.Section7
