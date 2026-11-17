module

public import Integration7.AERVVolumeBaseRestrictions

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! Base restriction is the actual additive map to supported AE
functions. Its two fibre values are the unchanged row and zero. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.DefinableGeometry
namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n k : ℕ}

theorem ae_volume_restriction_map_add
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (X : DefSet (rawVFSpace (M := M) (n+1)) (C.base : Set M)) (f g : AERVVolumeFunction hc C n k) :
    aeVolumeFunctionRestrictToSupported hc C X (f+g) =
      aeVolumeFunctionRestrictToSupported hc C X f + aeVolumeFunctionRestrictToSupported hc C X g := by
  induction f using Quotient.inductionOn with
  | h F =>
    induction g using Quotient.inductionOn with
    | h G =>
      apply Quotient.sound
      apply ae_rv_volume_function_equivalent_of_pointwise hc C
      intro x
      change positiveVolumeBlowupClass hc (vfParameterVolumeContext C x)
          (((selectedVolumeFamilySum F.2 G.2).onBase X).rowInContext x) =
        positiveVolumeBlowupClass hc (vfParameterVolumeContext C x)
          ((selectedVolumeFamilySum (F.2.onBase X) (G.2.onBase X)).rowInContext x)
      rw [selected_volume_family_sum_row_class]
      by_cases hx : x ∈ X.carrier
      · rw [selected_volume_on_base_row_class_inside hc _ X x hx,selected_volume_family_sum_row_class,
          selected_volume_on_base_row_class_inside hc F.2 X x hx,
          selected_volume_on_base_row_class_inside hc G.2 X x hx]
      · rw [selected_volume_on_base_row_class_outside hc _ X x hx,
          selected_volume_on_base_row_class_outside hc F.2 X x hx,
          selected_volume_on_base_row_class_outside hc G.2 X x hx,zero_add]

theorem ae_volume_restriction_map_zero
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (X : DefSet (rawVFSpace (M := M) (n+1)) (C.base : Set M)) :
    aeVolumeFunctionRestrictToSupported hc C X (0 : AERVVolumeFunction hc C n k) = 0 := by
  apply Quotient.sound
  apply ae_rv_volume_function_equivalent_of_pointwise hc C
  intro x
  change positiveVolumeBlowupClass hc (vfParameterVolumeContext C x)
      (((selectedZeroVolumeFamily C (n+1) k).onBase X).rowInContext x) =
    positiveVolumeBlowupClass hc (vfParameterVolumeContext C x)
      ((selectedZeroVolumeFamily C (n+1) k).rowInContext x)
  by_cases hx : x ∈ X.carrier
  · exact selected_volume_on_base_row_class_inside hc _ X x hx
  · rw [selected_volume_on_base_row_class_outside hc _ X x hx,selected_zero_volume_family_row_class]

def aeVolumeRestrictionAddHom
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (X : DefSet (rawVFSpace (M := M) (n+1)) (C.base : Set M)) :
    AERVVolumeFunction hc C n k →+ SupportedAERVVolumeFunction hc C X k where
  toFun := aeVolumeFunctionRestrictToSupported hc C X
  map_zero' := ae_volume_restriction_map_zero hc C X
  map_add' := ae_volume_restriction_map_add hc C X
end IntegrationInACVF.Section7
