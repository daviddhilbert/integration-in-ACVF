module

public import Integration7.AEOrdinaryVolumeScalarActions

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! Ordinary-valued AE functions form a semimodule over the actual
ordinary RV[0] coefficient semiring, with every law checked fibrewise. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open scoped DirectSum

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

instance aeOrdinaryRVVolumeFunctionModule
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M) (n : ℕ) :
    Module (RVVolumeBlowupClasses hc C 0) (AEOrdinaryRVVolumeFunction hc C n) where
  one_smul f := Quotient.inductionOn f (fun F => Quotient.sound
    (ae_ordinary_rv_volume_equivalent_of_pointwise hc C (fun x => by
      rw [ordinary_volume_family_scalar_row_class]
      change ordinaryVolumeCoefficientExtend hc C (vfParameterVolumeContext C x)
        (fun _ h => vfParameterVolumeContext_contains C x (Or.inl h)) 1 * _ = _
      rw [map_one,one_mul])))
  mul_smul z t f := Quotient.inductionOn₃ z t f (fun Z T F => Quotient.sound
    (ae_ordinary_rv_volume_equivalent_of_pointwise hc C (fun x => by
      simp only [ordinary_volume_family_scalar_row_class]
      let e := ordinaryVolumeCoefficientExtend hc C (vfParameterVolumeContext C x)
        (fun _ h => vfParameterVolumeContext_contains C x (Or.inl h))
      change e (rvVolumeBlowupClass hc C (n := 0) Z * rvVolumeBlowupClass hc C (n := 0) T) * _ =
        e (rvVolumeBlowupClass hc C (n := 0) Z) * (e (rvVolumeBlowupClass hc C (n := 0) T) * _)
      rw [map_mul,mul_assoc])))
  smul_zero z := Quotient.inductionOn z (fun Z => Quotient.sound
    (ae_ordinary_rv_volume_equivalent_of_pointwise hc C (fun x => by
      rw [ordinary_volume_family_scalar_row_class,ordinary_zero_volume_family_row_class,mul_zero])))
  smul_add z f g := Quotient.inductionOn₃ z f g (fun Z F G => Quotient.sound
    (ae_ordinary_rv_volume_equivalent_of_pointwise hc C (fun x => by
      simp only [ordinary_volume_family_scalar_row_class,ordinary_volume_family_coprod_row_class]
      exact mul_add _ _ _)))
  add_smul z t f := Quotient.inductionOn₃ z t f (fun Z T F => Quotient.sound
    (ae_ordinary_rv_volume_equivalent_of_pointwise hc C (fun x => by
      simp only [ordinary_volume_family_scalar_row_class,ordinary_volume_family_coprod_row_class]
      let e := ordinaryVolumeCoefficientExtend hc C (vfParameterVolumeContext C x)
        (fun _ h => vfParameterVolumeContext_contains C x (Or.inl h))
      change e (rvVolumeBlowupClass hc C (n := 0) Z + rvVolumeBlowupClass hc C (n := 0) T) * _ =
        e (rvVolumeBlowupClass hc C (n := 0) Z) * _ + e (rvVolumeBlowupClass hc C (n := 0) T) * _
      rw [map_add,add_mul])))
  zero_smul f := Quotient.inductionOn f (fun F => Quotient.sound
    (ae_ordinary_rv_volume_equivalent_of_pointwise hc C (fun x => by
      rw [ordinary_volume_family_scalar_row_class,ordinary_zero_volume_family_row_class]
      change ordinaryVolumeCoefficientExtend hc C (vfParameterVolumeContext C x)
        (fun _ h => vfParameterVolumeContext_contains C x (Or.inl h)) 0 * _ = 0
      rw [map_zero,zero_mul])))

end IntegrationInACVF.Section7
