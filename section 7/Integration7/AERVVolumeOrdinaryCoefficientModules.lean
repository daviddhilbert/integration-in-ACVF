import Integration7.OrdinaryVolumeCoefficientScalarRows

/-! Positive homogeneous AE volume functions form a semimodule over
the ordinary RV[0] coefficient semiring. Scalar multiplication is the
actual finite-factor family construction, and the laws hold fibrewise. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open scoped DirectSum

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

instance aeRVVolumeFunctionOrdinarySMul
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M) (n k : ℕ) :
    SMul (RVVolumeBlowupClasses hc C 0) (AERVVolumeFunction hc C n k) :=
  ⟨fun z f => aeRVVolumeFunctionZeroCoefficientProduct hc C n k f z⟩

instance aeRVVolumeFunctionOrdinaryModule
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M) (n k : ℕ) :
    Module (RVVolumeBlowupClasses hc C 0) (AERVVolumeFunction hc C n k) where
  one_smul f := Quotient.inductionOn f (fun F => Quotient.sound
    (ae_rv_volume_function_equivalent_of_pointwise hc C (fun x => by
      rw [volume_family_zero_product_row_scalar]
      change ordinaryVolumeCoefficientExtend hc C (vfParameterVolumeContext C x)
        (fun _ h => vfParameterVolumeContext_contains C x (Or.inl h)) 1 • _ = _
      rw [map_one,one_smul])))
  mul_smul z t f := Quotient.inductionOn₃ z t f (fun Z T F => Quotient.sound
    (ae_rv_volume_function_equivalent_of_pointwise hc C (fun x => by
      simp only [volume_family_zero_product_row_scalar]
      let e := ordinaryVolumeCoefficientExtend hc C (vfParameterVolumeContext C x)
        (fun _ h => vfParameterVolumeContext_contains C x (Or.inl h))
      change e (rvVolumeBlowupClass hc C (n := 0) Z * rvVolumeBlowupClass hc C (n := 0) T) • _ =
        e (rvVolumeBlowupClass hc C (n := 0) Z) • (e (rvVolumeBlowupClass hc C (n := 0) T) • _)
      rw [map_mul,mul_smul])))
  smul_zero z := Quotient.inductionOn z (fun Z => Quotient.sound
    (ae_rv_volume_function_equivalent_of_pointwise hc C (fun x => by
      rw [volume_family_zero_product_row_scalar,selected_zero_volume_family_row_class,
        smul_zero])))
  smul_add z f g := Quotient.inductionOn₃ z f g (fun Z F G => Quotient.sound
    (ae_rv_volume_function_equivalent_of_pointwise hc C (fun x => by
      simp only [volume_family_zero_product_row_scalar,selected_volume_family_sum_row_class]
      exact smul_add _ _ _)))
  add_smul z t f := Quotient.inductionOn₃ z t f (fun Z T F => Quotient.sound
    (ae_rv_volume_function_equivalent_of_pointwise hc C (fun x => by
      simp only [volume_family_zero_product_row_scalar,selected_volume_family_sum_row_class]
      let e := ordinaryVolumeCoefficientExtend hc C (vfParameterVolumeContext C x)
        (fun _ h => vfParameterVolumeContext_contains C x (Or.inl h))
      change e (rvVolumeBlowupClass hc C (n := 0) Z + rvVolumeBlowupClass hc C (n := 0) T) • _ =
        e (rvVolumeBlowupClass hc C (n := 0) Z) • _ + e (rvVolumeBlowupClass hc C (n := 0) T) • _
      rw [map_add,add_smul])))
  zero_smul f := Quotient.inductionOn f (fun F => Quotient.sound
    (ae_rv_volume_function_equivalent_of_pointwise hc C (fun x => by
      rw [volume_family_zero_product_row_scalar,selected_zero_volume_family_row_class]
      change ordinaryVolumeCoefficientExtend hc C (vfParameterVolumeContext C x)
        (fun _ h => vfParameterVolumeContext_contains C x (Or.inl h)) 0 • _ = 0
      rw [map_zero,zero_smul])))

end IntegrationInACVF.Section7
