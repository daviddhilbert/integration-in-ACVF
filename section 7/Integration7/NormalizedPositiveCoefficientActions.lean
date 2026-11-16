module

public import Integration7.NormalizedPositiveFunctionGeneration

@[expose] public section

/-! The actual positive coefficient action has the scalar-extension
meaning on normalized positive function generators. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

theorem normalized_positive_function_coefficient
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M) (n p k : ℕ)
    (u : PositiveVolumeBlowupClasses hc C p) (f : AERVVolumeFunction hc C n k) :
    normalizedPositiveVolumeFunction hc C n ((p+1)+k)
      (aeRVVolumeFunctionPositiveCoefficientProduct hc C n p k u f) =
    normalizedVolumeCoefficientMap hc C (DirectSum.of (RVVolumeBlowupClasses hc C) (p+1) u) •
      normalizedPositiveVolumeFunction hc C n k f := by
  have h := normalized_volume_function_generator_smul hc C n
    (DirectSum.of (RVVolumeBlowupClasses hc C) (p+1) u)
    (DirectSum.of (AEVolumeFunctionComponent hc C n) (k+1) f)
  rw [graded_ae_volume_coefficient_action_of] at h
  exact h
end IntegrationInACVF.Section7
