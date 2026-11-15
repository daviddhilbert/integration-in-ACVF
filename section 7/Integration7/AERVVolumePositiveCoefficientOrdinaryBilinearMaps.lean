import Integration7.AERVVolumeMixedScalarCoherence
import Integration7.OrdinaryVolumeCoefficientCommSemiring

/-! Positive coefficient multiplication is an actual bilinear map
over the ordinary RV[0] coefficient semiring on positive AE functions. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open scoped DirectSum

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

def aeRVVolumeFunctionPositiveCoefficientOrdinaryBilinearMap
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M) (n p k : ℕ) :
    PositiveVolumeBlowupClasses hc C p →ₗ[RVVolumeBlowupClasses hc C 0]
      (AERVVolumeFunction hc C n k →ₗ[RVVolumeBlowupClasses hc C 0] AERVVolumeFunction hc C n ((p+1)+k)) where
  toFun u := {
    toAddHom := aeRVVolumeFunctionPositiveCoefficientBiadditive hc C n p k u
    map_smul' z f := ae_rv_volume_positive_coefficient_smul_right hc C z u f }
  map_add' u v := LinearMap.ext (fun f => ae_rv_volume_positive_coefficient_add hc C u v f)
  map_smul' z u := LinearMap.ext (fun f => ae_rv_volume_positive_coefficient_smul_left hc C z u f)

end IntegrationInACVF.Section7
