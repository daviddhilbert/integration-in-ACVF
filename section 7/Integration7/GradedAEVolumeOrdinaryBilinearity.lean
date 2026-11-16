module

public import Integration7.GradedAEVolumeComponentActions

@[expose] public section

/-! Every homogeneous action is bilinear over ordinary RV[0],
including the arithmetic degree identification in the zero coefficient case. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open scoped DirectSum

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

theorem ae_volume_component_action_smul_left
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M) (n i j : ℕ)
    (z : RVVolumeBlowupClasses hc C 0) (u : RVVolumeBlowupClasses hc C i)
    (f : AEVolumeFunctionComponent hc C n j) :
    aeVolumeFunctionComponentCoefficientBiadditive hc C n i j (z • u) f =
      z • aeVolumeFunctionComponentCoefficientBiadditive hc C n i j u f := by
  cases i with
  | zero =>
    let e := aeVolumeFunctionComponentDegreeLinearEquiv hc C n (Nat.zero_add j)
    change e.symm ((z*u) • f)=z • e.symm (u • f)
    rw [mul_smul]
    exact e.symm.map_smul z (u • f)
  | succ p =>
    cases j with
    | zero => exact ae_ordinary_positive_coefficient_smul_left hc C z u f
    | succ k => exact ae_rv_volume_positive_coefficient_smul_left hc C z u f

theorem ae_volume_component_action_smul_right
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M) (n i j : ℕ)
    (z : RVVolumeBlowupClasses hc C 0) (u : RVVolumeBlowupClasses hc C i)
    (f : AEVolumeFunctionComponent hc C n j) :
    aeVolumeFunctionComponentCoefficientBiadditive hc C n i j u (z • f) =
      z • aeVolumeFunctionComponentCoefficientBiadditive hc C n i j u f := by
  cases i with
  | zero =>
    let e := aeVolumeFunctionComponentDegreeLinearEquiv hc C n (Nat.zero_add j)
    change e.symm (u • (z • f))=z • e.symm (u • f)
    rw [smul_comm u z f]
    exact e.symm.map_smul z (u • f)
  | succ p =>
    cases j with
    | zero => exact ae_ordinary_positive_coefficient_smul_right hc C z u f
    | succ k => exact ae_rv_volume_positive_coefficient_smul_right hc C z u f

end IntegrationInACVF.Section7
