module

public import Integration7.HKSupportedGradedVolumeFunctions
public import Integration7.SupportedUnivVolumeEquivalences
public import Integration7.GradedComponentMapInjectivity

@[expose] public section

/-! Supporting functions on the whole VF space changes no AE classes,
including weighted degree zero. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.DefinableGeometry

namespace IntegrationInACVF.Section7.HK
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n : ℕ}
variable (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)

theorem supported_volume_component_forget_injective
    (X : DefSet (rawVFSpace (M := M) (n+1)) (C.base : Set M)) (j : ℕ) :
    Function.Injective (supportedVolumeComponentForgetAddHom hc C X j) := by
  cases j with
  | zero => exact supported_zero_volume_function_forget_injective hc C X
  | succ k => exact supported_volume_function_forget_injective hc C X

theorem supported_graded_volume_forget_injective
    (X : DefSet (rawVFSpace (M := M) (n+1)) (C.base : Set M)) :
    Function.Injective (supportedGradedVolumeForgetAddHom hc C X) :=
  graded_component_map_to_sum_injective (supportedVolumeComponentForgetAddHom hc C X)
    (supported_volume_component_forget_injective hc C X)

def supportedZeroVolumeUnivLift : AEZeroVolumeFunction hc C n →
    SupportedAEZeroVolumeFunction hc C (DefSet.univ (rawVFSpace (M := M) (n+1)) (C.base : Set M)) :=
  Quotient.map (fun F => ⟨F.1,⟨F.2,fun _ => Set.mem_univ _⟩⟩) (fun _ _ h => h)

theorem supported_zero_volume_univ_forget_lift (f : AEZeroVolumeFunction hc C n) :
    supportedZeroVolumeFunctionForget hc C (DefSet.univ _ _) (supportedZeroVolumeUnivLift hc C f) = f :=
  Quotient.inductionOn f (fun _ => rfl)

theorem supported_volume_component_univ_forget_bijective (n j : ℕ) :
    Function.Bijective (supportedVolumeComponentForgetAddHom hc C
      (DefSet.univ (rawVFSpace (M := M) (n+1)) (C.base : Set M)) j) := by
  refine ⟨supported_volume_component_forget_injective hc C _ j,?_⟩
  cases j with
  | zero => intro f; exact ⟨supportedZeroVolumeUnivLift hc C f,supported_zero_volume_univ_forget_lift hc C f⟩
  | succ k => intro f; exact ⟨supportedVolumeUnivLift hc C n k f,supported_volume_univ_forget_lift hc C n k f⟩

def supportedVolumeComponentUnivEquiv (n j : ℕ) :
    SupportedVolumeFunctionComponent hc C (DefSet.univ (rawVFSpace (M := M) (n+1)) (C.base : Set M)) j ≃+
      AEVolumeFunctionComponent hc C n j :=
  AddEquiv.ofBijective (supportedVolumeComponentForgetAddHom hc C _ j)
    (supported_volume_component_univ_forget_bijective hc C n j)

end IntegrationInACVF.Section7.HK
