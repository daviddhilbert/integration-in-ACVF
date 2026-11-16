module

public import Integration7.SupportedPositiveGradedForget
public import Integration7.NormalizedPositiveDegreeFunctions
public import Integration7.GradedComponentMapInjectivity

@[expose] public section

/-! On the full VF domain, the supported positive presentation quotient
is the original positive AE function quotient, with the same graded action. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.DefinableGeometry
namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M) (n : ℕ)

def supportedVolumeUnivLift (j : ℕ) : AERVVolumeFunction hc C n j →
    SupportedAERVVolumeFunction hc C (DefSet.univ (rawVFSpace (M := M) (n+1)) (C.base : Set M)) j :=
  Quotient.map (fun F => ⟨F.1,⟨F.2,fun _ => Set.mem_univ _⟩⟩) (fun _ _ h => h)

theorem supported_volume_univ_forget_lift (j : ℕ) (f : AERVVolumeFunction hc C n j) :
    supportedVolumeFunctionForget hc C (DefSet.univ _ _) (supportedVolumeUnivLift hc C n j f) = f :=
  Quotient.inductionOn f (fun _ => rfl)

def supportedUnivPositiveGradedMap :
    SupportedPositiveGradedVolumeFunction hc C (DefSet.univ (rawVFSpace (M := M) (n+1)) (C.base : Set M))
      →ₗ[RVVolumeBlowupSemiring hc C] PositiveDegreeGradedVolumeFunction hc C n :=
  gradedSemiringActionLinearMap (supportedPositiveGradedAction hc C (DefSet.univ _ _))
    ((aeVolumeFunctionGradedAction hc C n).shift 1)
    (fun j => supportedVolumeFunctionForgetAddHom (k := j) hc C (DefSet.univ _ _))
    (supported_positive_component_action_forget hc C (DefSet.univ _ _))

theorem supported_univ_positive_graded_map_bijective : Function.Bijective (supportedUnivPositiveGradedMap hc C n) := by
  constructor
  · exact graded_component_map_to_sum_injective
      (fun j => supportedVolumeFunctionForgetAddHom (k := j) hc C (DefSet.univ _ _))
      (fun _ => supported_volume_function_forget_injective hc C (DefSet.univ _ _))
  · intro g
    induction g using DirectSum.induction_on with
    | zero => exact ⟨0,map_zero _⟩
    | add f g hf hg =>
      obtain ⟨p,hp⟩ := hf
      obtain ⟨q,hq⟩ := hg
      exact ⟨p+q,(map_add _ _ _).trans (congrArg₂ (fun x y => x+y) hp hq)⟩
    | of j f =>
      refine ⟨DirectSum.of (SupportedAERVVolumeFunction hc C (DefSet.univ _ _)) j
        (supportedVolumeUnivLift hc C n j f),?_⟩
      change gradedComponentMapToSum
        (fun j => supportedVolumeFunctionForgetAddHom (k := j) hc C (DefSet.univ _ _))
        (DirectSum.of (SupportedAERVVolumeFunction hc C (DefSet.univ _ _)) j
          (supportedVolumeUnivLift hc C n j f)) = _
      rw [graded_component_map_to_sum_of]
      exact congrArg (DirectSum.of (fun j => AEVolumeFunctionComponent hc C n (j+1)) j)
        (supported_volume_univ_forget_lift hc C n j f)

def supportedUnivPositiveGradedEquiv :
    SupportedPositiveGradedVolumeFunction hc C (DefSet.univ (rawVFSpace (M := M) (n+1)) (C.base : Set M))
      ≃ₗ[RVVolumeBlowupSemiring hc C] PositiveDegreeGradedVolumeFunction hc C n :=
  LinearEquiv.ofBijective (supportedUnivPositiveGradedMap hc C n) (supported_univ_positive_graded_map_bijective hc C n)
end IntegrationInACVF.Section7
