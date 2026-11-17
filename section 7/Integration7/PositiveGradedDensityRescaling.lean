module

public import Integration7.AERVVolumeDensityRescalingLinearity
public import Integration7.GradedAEVolumeActionCoherence
public import Integration7.GradedSemiringActionShifts
public import Integration7.GradedSemiringActionLinearMaps

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! Positive homogeneous AE functions assemble into their genuine raw
module over every coefficient degree. Named density rescaling is linear
on this whole module, without adding ordinary-valued inputs. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open scoped DirectSum
namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)

def positiveAEVolumeGradedAction (n : ℕ) :
    GradedSemiringAction (RVVolumeBlowupClasses hc C) (AERVVolumeFunction hc C n) :=
  (aeVolumeFunctionGradedAction hc C n).shift 1

abbrev PositiveGradedAEVolumeFunction (n : ℕ) := DirectSum ℕ (AERVVolumeFunction hc C n)

instance positiveGradedAEVolumeFunctionModule (n : ℕ) :
    Module (RVVolumeBlowupSemiring hc C) (PositiveGradedAEVolumeFunction hc C n) :=
  gradedSemiringActionModule (positiveAEVolumeGradedAction hc C n)

variable (c : CanonicalRV.RVSort M) (hcS : c.val ∈ C.base) (hc0 : c ≠ 0) (n : ℕ)

theorem ae_rv_volume_density_rescale_degree_heq {i j : ℕ} (h : i=j)
    {f : AERVVolumeFunction hc C n i} {g : AERVVolumeFunction hc C n j} (he : HEq f g) :
    HEq (aeRVVolumeFunctionRescale hc C c hcS hc0 f) (aeRVVolumeFunctionRescale hc C c hcS hc0 g) := by
  cases h
  cases he
  rfl

theorem positive_graded_density_rescale_compatible (i j : ℕ)
    (u : RVVolumeBlowupClasses hc C i) (f : AERVVolumeFunction hc C n j) :
    aeRVVolumeFunctionRescale hc C c hcS hc0 ((positiveAEVolumeGradedAction hc C n).act i j u f)=
      (positiveAEVolumeGradedAction hc C n).act i j u (aeRVVolumeFunctionRescale hc C c hcS hc0 f) := by
  have hR := graded_shift_component_action_heq (aeVolumeFunctionGradedAction hc C n) 1 i j u f
  have hT := graded_shift_component_action_heq (aeVolumeFunctionGradedAction hc C n) 1 i j u
    (aeRVVolumeFunctionRescale hc C c hcS hc0 f)
  cases i with
  | zero =>
    have hL := ae_rv_volume_density_rescale_degree_heq hc C c hcS hc0 n (Nat.zero_add j)
      (hR.trans (ae_volume_component_zero_coefficient_heq hc C n (j+1) u f))
    exact eq_of_heq (hL.trans ((heq_of_eq (ae_rv_volume_density_rescale_smul hc C c hcS hc0 u f)).trans
      (hT.trans (ae_volume_component_zero_coefficient_heq hc C n (j+1) u
        (aeRVVolumeFunctionRescale hc C c hcS hc0 f))).symm))
  | succ p =>
    have hL := ae_rv_volume_density_rescale_degree_heq hc C c hcS hc0 n rfl hR
    exact eq_of_heq (hL.trans ((heq_of_eq (ae_rv_volume_rescale_positive_coefficient hc C c hcS hc0 u f)).trans hT.symm))

def positiveGradedAEVolumeDensityRescale :
    PositiveGradedAEVolumeFunction hc C n →ₗ[RVVolumeBlowupSemiring hc C] PositiveGradedAEVolumeFunction hc C n :=
  gradedSemiringActionLinearMap (positiveAEVolumeGradedAction hc C n) (positiveAEVolumeGradedAction hc C n)
    (fun j => (aeRVVolumeFunctionRescaleOrdinaryLinearMap hc C c hcS hc0 n j).toAddMonoidHom)
    (positive_graded_density_rescale_compatible hc C c hcS hc0 n)

theorem positive_graded_density_rescale_of (j : ℕ) (f : AERVVolumeFunction hc C n j) :
    positiveGradedAEVolumeDensityRescale hc C c hcS hc0 n (DirectSum.of _ j f)=
      DirectSum.of _ j (aeRVVolumeFunctionRescale hc C c hcS hc0 f) := by
  change gradedComponentMapToSum
    (fun j => (aeRVVolumeFunctionRescaleOrdinaryLinearMap hc C c hcS hc0 n j).toAddMonoidHom)
    (DirectSum.of _ j f)=_
  exact graded_component_map_to_sum_of _ j f
end IntegrationInACVF.Section7
