module

public import Integration7.SelectedVolumeDensityRescaling
public import Integration7.VolumeIntegrationDensityRescaling
public import Integration7.VolumeFamilyRealizationIdentifications
public import Integration7.AERVVolumeFunctionIntegrals

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! Raw family total integration commutes with a named nonzero density
multiplier. Genuine full lifts supply the comparison; their different
coordinate-degree conventions are transported by the checked HEq bridge. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.DefinableGeometry
namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n a k : ℕ}
variable (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)

def selectedFamilyFullLiftRescaleBijection (F : SelectedVFVolumeFamily C n a k)
    (c : CanonicalRV.RVSort M) (hcS : c.val ∈ C.base) (hc0 : c ≠ 0) :
    VFVolumeBijection (F.rescale c hcS hc0).fullLift (F.fullLift.rescale c hcS hc0) := by
  apply VFVolumeBijection.of_preserving_vf_and_density hc C (Map.id _) Function.bijective_id
  · intro p; rfl
  · intro p; rfl

variable (Ξ : Set (Values.Gamma (M := M))) (hΞ : Cardinal.mk Ξ < C.κ)
variable (hGenerated : VFGammaGeneratedBase (⟨(C.base : Set M),Ξ⟩ : Base (M := M)))
variable (hNames : commonRealNames (⟨(C.base : Set M),Ξ⟩ : Base (M := M)) ⊆ (C.base : Set M))
variable (γ : Values.Gamma (M := M)) (hγ : γ ∈ Ξ) (hγ1 : 1 < γ)
include hΞ hNames γ hγ hγ1

theorem selected_family_canonical_integral_density_rescale (F : SelectedVFVolumeFamily C (n+1) a k)
    (c : CanonicalRV.RVSort M) (hcS : c.val ∈ C.base) (hc0 : c ≠ 0) :
    selectedFamilyCanonicalIntegralValue hc C Ξ hGenerated (F.rescale c hcS hc0)=
      positiveVolumeClassRescaleDefinable hc C c (Set.Definable.singleton_of_mem LRV hcS) hc0
        (selectedFamilyCanonicalIntegralValue hc C Ξ hGenerated F) := by
  have hF := selected_family_canonical_integral_full_lift hc C Ξ hΞ hGenerated hNames γ hγ hγ1 (F.rescale c hcS hc0)
  have hG := selected_family_canonical_integral_full_lift hc C Ξ hΞ hGenerated hNames γ hγ hγ1 F
  have hIso : positiveVFVolumeIsoClass hc C (F.rescale c hcS hc0).fullLift=
      positiveVFVolumeClassRescale hc C c hcS hc0 (positiveVFVolumeIsoClass hc C F.fullLift) :=
    (positiveVFVolumeIsoClass_eq_iff hc C).mpr
      ⟨VFVolumeIso.of_bijection (selectedFamilyFullLiftRescaleBijection hc C F c hcS hc0)⟩
  have hInt := (congrArg (positiveVolumeIntegrationEquiv hc C Ξ hΞ hGenerated hNames γ hγ hγ1) hIso).trans
    (positive_volume_integration_density_rescale hc C Ξ hΞ hGenerated hNames γ hγ hγ1
      c hcS hc0 (positiveVFVolumeIsoClass hc C F.fullLift))
  have hScale := dependent_degree_map_heq
    (fun j => positiveVolumeClassRescaleDefinable (k := j) hc C c (Set.Definable.singleton_of_mem LRV hcS) hc0)
    (family_realization_degree_eq n k) hG.symm
  exact eq_of_heq (hF.trans ((heq_of_eq hInt).trans hScale))

theorem ae_rv_volume_integral_density_rescale (f : AERVVolumeFunction hc C n k)
    (c : CanonicalRV.RVSort M) (hcS : c.val ∈ C.base) (hc0 : c ≠ 0) :
    aeRVVolumeFunctionIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1
      (aeRVVolumeFunctionRescale hc C c hcS hc0 f)=
    positiveVolumeClassRescaleDefinable hc C c (Set.Definable.singleton_of_mem LRV hcS) hc0
      (aeRVVolumeFunctionIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 f) := by
  induction f using Quotient.inductionOn with
  | h F => exact selected_family_canonical_integral_density_rescale hc C Ξ hΞ hGenerated hNames γ hγ hγ1 F.2 c hcS hc0
end IntegrationInACVF.Section7
