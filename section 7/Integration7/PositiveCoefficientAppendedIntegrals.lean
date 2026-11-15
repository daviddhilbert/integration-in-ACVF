import Integration7.SelectedPositiveCoefficientLiftBijections
import Integration7.PositiveVolumeIntegrationProducts

/-! Coefficient-first integration preserves actual multiplication by
a positive RV coefficient. The full VF realization is a genuine product;
the heterogeneous equality records only its arithmetic total degree. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n a k p : ℕ}

theorem selected_family_appended_integral_positive_coefficient
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (Ξ : Set (Values.Gamma (M := M))) (hΞ : Cardinal.mk Ξ < C.κ)
    (hGenerated : VFGammaGeneratedBase (⟨(C.base : Set M),Ξ⟩ : Base (M := M)))
    (hNames : commonRealNames (⟨(C.base : Set M),Ξ⟩ : Base (M := M)) ⊆ (C.base : Set M))
    (γ : Values.Gamma (M := M)) (hγ : γ ∈ Ξ) (hγ1 : 1 < γ)
    (U : PositiveRVVolumeObject (M := M) (C.base : Set M) p) (F : SelectedVFVolumeFamily C (n+1) a k) :
    HEq (selectedFamilyIntegralValue hc C Ξ hGenerated (selectedVolumeFamilyLeftProduct U F))
      (rvVolumeBlowupClassesProduct hc C (p+1) (appendVolumeDegree (n+1) k+1)
        (positiveVolumeBlowupClass hc C U) (selectedFamilyIntegralValue hc C Ξ hGenerated F)) := by
  let S := selectedVolumeFamilyLeftProduct U F
  let P := (rvVolumeLift U).prod F.appendedFullLift
  let h := appended_positive_coefficient_degree_eq (n+1) p k
  let E := positiveVolumeIntegrationEquiv hc C Ξ hΞ hGenerated hNames γ hγ hγ1
    (k := appendVolumeDegree (n+1) ((p+1)+k))
  have hClass := (positiveVFVolumeIsoClass_eq_iff hc C).mpr
    ⟨VFVolumeIso.of_bijection (selectedPositiveCoefficientAppendedLiftBijection hc U F)⟩
  have hS := selected_family_appended_integral_full_lift hc C Ξ hΞ hGenerated hNames γ hγ hγ1 S
  have hCast := positive_vf_volume_integration_reindex_heq hc C Ξ hΞ hGenerated hNames γ hγ hγ1 P h
  have hProduct := positive_volume_integration_product hc C Ξ hΞ hGenerated hNames γ hγ hγ1
    (positiveVFVolumeIsoClass hc C (rvVolumeLift U)) (positiveVFVolumeIsoClass hc C F.appendedFullLift)
  have hU := (proposition_7_9_positive hc C Ξ hΞ hGenerated hNames γ hγ hγ1 (rvVolumeLift U) U).mpr rfl
  rw [hU,selected_family_appended_integral_full_lift hc C Ξ hΞ hGenerated hNames γ hγ hγ1 F] at hProduct
  exact (heq_of_eq hS.symm).trans ((heq_of_eq (congrArg E hClass)).trans (hCast.trans (heq_of_eq hProduct)))

end IntegrationInACVF.Section7
