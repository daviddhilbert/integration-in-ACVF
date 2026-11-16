import Integration7.HKWeightedFamilyZeroProductLifts
import Integration7.HKAERVWeightedZeroModules
import Integration7.AERVVolumeFunctionIntegrals
import Integration7.HKWeightedVFZeroClassProducts

/-! The canonical integral preserves multiplication by an ordinary
RV[0] coefficient. This is the actual finite-factor product, compared
through its full VF realization; no density is added to the coefficient. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4

namespace IntegrationInACVF.Section7.HK
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n a k : ℕ}

theorem selected_family_canonical_integral_zero_coefficient
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (Ξ : Set (Values.Gamma (M := M))) (hΞ : Cardinal.mk Ξ < C.κ)
    (hGenerated : VFGammaGeneratedBase (⟨(C.base : Set M),Ξ⟩ : Base (M := M)))
    (hNames : commonRealNames (⟨(C.base : Set M),Ξ⟩ : Base (M := M)) ⊆ (C.base : Set M))
    (γ : Values.Gamma (M := M)) (hγ : γ ∈ Ξ) (hγ1 : 1 < γ)
    (F : SelectedVFVolumeFamily C (n+1) a k) (Z : ZeroRVVolumeObject (M := M) (C.base : Set M)) :
    selectedFamilyCanonicalIntegralValue hc C Ξ hGenerated (selectedFamilyWeightedZeroProduct F Z) =
      rvVolumeBlowupClassesProduct hc C (((k+1)+n)+1) 0
        (selectedFamilyCanonicalIntegralValue hc C Ξ hGenerated F) (rvVolumeBlowupClass hc C Z) := by
  let z := rvVolumeBlowupClass hc C (n := 0) Z
  let E := positiveVolumeIntegrationEquiv hc C Ξ hΞ hGenerated hNames γ hγ hγ1 (k := (n+1)+k)
  have hClass : positiveVFVolumeIsoClass hc C (selectedFamilyWeightedZeroProduct F Z).fullLift =
      positiveVFZeroCoefficientProduct hc C (positiveVFVolumeIsoClass hc C F.fullLift) z :=
    (positiveVFVolumeIsoClass_eq_iff hc C).mpr ⟨VFVolumeIso.of_bijection (weightedVolumeFamilyZeroProductLiftBijection hc F Z)⟩
  have hIntegral := (congrArg E hClass).trans
    (positive_volume_integration_zero_coefficient_product hc C Ξ hΞ hGenerated hNames γ hγ hγ1 _ z)
  have hF := selected_family_canonical_integral_full_lift hc C Ξ hΞ hGenerated hNames γ hγ hγ1 F
  have hProduct := dependent_degree_map_heq
    (fun j (v : PositiveVolumeBlowupClasses hc C j) => rvVolumeBlowupClassesProduct hc C (j+1) 0 v z)
    (family_realization_degree_eq n k) hF.symm
  exact eq_of_heq ((selected_family_canonical_integral_full_lift hc C Ξ hΞ hGenerated hNames γ hγ hγ1
    (selectedFamilyWeightedZeroProduct F Z)).trans ((heq_of_eq hIntegral).trans hProduct))

theorem ae_rv_volume_function_integral_zero_coefficient
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (Ξ : Set (Values.Gamma (M := M))) (hΞ : Cardinal.mk Ξ < C.κ)
    (hGenerated : VFGammaGeneratedBase (⟨(C.base : Set M),Ξ⟩ : Base (M := M)))
    (hNames : commonRealNames (⟨(C.base : Set M),Ξ⟩ : Base (M := M)) ⊆ (C.base : Set M))
    (γ : Values.Gamma (M := M)) (hγ : γ ∈ Ξ) (hγ1 : 1 < γ)
    (f : AERVVolumeFunction hc C n k) (z : RVBlowupClasses hc C 0) :
    aeRVVolumeFunctionIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1
      (aeRVVolumeFunctionWeightedZeroProduct hc C n k f z) =
      rvVolumeBlowupClassesProduct hc C (((k+1)+n)+1) 0
        (aeRVVolumeFunctionIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 f) z :=
  Quotient.inductionOn₂ f z (fun F Z =>
    selected_family_canonical_integral_zero_coefficient hc C Ξ hΞ hGenerated hNames γ hγ hγ1 F.2 Z)

end IntegrationInACVF.Section7.HK
