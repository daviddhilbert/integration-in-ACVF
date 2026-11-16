module

public import Integration7.HKZeroPositiveCoefficientLiftBijections
public import Integration7.HKAEZeroPositiveCoefficientProducts
public import Integration7.HKAEZeroIntegrals
public import Integration7.PositiveVolumeIntegrationProducts
public import Integration7.AppendedVolumeFunctionIntegrals

@[expose] public section

/-! Coefficient-first integration of a positive coefficient times an
ordinary-valued family is the actual graded product of their integrals. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters

namespace IntegrationInACVF.Section7.HK
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n a p : ℕ}

theorem zero_family_positive_coefficient_appended_integral
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (Ξ : Set (Values.Gamma (M := M))) (hΞ : Cardinal.mk Ξ < C.κ)
    (hGenerated : VFGammaGeneratedBase (⟨(C.base : Set M),Ξ⟩ : Base (M := M)))
    (hNames : commonRealNames (⟨(C.base : Set M),Ξ⟩ : Base (M := M)) ⊆ (C.base : Set M))
    (γ : Values.Gamma (M := M)) (hγ : γ ∈ Ξ) (hγ1 : 1 < γ)
    (U : PositiveRVVolumeObject (M := M) (C.base : Set M) p) (F : ZeroVFVolumeFamily C (n+1) a) :
    HEq (selectedFamilyIntegralValue hc C Ξ hGenerated (selectedZeroFamilyPositiveProduct U F))
      (rvVolumeBlowupClassesProduct hc C (p+1) (n+1) (positiveVolumeBlowupClass hc C U)
        (positiveVolumeIntegrationEquiv hc C Ξ hΞ hGenerated hNames γ hγ hγ1
          (positiveVFVolumeIsoClass hc C F.fullVFObject))) := by
  let S := selectedZeroFamilyPositiveProduct U F
  let P := (rvVolumeLift U).prod F.fullVFObject
  let h := zero_positive_coefficient_lift_degree n p
  let E := positiveVolumeIntegrationEquiv hc C Ξ hΞ hGenerated hNames γ hγ hγ1
    (k := appendVolumeDegree (n+1) p)
  let e := (definableVolumeFamilyAppendedSelectionBijection hc (F.mulConstant U)).trans hc C
    ((zeroPositiveCoefficientLiftBijection hc F U).symm hc C)
  have hClass := (positiveVFVolumeIsoClass_eq_iff hc C).mpr ⟨VFVolumeIso.of_bijection e⟩
  have hS := selected_family_appended_integral_full_lift hc C Ξ hΞ hGenerated hNames γ hγ hγ1 S
  have hCast := positive_vf_volume_integration_reindex_heq hc C Ξ hΞ hGenerated hNames γ hγ hγ1 P h
  have hProduct := positive_volume_integration_product hc C Ξ hΞ hGenerated hNames γ hγ hγ1
    (positiveVFVolumeIsoClass hc C (rvVolumeLift U)) (positiveVFVolumeIsoClass hc C F.fullVFObject)
  have hU := (proposition_7_9_positive hc C Ξ hΞ hGenerated hNames γ hγ hγ1 (rvVolumeLift U) U).mpr rfl
  rw [hU] at hProduct
  exact (heq_of_eq hS.symm).trans ((heq_of_eq (congrArg E hClass)).trans (hCast.trans (heq_of_eq hProduct)))

theorem ae_zero_positive_coefficient_appended_integral
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (Ξ : Set (Values.Gamma (M := M))) (hΞ : Cardinal.mk Ξ < C.κ)
    (hGenerated : VFGammaGeneratedBase (⟨(C.base : Set M),Ξ⟩ : Base (M := M)))
    (hNames : commonRealNames (⟨(C.base : Set M),Ξ⟩ : Base (M := M)) ⊆ (C.base : Set M))
    (γ : Values.Gamma (M := M)) (hγ : γ ∈ Ξ) (hγ1 : 1 < γ)
    (u : PositiveVolumeBlowupClasses hc C p) (f : AEZeroVolumeFunction hc C n) :
    HEq (aeRVVolumeFunctionAppendedIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1
      (aeZeroVolumeFunctionPositiveCoefficientProduct hc C n p u f))
      (rvVolumeBlowupClassesProduct hc C (p+1) (n+1) u
        (aeZeroVolumeFunctionIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 f)) :=
  Quotient.inductionOn₂ u f (fun U F =>
    zero_family_positive_coefficient_appended_integral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 U F.2)

end IntegrationInACVF.Section7.HK
