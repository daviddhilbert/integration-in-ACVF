import Integration7.VFVolumeRescalingClasses

/-! The genuine positive-dimensional VF integral commutes with named
nonzero density rescaling, before point normalization. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {k : ℕ}
variable (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
variable (Ξ : Set (Values.Gamma (M := M))) (hΞ : Cardinal.mk Ξ < C.κ)
variable (hGenerated : VFGammaGeneratedBase (⟨(C.base : Set M),Ξ⟩ : Base (M := M)))
variable (hNames : commonRealNames (⟨(C.base : Set M),Ξ⟩ : Base (M := M)) ⊆ (C.base : Set M))
variable (γ : Values.Gamma (M := M)) (hγ : γ ∈ Ξ) (hγ1 : 1 < γ)

theorem positive_volume_integration_density_rescale
    (c : CanonicalRV.RVSort M) (hcS : c.val ∈ C.base) (hc0 : c ≠ 0)
    (x : PositiveVFVolumeIsoClasses hc C k) :
    positiveVolumeIntegrationEquiv hc C Ξ hΞ hGenerated hNames γ hγ hγ1
      (positiveVFVolumeClassRescale hc C c hcS hc0 x)=
    positiveVolumeClassRescaleDefinable hc C c (Set.Definable.singleton_of_mem LRV hcS) hc0
      (positiveVolumeIntegrationEquiv hc C Ξ hΞ hGenerated hNames γ hγ hγ1 x) := by
  let E := positiveVolumeIntegrationEquiv hc C Ξ hΞ hGenerated hNames γ hγ hγ1 (k := k)
  change E (positiveVFVolumeClassRescale hc C c hcS hc0 x)=
    positiveVolumeClassRescaleDefinable hc C c (Set.Definable.singleton_of_mem LRV hcS) hc0 (E x)
  obtain ⟨y,rfl⟩ := E.symm.surjective x
  rw [E.apply_symm_apply]
  induction y using Quotient.inductionOn with
  | h U =>
    change E (positiveVFVolumeIsoClass hc C ((rvVolumeLift U).rescale c hcS hc0))=
      positiveVolumeBlowupClass hc C (U.rescaleDefinable c (Set.Definable.singleton_of_mem LRV hcS) hc0)
    apply (proposition_7_9_positive hc C Ξ hΞ hGenerated hNames γ hγ hγ1
      ((rvVolumeLift U).rescale c hcS hc0)
      (U.rescaleDefinable c (Set.Definable.singleton_of_mem LRV hcS) hc0)).mpr
    exact (positiveVFVolumeIsoClass_eq_iff hc C).mpr
      ⟨VFVolumeIso.of_bijection (vfVolumeRescaleLiftBijection hc C U c hcS hc0)⟩
end IntegrationInACVF.Section7
