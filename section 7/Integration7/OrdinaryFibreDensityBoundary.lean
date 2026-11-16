module

public import Integration7.RescaledPointBlowupBounds
public import Integration7.OrdinaryVFVolumeFamilies
public import Integration7.PositiveVolumeIntegrationEquivalence

@[expose] public section

/-! Forgetting the density on ordinary RV[0] rows cannot retain the
integrals of arbitrary positive-dimensional VF volume realizations.
The existing ordinary family integral uses its specified unit density;
this boundary does not contradict that unit-density construction. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)

def rescaledPointLiftOrdinaryFamily (c : CanonicalRV.RVSort M)
    (hcS : c.val ∈ C.base) (hc0 : c ≠ 0) : OrdinaryVFVolumeFamily C 1 0 where
  domain := (rvVolumeLift ((degreeOnePointVolumeObject (C.base : Set M)).rescale c hcS hc0)).domain
  finite_labels := (rvVolumeLift ((degreeOnePointVolumeObject (C.base : Set M)).rescale c hcS hc0)).finite_labels

theorem rescaled_point_lift_ordinary_family_equal (c d : CanonicalRV.RVSort M)
    (hcS : c.val ∈ C.base) (hc0 : c ≠ 0) (hdS : d.val ∈ C.base) (hd0 : d ≠ 0) :
    rescaledPointLiftOrdinaryFamily C c hcS hc0=rescaledPointLiftOrdinaryFamily C d hdS hd0 := rfl

variable (Ξ : Set (Values.Gamma (M := M))) (hΞ : Cardinal.mk Ξ < C.κ)
variable (hGenerated : VFGammaGeneratedBase (⟨(C.base : Set M),Ξ⟩ : Base (M := M)))
variable (hNames : commonRealNames (⟨(C.base : Set M),Ξ⟩ : Base (M := M)) ⊆ (C.base : Set M))
variable (γ : Values.Gamma (M := M)) (hγ : γ ∈ Ξ) (hγ1 : 1 < γ)

theorem rescaled_point_lift_integrals_unequal (c d : CanonicalRV.RVSort M)
    (hcS : c.val ∈ C.base) (hc0 : c ≠ 0) (hdS : d.val ∈ C.base) (hd0 : d ≠ 0)
    (hAbs : RVOperations.absoluteHom c ≠ RVOperations.absoluteHom d) :
    positiveVolumeIntegrationEquiv hc C Ξ hΞ hGenerated hNames γ hγ hγ1
      (positiveVFVolumeIsoClass hc C (rvVolumeLift ((degreeOnePointVolumeObject (C.base : Set M)).rescale c hcS hc0))) ≠
    positiveVolumeIntegrationEquiv hc C Ξ hΞ hGenerated hNames γ hγ hγ1
      (positiveVFVolumeIsoClass hc C (rvVolumeLift ((degreeOnePointVolumeObject (C.base : Set M)).rescale d hdS hd0))) := by
  have hC := (proposition_7_9_positive hc C Ξ hΞ hGenerated hNames γ hγ hγ1
    (rvVolumeLift ((degreeOnePointVolumeObject (C.base : Set M)).rescale c hcS hc0))
    ((degreeOnePointVolumeObject (C.base : Set M)).rescale c hcS hc0)).mpr rfl
  have hD := (proposition_7_9_positive hc C Ξ hΞ hGenerated hNames γ hγ hγ1
    (rvVolumeLift ((degreeOnePointVolumeObject (C.base : Set M)).rescale d hdS hd0))
    ((degreeOnePointVolumeObject (C.base : Set M)).rescale d hdS hd0)).mpr rfl
  rw [hC,hD]
  exact rescaled_point_classes_unequal hc C c d hcS hc0 hdS hd0 hAbs

theorem no_ordinary_family_map_recovers_all_point_densities (c d : CanonicalRV.RVSort M)
    (hcS : c.val ∈ C.base) (hc0 : c ≠ 0) (hdS : d.val ∈ C.base) (hd0 : d ≠ 0)
    (hAbs : RVOperations.absoluteHom c ≠ RVOperations.absoluteHom d) :
    ¬ ∃ J : OrdinaryVFVolumeFamily C 1 0 → PositiveVolumeBlowupClasses hc C 0,
      ∀ (e : CanonicalRV.RVSort M) (heS : e.val ∈ C.base) (he0 : e ≠ 0),
        J (rescaledPointLiftOrdinaryFamily C e heS he0)=
          positiveVolumeIntegrationEquiv hc C Ξ hΞ hGenerated hNames γ hγ hγ1
            (positiveVFVolumeIsoClass hc C
              (rvVolumeLift ((degreeOnePointVolumeObject (C.base : Set M)).rescale e heS he0))) := by
  rintro ⟨J,hJ⟩
  have h := congrArg J (rescaled_point_lift_ordinary_family_equal C c d hcS hc0 hdS hd0)
  rw [hJ,hJ] at h
  exact rescaled_point_lift_integrals_unequal hc C Ξ hΞ hGenerated hNames γ hγ hγ1
    c d hcS hc0 hdS hd0 hAbs h
end IntegrationInACVF.Section7
