module

public import Integration7.VolumeBlowupLiftInvariance
public import Integration7.VFVolumeClasses
public import Integration7.VolumeBlowupClasses

@[expose] public section

/-! The VF lift descends through the proved common-volume-blowup
relation. Injectivity, the converse of Proposition 7.8, is not assumed. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {k : ℕ}

theorem positive_lift_class_eq_of_common_volume_blowup
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (Ξ : Set (Values.Gamma (M := M)))
    (hGenerated : VFGammaGeneratedBase (⟨(C.base : Set M),Ξ⟩ : Base (M := M)))
    {U V : PositiveRVVolumeObject (M := M) (C.base : Set M) k}
    (h : VolumeBlowupEquivalent U V) :
    positiveVFVolumeIsoClass hc C (rvVolumeLift U) =
      positiveVFVolumeIsoClass hc C (rvVolumeLift V) :=
  (positiveVFVolumeIsoClass_eq_iff hc C).mpr (h.nonempty_volume_lift_iso hc C Ξ hGenerated)

def positiveVolumeLiftOnBlowupClasses
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M) (k : ℕ)
    (Ξ : Set (Values.Gamma (M := M)))
    (hGenerated : VFGammaGeneratedBase (⟨(C.base : Set M),Ξ⟩ : Base (M := M))) :
    PositiveVolumeBlowupClasses hc C k → PositiveVFVolumeIsoClasses hc C k :=
  Quotient.lift (fun U => positiveVFVolumeIsoClass hc C (rvVolumeLift U))
    (fun _ _ h => positive_lift_class_eq_of_common_volume_blowup hc C Ξ hGenerated h)

@[simp] theorem positiveVolumeLiftOnBlowupClasses_class
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M) (k : ℕ)
    (Ξ : Set (Values.Gamma (M := M)))
    (hGenerated : VFGammaGeneratedBase (⟨(C.base : Set M),Ξ⟩ : Base (M := M)))
    (U : PositiveRVVolumeObject (M := M) (C.base : Set M) k) :
    positiveVolumeLiftOnBlowupClasses hc C k Ξ hGenerated (positiveVolumeBlowupClass hc C U) =
      positiveVFVolumeIsoClass hc C (rvVolumeLift U) := rfl

end IntegrationInACVF.Section7
