import Integration7.VFVolumeDensityRescaling
import Integration7.PositiveVolumeIntegrationEquivalence
import Integration7.DefinableVolumeClassRescaling

/-! Named density rescaling descends to actual almost-everywhere VF
volume classes and commutes with the genuine RV volume lift. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.DefinableGeometry
namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {k : ℕ}
variable (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)

def positiveVFVolumeClassRescale (c : CanonicalRV.RVSort M) (hcS : c.val ∈ C.base) (hc0 : c ≠ 0) :
    PositiveVFVolumeIsoClasses hc C k → PositiveVFVolumeIsoClasses hc C k :=
  Quotient.map (fun U => U.rescale c hcS hc0) (fun _ _ ⟨f⟩ => ⟨f.rescale c hcS hc0⟩)

theorem positive_vf_volume_class_rescale_representative
    (c : CanonicalRV.RVSort M) (hcS : c.val ∈ C.base) (hc0 : c ≠ 0)
    (U : PositiveVFVolumeObject (M := M) (C.base : Set M) k) :
    positiveVFVolumeClassRescale hc C c hcS hc0 (positiveVFVolumeIsoClass hc C U)=
      positiveVFVolumeIsoClass hc C (U.rescale c hcS hc0) := rfl

def vfVolumeRescaleLiftBijection
    (U : PositiveRVVolumeObject (M := M) (C.base : Set M) k)
    (c : CanonicalRV.RVSort M) (hcS : c.val ∈ C.base) (hc0 : c ≠ 0) :
    VFVolumeBijection ((rvVolumeLift U).rescale c hcS hc0)
      (rvVolumeLift (U.rescaleDefinable c (Set.Definable.singleton_of_mem LRV hcS) hc0)) := by
  apply VFVolumeBijection.of_preserving_vf_and_density hc C (Map.id _) Function.bijective_id
  · intro p; rfl
  · intro p; rfl
end IntegrationInACVF.Section7
