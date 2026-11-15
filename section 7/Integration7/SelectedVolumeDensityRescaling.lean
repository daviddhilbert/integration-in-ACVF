import Integration7.VFVolumeDensityRescaling
import Integration7.DefinableVolumeClassRescaling
import Integration7.AERVVolumeFunctions

/-! Named nonzero density multipliers on actual selected families and
their AE quotient. The original domain, selected labels and all finite
selected fibres are retained. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.DefinableGeometry
namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {C : BaseContext M} {n a b k : ℕ}

def SelectedVFVolumeFamily.rescale (F : SelectedVFVolumeFamily C n a k)
    (c : CanonicalRV.RVSort M) (hcS : c.val ∈ C.base) (hc0 : c ≠ 0) : SelectedVFVolumeFamily C n a k where
  domain := F.domain
  selected := F.selected
  finite_selected := F.finite_selected
  form := F.form.rescale c hcS hc0

def rescaledSelectedFamilyRowIso
    (hc : CanonicalStructure.IsCanonical (M := M)) (F : SelectedVFVolumeFamily C n a k)
    (c : CanonicalRV.RVSort M) (hcS : c.val ∈ C.base) (hc0 : c ≠ 0)
    (x : Fin n → VFType (M := M)) :
    RVVolumeIso ((F.rescale c hcS hc0).rowInContext x)
      ((F.rowInContext x).rescaleDefinable c
        (Set.Definable.singleton_of_mem LRV ((vfParameterVolumeContext_contains C x) (Or.inl hcS))) hc0) :=
  RVVolumeIso.of_preserving_coordinates_full hc (vfParameterVolumeContext C x)
    (Iso.refl (F.rowInContext x).underlying) (fun _ => rfl) (fun _ => rfl)

theorem selected_volume_rescale_row_class
    (hc : CanonicalStructure.IsCanonical (M := M)) (F : SelectedVFVolumeFamily C n a k)
    (c : CanonicalRV.RVSort M) (hcS : c.val ∈ C.base) (hc0 : c ≠ 0)
    (x : Fin n → VFType (M := M)) :
    positiveVolumeBlowupClass hc (vfParameterVolumeContext C x) ((F.rescale c hcS hc0).rowInContext x)=
    positiveVolumeClassRescaleDefinable hc (vfParameterVolumeContext C x) c
      (Set.Definable.singleton_of_mem LRV ((vfParameterVolumeContext_contains C x) (Or.inl hcS))) hc0
      (positiveVolumeBlowupClass hc (vfParameterVolumeContext C x) (F.rowInContext x)) :=
  positiveVolumeBlowupClass_iso hc (vfParameterVolumeContext C x) (rescaledSelectedFamilyRowIso hc F c hcS hc0 x)

theorem ae_selected_volume_density_rescale
    (hc : CanonicalStructure.IsCanonical (M := M)) (F : SelectedVFVolumeFamily C (n+1) a k)
    (G : SelectedVFVolumeFamily C (n+1) b k) (c : CanonicalRV.RVSort M)
    (hcS : c.val ∈ C.base) (hc0 : c ≠ 0)
    (h : AERVVolumeFunctionEquivalent hc C ⟨a,F⟩ ⟨b,G⟩) :
    AERVVolumeFunctionEquivalent hc C ⟨a,F.rescale c hcS hc0⟩ ⟨b,G.rescale c hcS hc0⟩ := by
  obtain ⟨E,hE,hRows⟩ := h
  refine ⟨E,hE,?_⟩
  intro x hx
  rw [selected_volume_rescale_row_class,selected_volume_rescale_row_class,hRows _ hx]

def aeRVVolumeFunctionRescale (hc : CanonicalStructure.IsCanonical (M := M))
    (C : BaseContext M) (c : CanonicalRV.RVSort M) (hcS : c.val ∈ C.base) (hc0 : c ≠ 0) :
    AERVVolumeFunction hc C n k → AERVVolumeFunction hc C n k :=
  Quotient.map (fun F => ⟨F.1,F.2.rescale c hcS hc0⟩)
    (fun F G h => ae_selected_volume_density_rescale hc F.2 G.2 c hcS hc0 h)
end IntegrationInACVF.Section7
