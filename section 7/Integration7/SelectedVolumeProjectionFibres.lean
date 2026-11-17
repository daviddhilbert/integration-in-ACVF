module

public import Integration7.SelectedVolumeRowContexts
public import Integration7.IndexedVolumeEmpty
public import Integration7.IteratedVolumeBlowups

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! Fibrewise common blowups need only be supplied on the common VF
projection. All other fibres are genuinely empty and compare directly. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section4

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {C : BaseContext M} {n a b k : ℕ}

def SelectedVFVolumeFamily.vfProjection (F : SelectedVFVolumeFamily C n a k) :
    Set (Fin n → VFType (M := M)) := {x | ∃ r, (x,r) ∈ F.domain.carrier}

theorem SelectedVFVolumeFamily.rowInContext_empty_of_not_projection
    (F : SelectedVFVolumeFamily C n a k) (x : Fin n → VFType (M := M))
    (hx : x ∉ F.vfProjection) : (F.rowInContext x).underlying.obj.domain.carrier = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro r hr
  exact hx ⟨r,hr⟩

theorem selected_volume_common_on_projection
    (hc : CanonicalStructure.IsCanonical (M := M))
    (F : SelectedVFVolumeFamily C n a k) (G : SelectedVFVolumeFamily C n b k)
    (hProjection : F.vfProjection = G.vfProjection)
    (hCommon : ∀ x ∈ F.vfProjection, VolumeBlowupEquivalent (F.rowInContext x) (G.rowInContext x)) :
    ∀ x, VolumeBlowupEquivalent (F.rowInContext x) (G.rowInContext x) := by
  intro x
  by_cases hx : x ∈ F.vfProjection
  · exact hCommon x hx
  · have hxG : x ∉ G.vfProjection := hProjection ▸ hx
    exact VolumeBlowupEquivalent.of_iso (vfParameterVolumeContext C x)
      (RVVolumeIso.of_empty hc (vfParameterVolumeContext C x) _ _
        (F.rowInContext_empty_of_not_projection x hx) (G.rowInContext_empty_of_not_projection x hxG))

end IntegrationInACVF.Section7
