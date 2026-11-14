import Integration7.GammaVolumeDensityRescaling
import Integration7.VolumeBlowupRightProducts

/-! Degree reindexing retains original-Gamma common blowup geometry. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {S : Set M} {a b : ℕ}

theorem VolumeObjectGamma.reindexDegree
    {U : PositiveRVVolumeObject (M := M) S b} (hU : VolumeObjectGamma U B) (h : a=b) :
    VolumeObjectGamma (U.reindexDegree h) B := by
  cases h
  exact ⟨hU.coordinates.congr (fun _ => by funext i; rfl),hU.density⟩

def GammaVolumeObjects.reindexDegree (U : GammaVolumeObjects B S b) (h : a=b) :
    GammaVolumeObjects B S a := ⟨U.val.reindexDegree h,U.property.reindexDegree h⟩

theorem GammaVolumeBlowupEquivalent.reindexDegree
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    {U V : GammaVolumeObjects B (C.base : Set M) b}
    (g : GammaVolumeBlowupEquivalent B (C.base : Set M) b U V) (h : a=b) :
    GammaVolumeBlowupEquivalent B (C.base : Set M) a (U.reindexDegree h) (V.reindexDegree h) := by
  cases h
  have hU := gamma_volume_iso_of_label_identity hc (volumeCastReindexIso hc C U.val rfl)
    (U.property.reindexDegree rfl) rfl (fun _ => rfl)
  have hV := gamma_volume_iso_of_label_identity hc (volumeCastReindexIso hc C V.val rfl)
    (V.property.reindexDegree rfl) rfl (fun _ => rfl)
  exact ((GammaVolumeBlowupEquivalent.of_iso C B _ hU).trans hc C B g).trans hc C B
    (GammaVolumeBlowupEquivalent.of_iso C B _ (hV.symm hc C B))

end IntegrationInACVF.Section7
