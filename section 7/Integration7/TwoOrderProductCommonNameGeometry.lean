import Integration7.TwoOrderProductCommonNames
import IntegrationSection5.StandardContractionNormalization

/-! Fixed-name presentations keep the actual final contraction domains
and volume coordinate selectors in both VF orders. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3.GammaParameters SpecialTransformations.Section5
open IntegrationInACVF.Section5 IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7.TwoOrderProductPreparations
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {P : Base (M := M)} {S R : Set M} {d : ℕ}
variable {X Y : DefSet (M := M) S 2 0} {D E : DefSet (M := M) S 1 0}
variable {r t : RV (M := M)} {z : Fin d → RV (M := M)} {hz : ∀ j, (z j).val ∈ S}
variable (F : TwoOrderProductPreparations X Y D E r t z hz P)
variable (hSR : S ⊆ R) (hNames : commonRealNames P ⊆ R)

theorem head_present_target_carrier :
    carrier (F.present hSR hNames).headContraction.target = carrier F.headContraction.target := rfl

theorem tail_present_target_carrier :
    carrier (F.present hSR hNames).tailContraction.target = carrier F.tailContraction.target := rfl

theorem head_present_volume_index :
    (F.present hSR hNames).headContraction.volumeIndex = F.headContraction.volumeIndex := by
  unfold headContraction rvClassProductStandardContraction standardFromProgram StandardContraction.volumeIndex
  rw [orderedCastSource_volumeIndex,orderedCastSource_volumeIndex]
  rfl

theorem tail_present_volume_index :
    (F.present hSR hNames).tailContraction.volumeIndex = F.tailContraction.volumeIndex := by
  unfold tailContraction swappedRVClassProductStandardContraction standardFromProgram StandardContraction.volumeIndex
  rw [orderedCastSource_volumeIndex,orderedCastSource_volumeIndex]
  rfl

theorem head_present_normalized_domain :
    carrier (rvObjectDomain (F.present hSR hNames).headContraction.normalizedObject) =
      carrier (rvObjectDomain F.headContraction.normalizedObject) := by
  unfold StandardContraction.normalizedObject
  rw [head_present_volume_index]
  rfl

theorem tail_present_normalized_domain :
    carrier (rvObjectDomain (F.present hSR hNames).tailContraction.normalizedObject) =
      carrier (rvObjectDomain F.tailContraction.normalizedObject) := by
  unfold StandardContraction.normalizedObject
  rw [tail_present_volume_index]
  rfl

end IntegrationInACVF.Section7.TwoOrderProductPreparations
