import IntegrationSection6.FiniteSelectedContractions

/-! First-volume normalization preserves the entire selected volume tuple
of a standard contraction, including the old labels, literally. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
open IntegrationInACVF.Section5
namespace IntegrationInACVF.Section6
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {S : Set M} {n a k : ℕ}
variable {U : DefSet (M := M) S n a} {σ : Equiv.Perm (Fin n)}

theorem rawSelectedNormalization_volume (C : StandardContraction U σ) (ρ : Fin k → Fin a)
    (u : rvObjectDomain C.contractionObject) :
    (rvObjectVolume (appendSelectedVolumeObject C.normalizedObject (fun j => FiniteRV.contractionOldLabelIndex C (ρ j)))
      (toFirstVolume (Map.image (rawLabelMap C.target)) C.volumeIndex u)).val =
    (rvObjectVolume (appendSelectedVolumeObject C.contractionObject (fun j => suffixIndex C.program.rvArity_le (ρ j))) u).val := by
  rw [appendSelectedVolumeObject_value,appendSelectedVolumeObject_value]
  apply congrArg₂ Fin.append
  · exact toFirstVolume_volume _ _ _
  · funext j
    exact toFirstVolume_oldLabels _ _ _ _

end IntegrationInACVF.Section6
