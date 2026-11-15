import Integration7.VolumeFamilyCoproductRowIsomorphisms
import Integration7.DefinableVolumeFamilySelectionRows
import Integration7.IndexedVolumeEmpty

/-! Actual selected-family representatives of zero and fibrewise
addition. Tagged disjoint unions are converted back to selected labels
by retaining their genuine volume tuple. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.DefinableGeometry

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {C : BaseContext M} {n a b k : ℕ}

def selectedToDefinableVolumeRowIso
    (hc : CanonicalStructure.IsCanonical (M := M)) (F : SelectedVFVolumeFamily C n a k)
    (x : Fin n → VFType (M := M)) : RVVolumeIso (F.rowInContext x) (F.toDefinable.rowInContext x) :=
  RVVolumeIso.of_preserving_coordinates_full hc (vfParameterVolumeContext C x)
    (rvFiniteIsoOfAmbient (rvIsoOfVolumePreservingBijection (Map.id _) Function.bijective_id (fun _ => rfl)))
    (fun _ => rfl) (fun _ => rfl)

def selectedVolumeFamilySum (F : SelectedVFVolumeFamily C n a k) (G : SelectedVFVolumeFamily C n b k) :
    SelectedVFVolumeFamily C n ((1+(a+b))+(k+1)) k := (F.toDefinable.coprod G.toDefinable).toSelected

theorem selected_volume_family_sum_row_class
    (hc : CanonicalStructure.IsCanonical (M := M))
    (F : SelectedVFVolumeFamily C n a k) (G : SelectedVFVolumeFamily C n b k)
    (x : Fin n → VFType (M := M)) :
    positiveVolumeBlowupClass hc (vfParameterVolumeContext C x) ((selectedVolumeFamilySum F G).rowInContext x) =
      positiveVolumeBlowupClass hc (vfParameterVolumeContext C x) (F.rowInContext x) +
        positiveVolumeBlowupClass hc (vfParameterVolumeContext C x) (G.rowInContext x) := by
  let D := vfParameterVolumeContext C x
  have hSelection := positiveVolumeBlowupClass_iso hc D ((F.toDefinable.coprod G.toDefinable).selectionRowIso hc x)
  have hSum := volume_family_coprod_row_class hc F.toDefinable G.toDefinable x
  have hF := positiveVolumeBlowupClass_iso hc D (selectedToDefinableVolumeRowIso hc F x)
  have hG := positiveVolumeBlowupClass_iso hc D (selectedToDefinableVolumeRowIso hc G x)
  exact hSelection.symm.trans (hSum.trans (congrArg₂ (fun y z => y+z) hF.symm hG.symm))

def selectedZeroVolumeFamily (C : BaseContext M) (n k : ℕ) : SelectedVFVolumeFamily C n (k+1) k where
  domain := DefSet.empty (rawMixedSpace (M := M) n (k+1)) (C.base : Set M)
  selected := id
  finite_selected _ _ := Set.finite_empty.subset (fun _ h => h.1)
  form := VolumeForm.one _

theorem selected_zero_volume_family_row_class
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M) (n k : ℕ)
    (x : Fin n → VFType (M := M)) :
    positiveVolumeBlowupClass hc (vfParameterVolumeContext C x) ((selectedZeroVolumeFamily C n k).rowInContext x) = 0 :=
  positiveVolumeBlowupClass_iso hc (vfParameterVolumeContext C x)
    (RVVolumeIso.of_empty hc (vfParameterVolumeContext C x) _ _ rfl rfl)

end IntegrationInACVF.Section7
