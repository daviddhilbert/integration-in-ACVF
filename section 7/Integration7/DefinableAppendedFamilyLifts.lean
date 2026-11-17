module

public import Integration7.AppendedFamilyLiftCoordinates
public import Integration7.VFVolumePreservingLabelImages
public import Integration7.DefinableVolumeFamilySelections

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! Coefficient-first realizations for arbitrary definable volume maps.
Redundant selected-presentation graph labels are forgotten by an actual
VF-preserving volume bijection, retaining the original family density. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.DefinableGeometry

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {C : BaseContext M} {n a k : ℕ}

def SelectedVFVolumeFamily.appendedLiftBaseProjection (F : SelectedVFVolumeFamily C n a k) :
    Map F.appendedFullLift.domain F.domain :=
  (vfSelect ((finCongr (append_volume_length_eq n k)).symm ∘ Fin.natAdd (k+1)) F.appendedFullLift.domain).corestrict
    (fun q => ((mem_appended_family_full_lift F q.val.1 q.val.2).mp q.property).1)

theorem SelectedVFVolumeFamily.appendedLiftBaseProjection_value
    (F : SelectedVFVolumeFamily C n a k) (q : F.appendedFullLift.domain) :
    (F.appendedLiftBaseProjection q).val = (appendedFamilyBaseCoordinates n k q.val.1,q.val.2) := rfl

def forgetAppendedVolumeGraphLabels (F : DefinableVFVolumeFamily C n a k) :
    Map F.toSelected.appendedFullLift.domain
      (DefSet.univ (rawMixedSpace (M := M) (appendVolumeDegree n k+1) a) (C.base : Set M)) :=
  (Map.prodUnivMap (Map.id (DefSet.univ (rawVFSpace (M := M) (appendVolumeDegree n k+1)) (C.base : Set M)))
    (rvCoordinateSelectMap (C.base : Set M) (Fin.castAdd (k+1) : Fin a → Fin (a+(k+1))))).comp
      (Map.id F.toSelected.appendedFullLift.domain).toUniv

theorem forget_appended_volume_graph_labels_injective (F : DefinableVFVolumeFamily C n a k) :
    Function.Injective (forgetAppendedVolumeGraphLabels F) := by
  intro q r he
  have h := congrArg Subtype.val he
  change (q.val.1,q.val.2 ∘ Fin.castAdd (k+1)) = (r.val.1,r.val.2 ∘ Fin.castAdd (k+1)) at h
  have hx := congrArg Prod.fst h
  have hr := congrArg Prod.snd h
  have hq := ((mem_appended_family_full_lift F.toSelected q.val.1 q.val.2).mp q.property).2
  have hs := ((mem_appended_family_full_lift F.toSelected r.val.1 r.val.2).mp r.property).2
  apply Subtype.ext
  refine Prod.ext hx ?_
  funext i
  refine Fin.addCases (m := a) (n := k+1) (fun j => ?_) (fun j => ?_) i
  · exact congrFun hr j
  · change q.val.2 (Fin.natAdd a j)=r.val.2 (Fin.natAdd a j)
    exact (congrFun hq j).symm.trans
      ((congrArg (fun x => tupleRV (appendedFamilyCoefficientCoordinates n k x) j) hx).trans (congrFun hs j))

def DefinableVFVolumeFamily.appendedFullLift (F : DefinableVFVolumeFamily C n a k) :
    PositiveVFVolumeObject (M := M) (C.base : Set M) (appendVolumeDegree n k) :=
  F.toSelected.appendedFullLift.vfPreservingImage (forgetAppendedVolumeGraphLabels F)
    (forget_appended_volume_graph_labels_injective F) (fun _ => rfl)

def definableVolumeFamilyAppendedSelectionBijection
    (hc : CanonicalStructure.IsCanonical (M := M)) (F : DefinableVFVolumeFamily C n a k) :
    VFVolumeBijection F.toSelected.appendedFullLift F.appendedFullLift :=
  vfPreservingLabelImageBijection hc C F.toSelected.appendedFullLift (forgetAppendedVolumeGraphLabels F)
    (forget_appended_volume_graph_labels_injective F) (fun _ => rfl)

def DefinableVFVolumeFamily.appendedLiftBaseProjection (F : DefinableVFVolumeFamily C n a k) :
    Map F.appendedFullLift.domain F.domain :=
  (mixedRVMapGraphProjection F.volume).comp (F.toSelected.appendedLiftBaseProjection.comp
    ((forgetAppendedVolumeGraphLabels F).toImage.inverse
      (vf_label_image_to_image_bijective _ (forget_appended_volume_graph_labels_injective F))))

theorem DefinableVFVolumeFamily.appendedFullLift_density
    (F : DefinableVFVolumeFamily C n a k) (q : F.appendedFullLift.domain) :
    F.appendedFullLift.form.value q = F.form.value (F.appendedLiftBaseProjection q) :=
  F.toSelected.appendedFullLift_density _

end IntegrationInACVF.Section7
