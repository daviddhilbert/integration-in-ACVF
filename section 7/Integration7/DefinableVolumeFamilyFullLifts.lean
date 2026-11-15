import Integration7.DefinableVolumeFamilySelections
import Integration7.SelectedFamilyFullLifts
import Integration7.VFVolumeBijections

/-! Full VF realizations of arbitrary definable positive volume maps.
The selected presentation adds graph labels; the full lift below forgets
those redundant labels through a definable bijection preserving every VF
coordinate and the original density. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.DefinableGeometry

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {C : BaseContext M} {n a k : ℕ}

def forgetVolumeGraphLabels (F : DefinableVFVolumeFamily C n a k) :
    Map F.toSelected.fullLift.domain
      (DefSet.univ (rawMixedSpace (M := M) (n+(k+1)) a) (C.base : Set M)) :=
  (Map.prodUnivMap (Map.id (DefSet.univ (rawVFSpace (M := M) (n+(k+1))) (C.base : Set M)))
    (rvCoordinateSelectMap (C.base : Set M) (Fin.castAdd (k+1) : Fin a → Fin (a+(k+1))))).comp
      (Map.id F.toSelected.fullLift.domain).toUniv

@[simp] theorem forget_volume_graph_labels_value
    (F : DefinableVFVolumeFamily C n a k) (q : F.toSelected.fullLift.domain) :
    (forgetVolumeGraphLabels F q).val = (q.val.1,q.val.2 ∘ Fin.castAdd (k+1)) := rfl

theorem forget_volume_graph_labels_injective (F : DefinableVFVolumeFamily C n a k) :
    Function.Injective (forgetVolumeGraphLabels F) := by
  intro p q he
  have h := congrArg Subtype.val he
  change (p.val.1,p.val.2 ∘ Fin.castAdd (k+1)) =
    (q.val.1,q.val.2 ∘ Fin.castAdd (k+1)) at h
  have hp := ((mem_selected_rv_vf_tail_lift F.toSelected.domain F.toSelected.selected p.val).mp p.property).2
  have hq := ((mem_selected_rv_vf_tail_lift F.toSelected.domain F.toSelected.selected q.val).mp q.property).2
  have hx := congrArg Prod.fst h
  have hr := congrArg Prod.snd h
  apply Subtype.ext
  refine Prod.ext hx ?_
  funext i
  refine Fin.addCases (m := a) (n := k+1) (fun j => ?_) (fun j => ?_) i
  · exact congrFun hr j
  · change p.val.2 (Fin.natAdd a j) = q.val.2 (Fin.natAdd a j)
    exact (congrFun hp j).symm.trans
      ((congrArg (fun x => tupleRV (x ∘ Fin.natAdd n) j) hx).trans (congrFun hq j))

theorem forget_volume_graph_labels_to_image_bijective (F : DefinableVFVolumeFamily C n a k) :
    Function.Bijective (forgetVolumeGraphLabels F).toImage := by
  constructor
  · intro p q he
    have hv := congrArg Subtype.val he
    exact forget_volume_graph_labels_injective F (Subtype.ext hv)
  · rintro ⟨q,p,hp⟩
    exact ⟨p,Subtype.ext hp⟩

def DefinableVFVolumeFamily.fullLift (F : DefinableVFVolumeFamily C n a k) :
    PositiveVFVolumeObject (M := M) (C.base : Set M) (n+k) where
  arity := a
  domain := (forgetVolumeGraphLabels F).image
  finite_labels x := by
    apply ((F.toSelected.fullLift.finite_labels x).image (fun r => r ∘ Fin.castAdd (k+1))).subset
    rintro r ⟨p,hp⟩
    change (p.val.1,p.val.2 ∘ Fin.castAdd (k+1)) = (x,r) at hp
    have hx := congrArg Prod.fst hp
    refine ⟨p.val.2,?_,congrArg Prod.snd hp⟩
    exact Eq.mp (congrArg (fun y => (y,p.val.2) ∈ F.toSelected.fullLift.domain.carrier) hx) p.property
  form := F.toSelected.fullLift.form.pullback
    ((forgetVolumeGraphLabels F).toImage.inverse (forget_volume_graph_labels_to_image_bijective F))

def definableVolumeFamilySelectionLiftBijection
    (hc : CanonicalStructure.IsCanonical (M := M)) (F : DefinableVFVolumeFamily C n a k) :
    VFVolumeBijection F.toSelected.fullLift F.fullLift :=
  VFVolumeBijection.of_preserving_vf_and_density hc C (forgetVolumeGraphLabels F).toImage
    (forget_volume_graph_labels_to_image_bijective F) (fun _ => rfl) (fun p => by
      change F.toSelected.fullLift.form.value p = F.toSelected.fullLift.form.value
        ((forgetVolumeGraphLabels F).toImage.inverse (forget_volume_graph_labels_to_image_bijective F)
          ((forgetVolumeGraphLabels F).toImage p))
      rw [Map.inverse_apply])

def DefinableVFVolumeFamily.fullLiftBaseProjection (F : DefinableVFVolumeFamily C n a k) :
    Map F.fullLift.domain F.domain :=
  (mixedRVMapGraphProjection F.volume).comp
    ((selectedRVVFTailProjection F.toSelected.domain F.toSelected.selected).comp
      ((forgetVolumeGraphLabels F).toImage.inverse (forget_volume_graph_labels_to_image_bijective F)))

@[simp] theorem DefinableVFVolumeFamily.fullLift_density
    (F : DefinableVFVolumeFamily C n a k) (p : F.fullLift.domain) :
    F.fullLift.form.value p = F.form.value (F.fullLiftBaseProjection p) := rfl

end IntegrationInACVF.Section7
