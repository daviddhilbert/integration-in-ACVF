module

public import Integration7.DefinableAppendedFamilyLifts

@[expose] public section

/-! Coefficient-first full lifts of arbitrary volume maps have the
literal original base point and realize the original volume tuple in
the front VF block. No extra graph labels remain. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.DefinableGeometry

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {C : BaseContext M} {n a k : ℕ}

theorem DefinableVFVolumeFamily.appendedLiftBaseProjection_value
    (F : DefinableVFVolumeFamily C n a k) (p : F.appendedFullLift.domain) :
    (F.appendedLiftBaseProjection p).val = (appendedFamilyBaseCoordinates n k p.val.1,p.val.2) := by
  let q := (forgetAppendedVolumeGraphLabels F).toImage.inverse
    (vf_label_image_to_image_bijective _ (forget_appended_volume_graph_labels_injective F)) p
  have hq := congrArg Subtype.val (Map.apply_inverse (forgetAppendedVolumeGraphLabels F).toImage
    (vf_label_image_to_image_bijective _ (forget_appended_volume_graph_labels_injective F)) p)
  change (q.val.1,q.val.2 ∘ Fin.castAdd (k+1))=p.val at hq
  have hx := congrArg Prod.fst hq
  have hr := congrArg Prod.snd hq
  have h := mixed_rv_map_graph_projection_value F.volume (F.toSelected.appendedLiftBaseProjection q)
  change (F.appendedLiftBaseProjection p).val =
    (appendedFamilyBaseCoordinates n k q.val.1,q.val.2 ∘ Fin.castAdd (k+1)) at h
  exact h.trans (Prod.ext (congrArg (appendedFamilyBaseCoordinates n k) hx) hr)

theorem DefinableVFVolumeFamily.appendedLift_volume_constraint
    (F : DefinableVFVolumeFamily C n a k) (p : F.appendedFullLift.domain) :
    tupleRV (appendedFamilyCoefficientCoordinates n k p.val.1) =
      (F.volume (F.appendedLiftBaseProjection p)).val := by
  let q := (forgetAppendedVolumeGraphLabels F).toImage.inverse
    (vf_label_image_to_image_bijective _ (forget_appended_volume_graph_labels_injective F)) p
  have hq := congrArg Subtype.val (Map.apply_inverse (forgetAppendedVolumeGraphLabels F).toImage
    (vf_label_image_to_image_bijective _ (forget_appended_volume_graph_labels_injective F)) p)
  change (q.val.1,q.val.2 ∘ Fin.castAdd (k+1))=p.val at hq
  have hx := congrArg Prod.fst hq
  have ht := ((mem_appended_family_full_lift F.toSelected q.val.1 q.val.2).mp q.property).2
  have hv := mixed_rv_map_graph_retained_tuple F.volume (F.toSelected.appendedLiftBaseProjection q)
  change (F.volume (F.appendedLiftBaseProjection p)).val=q.val.2 ∘ Fin.natAdd a at hv
  exact (congrArg (fun x => tupleRV (appendedFamilyCoefficientCoordinates n k x)) hx).symm.trans (ht.trans hv.symm)

theorem mem_definable_appended_family_lift
    (F : DefinableVFVolumeFamily C n a k)
    (x : Fin (appendVolumeDegree n k+1) → VFType (M := M)) (r : Fin a → CanonicalRV.RVSort M) :
    (x,r) ∈ F.appendedFullLift.domain.carrier ↔
      ∃ p : F.domain, p.val=(appendedFamilyBaseCoordinates n k x,r) ∧
        tupleRV (appendedFamilyCoefficientCoordinates n k x)=(F.volume p).val := by
  constructor
  · intro hp
    let p : F.appendedFullLift.domain := ⟨(x,r),hp⟩
    exact ⟨F.appendedLiftBaseProjection p,F.appendedLiftBaseProjection_value p,F.appendedLift_volume_constraint p⟩
  · rintro ⟨p,hp,ht⟩
    have hx := congrArg Prod.fst hp
    have hr := congrArg Prod.snd hp
    have hGraph : (appendedFamilyBaseCoordinates n k x,Fin.append r (F.volume p).val) ∈ F.toSelected.domain.carrier := by
      refine ⟨p,?_⟩
      change (p.val.1,Fin.append p.val.2 (F.volume p).val)=_
      exact Prod.ext hx (congrArg (fun s => Fin.append s (F.volume p).val) hr)
    have hLift : (x,Fin.append r (F.volume p).val) ∈ F.toSelected.appendedFullLift.domain.carrier := by
      apply (mem_appended_family_full_lift F.toSelected _ _).mpr
      refine ⟨hGraph,?_⟩
      change tupleRV (appendedFamilyCoefficientCoordinates n k x)=Fin.append r (F.volume p).val ∘ Fin.natAdd a
      simpa only [Function.comp_def,Fin.append_right] using ht
    refine ⟨⟨(x,Fin.append r (F.volume p).val),hLift⟩,?_⟩
    change (x,Fin.append r (F.volume p).val ∘ Fin.castAdd (k+1))=(x,r)
    exact Prod.ext rfl (funext (Fin.append_left _ _))

end IntegrationInACVF.Section7
