module

public import Integration7.DefinableVolumeFamilyFullLifts

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! Literal carriers and original densities for full family lifts.
Membership realizes the definable volume tuple by the new VF tail and
keeps exactly the old RV labels. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.DefinableGeometry

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {C : BaseContext M} {n a k : ℕ}

theorem DefinableVFVolumeFamily.fullLiftBaseProjection_value
    (F : DefinableVFVolumeFamily C n a k) (p : F.fullLift.domain) :
    (F.fullLiftBaseProjection p).val = (p.val.1 ∘ Fin.castAdd (k+1),p.val.2) := by
  let q := (forgetVolumeGraphLabels F).toImage.inverse (forget_volume_graph_labels_to_image_bijective F) p
  have hq := congrArg Subtype.val
    (Map.apply_inverse (forgetVolumeGraphLabels F).toImage (forget_volume_graph_labels_to_image_bijective F) p)
  change (q.val.1,q.val.2 ∘ Fin.castAdd (k+1)) = p.val at hq
  have hx := congrArg Prod.fst hq
  have hr := congrArg Prod.snd hq
  have hu := mixed_rv_map_graph_projection_value F.volume
    (selectedRVVFTailProjection F.toSelected.domain F.toSelected.selected q)
  change (F.fullLiftBaseProjection p).val = (q.val.1 ∘ Fin.castAdd (k+1),q.val.2 ∘ Fin.castAdd (k+1)) at hu
  exact hu.trans (Prod.ext (congrArg (fun x => x ∘ Fin.castAdd (k+1)) hx) hr)

theorem DefinableVFVolumeFamily.fullLift_volume_constraint
    (F : DefinableVFVolumeFamily C n a k) (p : F.fullLift.domain) :
    tupleRV (p.val.1 ∘ Fin.natAdd n) = (F.volume (F.fullLiftBaseProjection p)).val := by
  let q := (forgetVolumeGraphLabels F).toImage.inverse (forget_volume_graph_labels_to_image_bijective F) p
  have hq := congrArg Subtype.val
    (Map.apply_inverse (forgetVolumeGraphLabels F).toImage (forget_volume_graph_labels_to_image_bijective F) p)
  change (q.val.1,q.val.2 ∘ Fin.castAdd (k+1)) = p.val at hq
  have hx := congrArg Prod.fst hq
  have ht := ((mem_selected_rv_vf_tail_lift F.toSelected.domain F.toSelected.selected q.val).mp q.property).2
  have hv := mixed_rv_map_graph_retained_tuple F.volume
    (selectedRVVFTailProjection F.toSelected.domain F.toSelected.selected q)
  change (F.volume (F.fullLiftBaseProjection p)).val = q.val.2 ∘ Fin.natAdd a at hv
  exact (congrArg (fun x => tupleRV (x ∘ Fin.natAdd n)) hx).symm.trans (ht.trans hv.symm)

theorem mem_definable_volume_family_full_lift
    (F : DefinableVFVolumeFamily C n a k)
    (x : Fin (n+(k+1)) → VFType (M := M)) (r : Fin a → CanonicalRV.RVSort M) :
    (x,r) ∈ F.fullLift.domain.carrier ↔
      ∃ p : F.domain, p.val=(x ∘ Fin.castAdd (k+1),r) ∧
        tupleRV (x ∘ Fin.natAdd n) = (F.volume p).val := by
  constructor
  · intro h
    let p : F.fullLift.domain := ⟨(x,r),h⟩
    exact ⟨F.fullLiftBaseProjection p,F.fullLiftBaseProjection_value p,F.fullLift_volume_constraint p⟩
  · rintro ⟨p,hp,ht⟩
    have hx := congrArg Prod.fst hp
    have hr := congrArg Prod.snd hp
    have hGraph : (x ∘ Fin.castAdd (k+1),Fin.append r (F.volume p).val) ∈ F.toSelected.domain.carrier := by
      refine ⟨p,?_⟩
      change (p.val.1,Fin.append p.val.2 (F.volume p).val) = _
      exact Prod.ext hx (congrArg (fun s => Fin.append s (F.volume p).val) hr)
    have hLift : (x,Fin.append r (F.volume p).val) ∈ F.toSelected.fullLift.domain.carrier := by
      apply (mem_selected_rv_vf_tail_lift F.toSelected.domain F.toSelected.selected _).mpr
      refine ⟨hGraph,?_⟩
      change tupleRV (x ∘ Fin.natAdd n) = Fin.append r (F.volume p).val ∘ Fin.natAdd a
      simpa only [Function.comp_def,Fin.append_right] using ht
    refine ⟨⟨(x,Fin.append r (F.volume p).val),hLift⟩,?_⟩
    change (x,Fin.append r (F.volume p).val ∘ Fin.castAdd (k+1)) = (x,r)
    exact Prod.ext rfl (funext (Fin.append_left _ _))

end IntegrationInACVF.Section7
