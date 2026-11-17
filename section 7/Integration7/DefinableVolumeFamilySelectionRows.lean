module

public import Integration7.DefinableVolumeFamilySelections
public import Integration7.VolumeRelabeling

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! Retaining the volume tuple gives a genuine volume isomorphism on
every actual named RV row. No coordinate or density equation is assumed. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.DefinableGeometry

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {C : BaseContext M} {n a k : ℕ}

def DefinableVFVolumeFamily.selectionRowMap (F : DefinableVFVolumeFamily C n a k)
    (x : Fin n → VFType (M := M)) :
    Map (F.rowInContext x).underlying.obj.domain (F.toSelected.rowInContext x).underlying.obj.domain := by
  let S := ((vfParameterVolumeContext C x).base : Set M)
  let f := (rvAppendMap S a (k+1)).comp
    (((Map.id (F.rowInContext x).underlying.obj.domain).pair (F.rowInContext x).underlying.obj.volume).toUniv)
  exact f.corestrict (fun r => ⟨⟨(x,r.val),r.property⟩,rfl⟩)

theorem DefinableVFVolumeFamily.selectionRowMap_value (F : DefinableVFVolumeFamily C n a k)
    (x : Fin n → VFType (M := M)) (r : (F.rowInContext x).underlying.obj.domain) :
    (F.selectionRowMap x r).val = Fin.append r.val ((F.rowInContext x).underlying.obj.value r) := rfl

theorem DefinableVFVolumeFamily.selectionRowMap_bijective (F : DefinableVFVolumeFamily C n a k)
    (x : Fin n → VFType (M := M)) : Function.Bijective (F.selectionRowMap x) := by
  constructor
  · intro r s h
    apply Subtype.ext
    funext i
    have hi := congrArg (fun q : (F.toSelected.rowInContext x).underlying.obj.domain => q.val (Fin.castAdd (k+1) i)) h
    simpa only [F.selectionRowMap_value,Fin.append_left] using hi
  · intro s
    let q : F.toSelected.domain := ⟨(x,s.val),s.property⟩
    let p := mixedRVMapGraphProjection F.volume q
    have hp := mixed_rv_map_graph_projection_value F.volume q
    have hx := congrArg Prod.fst hp
    change p.val.1=x at hx
    let r : (F.rowInContext x).underlying.obj.domain := ⟨p.val.2,by
      have h := p.property
      change (p.val.1,p.val.2) ∈ F.domain.carrier at h
      rw [hx] at h
      exact h⟩
    have hq := Map.apply_inverse (appendMixedRVMap F.volume).toImage
      (append_mixed_rv_map_to_image_bijective F.volume) q
    have hRV := congrArg (fun w : F.toSelected.domain => w.val.2) hq
    change Fin.append p.val.2 (F.volume p).val = s.val at hRV
    refine ⟨r,Subtype.ext ?_⟩
    change Fin.append p.val.2 (F.volume ⟨(x,p.val.2),r.property⟩).val = s.val
    have he : (⟨(x,p.val.2),r.property⟩ : F.domain)=p := Subtype.ext (Prod.ext hx.symm rfl)
    rw [he]
    exact hRV

theorem DefinableVFVolumeFamily.selectionRowMap_coordinates (F : DefinableVFVolumeFamily C n a k)
    (x : Fin n → VFType (M := M)) (r : (F.rowInContext x).underlying.obj.domain) :
    (F.toSelected.rowInContext x).underlying.obj.value (F.selectionRowMap x r) =
      (F.rowInContext x).underlying.obj.value r := by
  funext i
  exact Fin.append_right r.val ((F.rowInContext x).underlying.obj.value r) i

theorem DefinableVFVolumeFamily.selectionRowMap_density (F : DefinableVFVolumeFamily C n a k)
    (x : Fin n → VFType (M := M)) (r : (F.rowInContext x).underlying.obj.domain) :
    (F.toSelected.rowInContext x).form.value (F.selectionRowMap x r) = (F.rowInContext x).form.value r := by
  change F.form.value (mixedRVMapGraphProjection F.volume ((appendMixedRVMap F.volume).toImage
    ⟨(x,r.val),r.property⟩)) = F.form.value ⟨(x,r.val),r.property⟩
  rw [mixed_rv_map_graph_projection_append]

def DefinableVFVolumeFamily.selectionRowIso
    (hc : CanonicalStructure.IsCanonical (M := M)) (F : DefinableVFVolumeFamily C n a k)
    (x : Fin n → VFType (M := M)) : RVVolumeIso (F.rowInContext x) (F.toSelected.rowInContext x) :=
  RVVolumeIso.of_preserving_coordinates_full hc (vfParameterVolumeContext C x)
    (rvFiniteIsoOfAmbient (rvIsoOfVolumePreservingBijection (F.selectionRowMap x)
      (F.selectionRowMap_bijective x) (F.selectionRowMap_coordinates x)))
    (F.selectionRowMap_coordinates x) (F.selectionRowMap_density x)

end IntegrationInACVF.Section7
