import Integration7.SelectedVolumeRowContexts
import Integration7.VolumeRelabeling
import Section4.RVIsoTools

/-! Appending the actual density is a definable bijection on each
selected RV fibre. It preserves every selected coordinate and the form. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.DefinableGeometry
namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {C : BaseContext M} {n a k : ℕ}

def SelectedVFVolumeFamily.densityGraphRowMap (F : SelectedVFVolumeFamily C n a k)
    (x : Fin n → VFType (M := M)) :
    Map (F.rowObject x).underlying.obj.domain (F.densityGraph.rowObject x).underlying.obj.domain := by
  let S := (C.base : Set M) ∪ Set.range (fun i => (x i).val)
  let f := (rvAppendMap S a 1).comp
    (((Map.id (F.rowObject x).underlying.obj.domain).pair (F.rowObject x).form.map).toUniv)
  exact f.corestrict (fun r => ⟨⟨(x,r.val),r.property⟩,rfl⟩)

theorem SelectedVFVolumeFamily.densityGraphRowMap_value (F : SelectedVFVolumeFamily C n a k)
    (x : Fin n → VFType (M := M)) (r : (F.rowObject x).underlying.obj.domain) :
    (F.densityGraphRowMap x r).val = Fin.append r.val ((F.rowObject x).form.map r).val := rfl

theorem SelectedVFVolumeFamily.densityGraphRowMap_bijective (F : SelectedVFVolumeFamily C n a k)
    (x : Fin n → VFType (M := M)) : Function.Bijective (F.densityGraphRowMap x) := by
  constructor
  · intro r s hrs
    apply Subtype.ext
    funext i
    have h := congrArg (fun q : (F.densityGraph.rowObject x).underlying.obj.domain => q.val (Fin.castAdd 1 i)) hrs
    simpa only [F.densityGraphRowMap_value,Fin.append_left] using h
  · intro s
    let q : F.densityGraph.domain := ⟨(x,s.val),s.property⟩
    let p := densityGraphProjection F.form q
    have hp := densityGraphProjection_value F.form q
    have hx : p.val.1 = x := congrArg Prod.fst hp
    let r : (F.rowObject x).underlying.obj.domain := ⟨p.val.2,by
      have h := p.property
      change (p.val.1,p.val.2) ∈ F.domain.carrier at h
      rw [hx] at h
      exact h⟩
    refine ⟨r,?_⟩
    have hq := Map.apply_inverse (appendDensityMap F.form).toImage
      (appendDensityMap_toImage_bijective F.form) q
    have hRV := congrArg (fun w : F.densityGraph.domain => w.val.2) hq
    change Fin.append p.val.2 (F.form.map p).val = s.val at hRV
    apply Subtype.ext
    change Fin.append p.val.2 (F.form.map ⟨(x,p.val.2),r.property⟩).val = s.val
    have he : (⟨(x,p.val.2),r.property⟩ : F.domain) = p := Subtype.ext (Prod.ext hx.symm rfl)
    rw [he]
    exact hRV

theorem SelectedVFVolumeFamily.densityGraphRowMap_coordinates (F : SelectedVFVolumeFamily C n a k)
    (x : Fin n → VFType (M := M)) (r : (F.rowObject x).underlying.obj.domain) :
    (F.densityGraph.rowObject x).underlying.obj.value (F.densityGraphRowMap x r) =
      (F.rowObject x).underlying.obj.value r := by
  funext i
  exact Fin.append_left r.val ((F.rowObject x).form.map r).val (F.selected i)

theorem SelectedVFVolumeFamily.densityGraphRowMap_density (F : SelectedVFVolumeFamily C n a k)
    (x : Fin n → VFType (M := M)) (r : (F.rowObject x).underlying.obj.domain) :
    (F.densityGraph.rowObject x).form.value (F.densityGraphRowMap x r) = (F.rowObject x).form.value r := by
  have h := F.densityGraph_form_last ⟨(x,(F.densityGraphRowMap x r).val),(F.densityGraphRowMap x r).property⟩
  exact h.trans (Fin.append_right r.val ((F.rowObject x).form.map r).val 0)

def SelectedVFVolumeFamily.densityGraphRowIso
    (hc : CanonicalStructure.IsCanonical (M := M)) (F : SelectedVFVolumeFamily C n a k)
    (x : Fin n → VFType (M := M)) : RVVolumeIso (F.rowInContext x) (F.densityGraph.rowInContext x) := by
  let h := vfParameterVolumeContext_contains C x
  let f := (F.densityGraphRowMap x).extend h
  have hf : Function.Bijective f := F.densityGraphRowMap_bijective x
  let e := rvFiniteIsoOfAmbient (rvIsoOfVolumePreservingBijection
    (U := (F.rowInContext x).underlying.obj) (V := (F.densityGraph.rowInContext x).underlying.obj)
    f hf (F.densityGraphRowMap_coordinates x))
  exact RVVolumeIso.of_preserving_coordinates_full hc (vfParameterVolumeContext C x) e
    (F.densityGraphRowMap_coordinates x) (F.densityGraphRowMap_density x)

end IntegrationInACVF.Section7
