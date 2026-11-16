module

public import Integration7.SelectedVolumeRowContexts
public import Integration7.RVCoordinateSelection

@[expose] public section

/-! Positive homogeneous volume families with an arbitrary definable
RV volume map. The finite condition fixes both the VF base and the volume
tuple, so it includes selected-coordinate families and tagged coproducts. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.DefinableGeometry

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n a k : ℕ}

structure DefinableVFVolumeFamily (C : BaseContext M) (n a k : ℕ) where
  domain : DefSet (rawMixedSpace (M := M) n a) (C.base : Set M)
  volume : Map domain (DefSet.univ (rawRVSpace (M := M) (k+1)) (C.base : Set M))
  finite_volume : ∀ (x : Fin n → VFType (M := M)) (t : Fin (k+1) → CanonicalRV.RVSort M),
    {r : Fin a → CanonicalRV.RVSort M | ∃ p : domain, p.val=(x,r) ∧ (volume p).val=t}.Finite
  form : VolumeForm domain

def SelectedVFVolumeFamily.toDefinable {C : BaseContext M} (F : SelectedVFVolumeFamily C n a k) :
    DefinableVFVolumeFamily C n a k where
  domain := F.domain
  volume := (rvCoordinateSelectMap (C.base : Set M) F.selected).comp
    (Map.snd (rawVFSpace n) (rawRVSpace a) (C.base : Set M) F.domain)
  finite_volume x t := (F.finite_selected x t).subset (by
    rintro r ⟨p,hp,ht⟩
    refine ⟨hp ▸ p.property,?_⟩
    change p.val.2 ∘ F.selected = t at ht
    have hr := congrArg Prod.snd hp
    rw [hr] at ht
    exact ht)
  form := F.form

def DefinableVFVolumeFamily.rowObject {C : BaseContext M} (F : DefinableVFVolumeFamily C n a k)
    (x : Fin n → VFType (M := M)) :
    PositiveRVVolumeObject (M := M) ((C.base : Set M) ∪ Set.range (fun i => (x i).val)) k where
  underlying := {
    obj := ⟨a,vfRVFibre F.domain x,
      (F.volume.extend Set.subset_union_left).comp (vfRVFibreEmbed F.domain x)⟩
    property := by
      intro t
      apply (F.finite_volume x t.val).of_injOn (f := fun r : vfRVFibre F.domain x => r.val)
      · intro r hr
        exact ⟨⟨(x,r.val),r.property⟩,rfl,congrArg Subtype.val hr⟩
      · intro r hr s hs he
        exact Subtype.ext he }
  form := F.form.vfRVFibre x

def DefinableVFVolumeFamily.rowInContext {C : BaseContext M} (F : DefinableVFVolumeFamily C n a k)
    (x : Fin n → VFType (M := M)) :
    PositiveRVVolumeObject (M := M) ((vfParameterVolumeContext C x).base : Set M) k :=
  (F.rowObject x).extend (vfParameterVolumeContext_contains C x)

@[simp] theorem DefinableVFVolumeFamily.rowInContext_volume {C : BaseContext M}
    (F : DefinableVFVolumeFamily C n a k) (x : Fin n → VFType (M := M))
    (r : (F.rowInContext x).underlying.obj.domain) :
    (F.rowInContext x).underlying.obj.value r = (F.volume ⟨(x,r.val),r.property⟩).val := rfl

@[simp] theorem DefinableVFVolumeFamily.rowInContext_density {C : BaseContext M}
    (F : DefinableVFVolumeFamily C n a k) (x : Fin n → VFType (M := M))
    (r : (F.rowInContext x).underlying.obj.domain) :
    (F.rowInContext x).form.value r = F.form.value ⟨(x,r.val),r.property⟩ := rfl

end IntegrationInACVF.Section7
