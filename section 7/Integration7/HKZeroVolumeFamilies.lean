module

public import Integration7.HKRVVolumeProducts
public import Integration7.OrdinaryVFVolumeFamilies
public import Integration7.DefinableVFVolumeFamilies

@[expose] public section

/-! Zero-degree coefficient families retain an arbitrary definable density.
Rows and their original-context extensions keep that same density, and
the full VF realization uses it rather than replacing it by one. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.DefinableGeometry

namespace IntegrationInACVF.Section7.HK
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S T : Set M} {n a : ℕ}

def ZeroRVVolumeObject.extend (Z : ZeroRVVolumeObject (M := M) S) (h : S ⊆ T) :
    ZeroRVVolumeObject (M := M) T where
  underlying := Section6.FiniteRV.extendObject h Z.underlying
  form := Z.form.extend h

@[simp] theorem ZeroRVVolumeObject.extend_density (Z : ZeroRVVolumeObject (M := M) S) (h : S ⊆ T)
    (z : (Z.extend h).underlying.obj.domain) : (Z.extend h).form.value z = Z.form.value ⟨z.val,z.property⟩ := rfl

structure ZeroVFVolumeFamily (C : BaseContext M) (n a : ℕ) where
  domain : DefSet (rawMixedSpace (M := M) n a) (C.base : Set M)
  finite_labels : ∀ x : Fin n → VFType (M := M), {r : Fin a → CanonicalRV.RVSort M | (x,r) ∈ domain.carrier}.Finite
  form : VolumeForm domain

def ZeroVFVolumeFamily.toOrdinary {C : BaseContext M} (F : ZeroVFVolumeFamily C n a) :
    OrdinaryVFVolumeFamily C n a := ⟨F.domain,F.finite_labels⟩

def ZeroVFVolumeFamily.ofOrdinary {C : BaseContext M} (F : OrdinaryVFVolumeFamily C n a) :
    ZeroVFVolumeFamily C n a := ⟨F.domain,F.finite_labels,VolumeForm.one F.domain⟩

def ZeroVFVolumeFamily.rowObject {C : BaseContext M} (F : ZeroVFVolumeFamily C n a)
    (x : Fin n → VFType (M := M)) :
    ZeroRVVolumeObject (M := M) ((C.base : Set M) ∪ Set.range (fun i => (x i).val)) where
  underlying := ordinaryZeroVolumeRow F.domain F.finite_labels x
  form := F.form.vfRVFibre x

def ZeroVFVolumeFamily.rowInContext {C : BaseContext M} (F : ZeroVFVolumeFamily C n a)
    (x : Fin n → VFType (M := M)) : ZeroRVVolumeObject (M := M) ((vfParameterVolumeContext C x).base : Set M) :=
  (F.rowObject x).extend (vfParameterVolumeContext_contains C x)

@[simp] theorem ZeroVFVolumeFamily.rowInContext_density {C : BaseContext M}
    (F : ZeroVFVolumeFamily C n a) (x : Fin n → VFType (M := M))
    (r : (F.rowInContext x).underlying.obj.domain) :
    (F.rowInContext x).form.value r = F.form.value ⟨(x,r.val),r.property⟩ := rfl

def ZeroVFVolumeFamily.fullVFObject {C : BaseContext M} (F : ZeroVFVolumeFamily C (n+1) a) :
    PositiveVFVolumeObject (M := M) (C.base : Set M) n :=
  ⟨a,F.domain,F.finite_labels,F.form⟩

@[simp] theorem ZeroVFVolumeFamily.fullVFObject_density {C : BaseContext M}
    (F : ZeroVFVolumeFamily C (n+1) a) (p : F.domain) : F.fullVFObject.form.value p = F.form.value p := rfl

@[simp] theorem ZeroVFVolumeFamily.ofOrdinary_fullVFObject {C : BaseContext M}
    (F : OrdinaryVFVolumeFamily C (n+1) a) :
    (ZeroVFVolumeFamily.ofOrdinary F).fullVFObject = F.fullVFObject := rfl

def ZeroVFVolumeFamily.pointPad {C : BaseContext M} (F : ZeroVFVolumeFamily C n a) :
    DefinableVFVolumeFamily C n a 0 where
  domain := F.domain
  volume := rvScalarOne F.domain
  finite_volume x t := (F.finite_labels x).subset (by
    rintro r ⟨p,hp,_⟩
    change (x,r) ∈ F.domain.carrier
    rw [← hp]
    exact p.property)
  form := F.form

@[simp] theorem ZeroVFVolumeFamily.pointPad_row_density {C : BaseContext M}
    (F : ZeroVFVolumeFamily C n a) (x : Fin n → VFType (M := M))
    (r : (F.pointPad.rowInContext x).underlying.obj.domain) :
    (F.pointPad.rowInContext x).form.value r = (F.rowInContext x).form.value r := rfl

end IntegrationInACVF.Section7.HK
