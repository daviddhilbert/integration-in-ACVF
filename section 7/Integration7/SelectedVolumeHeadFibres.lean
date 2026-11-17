module

public import Integration7.MixedHeadFibres
public import Integration7.SelectedVolumeFamilies

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! Freezing the retained VF tuple gives an actual unary selected
volume family in its genuine finite-parameter context. No VF field or
generation assertion is made about that term-generated context. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.DefinableGeometry

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {C : BaseContext M} {n a k : ℕ}

def SelectedVFVolumeFamily.headFibre (F : SelectedVFVolumeFamily C (n+1) a k)
    (x : Fin n → VFType (M := M)) : SelectedVFVolumeFamily (vfParameterVolumeContext C x) 1 a k where
  domain := (mixedHeadFibre F.domain x).extend (vfParameterVolumeContext_contains C x)
  selected := F.selected
  finite_selected y t := F.finite_selected (Fin.cons (y 0) x) t
  form := (F.form.mixedHeadFibre x).extend (vfParameterVolumeContext_contains C x)

@[simp] theorem SelectedVFVolumeFamily.headFibre_domain
    (F : SelectedVFVolumeFamily C (n+1) a k) (x : Fin n → VFType (M := M))
    (y : Fin 1 → VFType (M := M)) (r : Fin a → CanonicalRV.RVSort M) :
    (y,r) ∈ (F.headFibre x).domain.carrier ↔ (Fin.cons (y 0) x,r) ∈ F.domain.carrier := Iff.rfl

@[simp] theorem SelectedVFVolumeFamily.headFibre_density
    (F : SelectedVFVolumeFamily C (n+1) a k) (x : Fin n → VFType (M := M))
    (p : (F.headFibre x).domain) :
    (F.headFibre x).form.value p = F.form.value ⟨(Fin.cons (p.val.1 0) x,p.val.2),p.property⟩ := rfl

def SelectedVFVolumeFamily.extendContext (F : SelectedVFVolumeFamily C n a k)
    {D : BaseContext M} (hCD : (C.base : Set M) ⊆ (D.base : Set M)) : SelectedVFVolumeFamily D n a k where
  domain := F.domain.extend hCD
  selected := F.selected
  finite_selected := F.finite_selected
  form := F.form.extend hCD

@[simp] theorem SelectedVFVolumeFamily.extendContext_density
    (F : SelectedVFVolumeFamily C n a k) {D : BaseContext M}
    (hCD : (C.base : Set M) ⊆ (D.base : Set M)) (p : (F.extendContext hCD).domain) :
    (F.extendContext hCD).form.value p = F.form.value ⟨p.val,p.property⟩ := rfl

end IntegrationInACVF.Section7
