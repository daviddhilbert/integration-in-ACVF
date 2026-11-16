module

public import Integration7.DefinableVolumeFamilyCoproducts
public import Integration7.VolumeCoproduct

@[expose] public section

/-! The tagged union of families restricts on every named VF fibre to
the literal RV tagged union. Its two inclusions retain the original
volume coordinate map and density. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.DefinableGeometry

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {C : BaseContext M} {n a b k : ℕ}

theorem volume_family_coprod_row_carrier
    (F : DefinableVFVolumeFamily C n a k) (G : DefinableVFVolumeFamily C n b k)
    (x : Fin n → VFType (M := M)) :
    ((F.coprod G).rowInContext x).underlying.obj.domain.carrier =
      ((F.rowInContext x).coprod (G.rowInContext x)).underlying.obj.domain.carrier := by
  ext r
  constructor
  · rintro (⟨u,hu⟩ | ⟨v,hv⟩)
    · left
      change (u.val.1,rvLeftTag b u.val.2)=(x,r) at hu
      have hx := congrArg Prod.fst hu
      have hRV := congrArg Prod.snd hu
      have hmem : (x,u.val.2) ∈ F.domain.carrier := by
        have h := u.property
        change (u.val.1,u.val.2) ∈ F.domain.carrier at h
        change u.val.1=x at hx
        rw [hx] at h
        exact h
      exact ⟨⟨u.val.2,hmem⟩,hRV⟩
    · right
      change (v.val.1,rvRightTag a v.val.2)=(x,r) at hv
      have hx := congrArg Prod.fst hv
      have hRV := congrArg Prod.snd hv
      have hmem : (x,v.val.2) ∈ G.domain.carrier := by
        have h := v.property
        change (v.val.1,v.val.2) ∈ G.domain.carrier at h
        change v.val.1=x at hx
        rw [hx] at h
        exact h
      exact ⟨⟨v.val.2,hmem⟩,hRV⟩
  · rintro (⟨u,hu⟩ | ⟨v,hv⟩)
    · left
      exact ⟨⟨(x,u.val),u.property⟩,Prod.ext rfl hu⟩
    · right
      exact ⟨⟨(x,v.val),v.property⟩,Prod.ext rfl hv⟩

def volumeFamilyCoprodRowLeftMap (F : DefinableVFVolumeFamily C n a k) (G : DefinableVFVolumeFamily C n b k)
    (x : Fin n → VFType (M := M)) :
    Map (F.rowInContext x).underlying.obj.domain ((F.coprod G).rowInContext x).underlying.obj.domain :=
  (rvLeftTagMap (F.rowInContext x).underlying.obj.domain b).corestrict
    (fun r => Or.inl ⟨⟨(x,r.val),r.property⟩,rfl⟩)

def volumeFamilyCoprodRowRightMap (F : DefinableVFVolumeFamily C n a k) (G : DefinableVFVolumeFamily C n b k)
    (x : Fin n → VFType (M := M)) :
    Map (G.rowInContext x).underlying.obj.domain ((F.coprod G).rowInContext x).underlying.obj.domain :=
  (rvRightTagMap (G.rowInContext x).underlying.obj.domain a).corestrict
    (fun r => Or.inr ⟨⟨(x,r.val),r.property⟩,rfl⟩)

theorem volume_family_coprod_row_left_coordinates
    (F : DefinableVFVolumeFamily C n a k) (G : DefinableVFVolumeFamily C n b k)
    (x : Fin n → VFType (M := M)) (r : (F.rowInContext x).underlying.obj.domain) :
    ((F.coprod G).rowInContext x).underlying.obj.value (volumeFamilyCoprodRowLeftMap F G x r) =
      (F.rowInContext x).underlying.obj.value r :=
  congrArg Subtype.val (volume_family_coprod_volume_left F G ⟨(x,r.val),r.property⟩)

theorem volume_family_coprod_row_right_coordinates
    (F : DefinableVFVolumeFamily C n a k) (G : DefinableVFVolumeFamily C n b k)
    (x : Fin n → VFType (M := M)) (r : (G.rowInContext x).underlying.obj.domain) :
    ((F.coprod G).rowInContext x).underlying.obj.value (volumeFamilyCoprodRowRightMap F G x r) =
      (G.rowInContext x).underlying.obj.value r :=
  congrArg Subtype.val (volume_family_coprod_volume_right F G ⟨(x,r.val),r.property⟩)

theorem volume_family_coprod_row_left_density
    (F : DefinableVFVolumeFamily C n a k) (G : DefinableVFVolumeFamily C n b k)
    (x : Fin n → VFType (M := M)) (r : (F.rowInContext x).underlying.obj.domain) :
    ((F.coprod G).rowInContext x).form.value (volumeFamilyCoprodRowLeftMap F G x r) =
      (F.rowInContext x).form.value r :=
  volume_family_coprod_density_left F G ⟨(x,r.val),r.property⟩

theorem volume_family_coprod_row_right_density
    (F : DefinableVFVolumeFamily C n a k) (G : DefinableVFVolumeFamily C n b k)
    (x : Fin n → VFType (M := M)) (r : (G.rowInContext x).underlying.obj.domain) :
    ((F.coprod G).rowInContext x).form.value (volumeFamilyCoprodRowRightMap F G x r) =
      (G.rowInContext x).form.value r :=
  volume_family_coprod_density_right F G ⟨(x,r.val),r.property⟩

end IntegrationInACVF.Section7
