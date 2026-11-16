module

public import Integration7.OrdinaryVolumeHeadFibres
public import Integration7.OrdinaryVolumeFamilyCoproducts
public import Integration7.VFVolumeBijections

@[expose] public section

/-! Actual frozen unit-density realizations preserve ordinary-family
coproducts. Both identifications keep the VF tuple and the unit density. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry
namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {C : BaseContext M} {n a b : ℕ}

def ordinaryFamilyFullCoprodBijection
    (hc : CanonicalStructure.IsCanonical (M := M))
    (F : OrdinaryVFVolumeFamily C (n+1) a) (G : OrdinaryVFVolumeFamily C (n+1) b) :
    VFVolumeBijection (F.coprod G).fullVFObject (F.fullVFObject.coprod G.fullVFObject) := by
  let U := (F.coprod G).fullVFObject
  let V := F.fullVFObject.coprod G.fullVFObject
  let f : Map U.domain V.domain := Map.id _
  have hForm (p : U.domain) : U.form.value p = V.form.value (f p) := by
    rcases vf_volume_coprod_cases F.fullVFObject G.fullVFObject (f p) with ⟨u,hu⟩ | ⟨v,hv⟩
    · rw [← hu,vf_volume_coprod_density_left]
      rfl
    · rw [← hv,vf_volume_coprod_density_right]
      rfl
  exact VFVolumeBijection.of_preserving_vf_and_density hc C f Function.bijective_id (fun _ => rfl) hForm

theorem ordinary_frozen_head_coprod_carrier
    (hc : CanonicalStructure.IsCanonical (M := M))
    (F : OrdinaryVFVolumeFamily C (n+1) a) (G : OrdinaryVFVolumeFamily C (n+1) b)
    (x : Fin n → VFType (M := M)) :
    ((F.coprod G).frozenHeadFamily hc x).domain.carrier =
      ((F.frozenHeadFamily hc x).coprod (G.frozenHeadFamily hc x)).domain.carrier := by
  ext p
  rcases p with ⟨y,r⟩
  have hOld := Set.ext_iff.mp (ordinary_volume_family_coprod_row_carrier F G (Fin.cons (y 0) x)) r
  have hNew := Set.ext_iff.mp (ordinary_volume_family_coprod_row_carrier
    (F.frozenHeadFamily hc x) (G.frozenHeadFamily hc x) y) r
  exact hOld.trans hNew.symm

def ordinaryFrozenHeadCoprodBijection
    (hc : CanonicalStructure.IsCanonical (M := M))
    (F : OrdinaryVFVolumeFamily C (n+1) a) (G : OrdinaryVFVolumeFamily C (n+1) b)
    (x : Fin n → VFType (M := M)) :
    VFVolumeBijection ((F.coprod G).frozenHeadFamily hc x).fullVFObject
      ((F.frozenHeadFamily hc x).fullVFObject.coprod (G.frozenHeadFamily hc x).fullVFObject) := by
  let D := frozenHeadVolumeContext hc C x
  let U := ((F.coprod G).frozenHeadFamily hc x).fullVFObject
  let V := ((F.frozenHeadFamily hc x).coprod (G.frozenHeadFamily hc x)).fullVFObject
  have hUV := ordinary_frozen_head_coprod_carrier hc F G x
  let f : Map U.domain V.domain := Map.inclusion hUV.le
  have hf : Function.Bijective f := by
    constructor
    · intro u v h
      exact Subtype.ext (congrArg (fun q : V.domain => q.val) h)
    · intro v
      exact ⟨⟨v.val,hUV.ge v.property⟩,rfl⟩
  exact (VFVolumeBijection.of_preserving_vf_and_density hc D f hf (fun _ => rfl) (fun _ => rfl)).trans hc D
    (ordinaryFamilyFullCoprodBijection hc (F.frozenHeadFamily hc x) (G.frozenHeadFamily hc x))
end IntegrationInACVF.Section7
