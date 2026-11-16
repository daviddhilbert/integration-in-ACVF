module

public import Integration7.HKZeroVolumeHeadFibres
public import Integration7.HKZeroFamilyCoproducts
public import Integration7.VFVolumeBijections

@[expose] public section

/-! Actual frozen unit-density realizations preserve ordinary-family
coproducts. Both identifications keep the VF tuple and the original densities. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry
namespace IntegrationInACVF.Section7.HK
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {C : BaseContext M} {n a b : ℕ}

def zeroFamilyFullCoprodBijection
    (hc : CanonicalStructure.IsCanonical (M := M))
    (F : ZeroVFVolumeFamily C (n+1) a) (G : ZeroVFVolumeFamily C (n+1) b) :
    VFVolumeBijection (F.coprod G).fullVFObject (F.fullVFObject.coprod G.fullVFObject) := by
  exact VFVolumeBijection.refl hc C (F.fullVFObject.coprod G.fullVFObject)

theorem zero_frozen_head_coprod_carrier
    (hc : CanonicalStructure.IsCanonical (M := M))
    (F : ZeroVFVolumeFamily C (n+1) a) (G : ZeroVFVolumeFamily C (n+1) b)
    (x : Fin n → VFType (M := M)) :
    ((F.coprod G).frozenHeadFamily hc x).domain.carrier =
      ((F.frozenHeadFamily hc x).coprod (G.frozenHeadFamily hc x)).domain.carrier := by
  ext p
  rcases p with ⟨y,r⟩
  have hOld := Set.ext_iff.mp (ordinary_volume_family_coprod_row_carrier F.toOrdinary G.toOrdinary (Fin.cons (y 0) x)) r
  have hNew := Set.ext_iff.mp (ordinary_volume_family_coprod_row_carrier
    (F.frozenHeadFamily hc x).toOrdinary (G.frozenHeadFamily hc x).toOrdinary y) r
  exact hOld.trans hNew.symm

def zeroFrozenHeadCoprodBijection
    (hc : CanonicalStructure.IsCanonical (M := M))
    (F : ZeroVFVolumeFamily C (n+1) a) (G : ZeroVFVolumeFamily C (n+1) b)
    (x : Fin n → VFType (M := M)) :
    VFVolumeBijection ((F.coprod G).frozenHeadFamily hc x).fullVFObject
      ((F.frozenHeadFamily hc x).fullVFObject.coprod (G.frozenHeadFamily hc x).fullVFObject) := by
  let D := frozenHeadVolumeContext hc C x
  let U := ((F.coprod G).frozenHeadFamily hc x).fullVFObject
  let V := ((F.frozenHeadFamily hc x).coprod (G.frozenHeadFamily hc x)).fullVFObject
  have hUV := zero_frozen_head_coprod_carrier hc F G x
  let f : Map U.domain V.domain := Map.inclusion hUV.le
  have hf : Function.Bijective f := by
    constructor
    · intro u v h
      exact Subtype.ext (congrArg (fun q : V.domain => q.val) h)
    · intro v
      exact ⟨⟨v.val,hUV.ge v.property⟩,rfl⟩
  have hDensity (p : U.domain) : U.form.value p = V.form.value (f p) := by
    rcases vf_volume_coprod_cases (F.frozenHeadFamily hc x).fullVFObject
      (G.frozenHeadFamily hc x).fullVFObject (f p) with ⟨u,hu⟩ | ⟨v,hv⟩
    · let u' : F.domain := ⟨(Fin.cons (u.val.1 0) x,u.val.2),u.property⟩
      have hp : (⟨(Fin.cons (p.val.1 0) x,p.val.2),p.property⟩ : (F.fullVFObject.coprod G.fullVFObject).domain) =
          vfVolumeCoprodLeftMap F.fullVFObject G.fullVFObject u' := by
        apply Subtype.ext
        exact congrArg (fun q : (Fin 1 → VFType (M := M)) × (Fin (1+(a+b)) → CanonicalRV.RVSort M) => ((Fin.cons (q.1 0) x : Fin (n+1) → VFType (M := M)),q.2)) (congrArg Subtype.val hu).symm
      change (F.fullVFObject.coprod G.fullVFObject).form.value
        ⟨(Fin.cons (p.val.1 0) x,p.val.2),p.property⟩ =
        ((F.frozenHeadFamily hc x).fullVFObject.coprod (G.frozenHeadFamily hc x).fullVFObject).form.value (f p)
      rw [hp,← hu,vf_volume_coprod_density_left,vf_volume_coprod_density_left]
      rfl
    · let v' : G.domain := ⟨(Fin.cons (v.val.1 0) x,v.val.2),v.property⟩
      have hp : (⟨(Fin.cons (p.val.1 0) x,p.val.2),p.property⟩ : (F.fullVFObject.coprod G.fullVFObject).domain) =
          vfVolumeCoprodRightMap F.fullVFObject G.fullVFObject v' := by
        apply Subtype.ext
        exact congrArg (fun q : (Fin 1 → VFType (M := M)) × (Fin (1+(a+b)) → CanonicalRV.RVSort M) => ((Fin.cons (q.1 0) x : Fin (n+1) → VFType (M := M)),q.2)) (congrArg Subtype.val hv).symm
      change (F.fullVFObject.coprod G.fullVFObject).form.value
        ⟨(Fin.cons (p.val.1 0) x,p.val.2),p.property⟩ =
        ((F.frozenHeadFamily hc x).fullVFObject.coprod (G.frozenHeadFamily hc x).fullVFObject).form.value (f p)
      rw [hp,← hv,vf_volume_coprod_density_right,vf_volume_coprod_density_right]
      rfl
  exact VFVolumeBijection.of_preserving_vf_and_density hc D f hf (fun _ => rfl) hDensity
end IntegrationInACVF.Section7.HK
