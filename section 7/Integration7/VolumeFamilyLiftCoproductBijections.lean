module

public import Integration7.VolumeFamilyLiftCoproductCarriers

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! The literal coproduct carrier identification preserves VF tuples
and the original density, so it is an actual full VF volume bijection. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.DefinableGeometry

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {C : BaseContext M} {n a b k : ℕ}

def definableVolumeFamilyLiftCoprodBijection
    (hc : CanonicalStructure.IsCanonical (M := M))
    (F : DefinableVFVolumeFamily C n a k) (G : DefinableVFVolumeFamily C n b k) :
    VFVolumeBijection (F.fullLift.coprod G.fullLift) (F.coprod G).fullLift := by
  let he := volume_family_lift_coprod_carrier F G
  let f : Map (F.fullLift.coprod G.fullLift).domain (F.coprod G).fullLift.domain := Map.inclusion he.ge
  have hf : Function.Bijective f := by
    constructor
    · intro p q h
      have hv := congrArg Subtype.val h
      exact Subtype.ext hv
    · intro p
      exact ⟨⟨p.val,he.le p.property⟩,rfl⟩
  refine VFVolumeBijection.of_preserving_vf_and_density hc C f hf (fun _ => rfl) ?_
  intro p
  rcases vf_volume_coprod_cases F.fullLift G.fullLift p with ⟨u,rfl⟩ | ⟨v,rfl⟩
  · have hBase : (F.coprod G).fullLiftBaseProjection (f (vfVolumeCoprodLeftMap F.fullLift G.fullLift u)) =
        volumeFamilyCoprodLeftMap F G (F.fullLiftBaseProjection u) := by
      apply Subtype.ext
      have h := (F.coprod G).fullLiftBaseProjection_value (f (vfVolumeCoprodLeftMap F.fullLift G.fullLift u))
      have hF := F.fullLiftBaseProjection_value u
      have hx := congrArg Prod.fst hF
      have hr := congrArg Prod.snd hF
      refine h.trans ?_
      change (u.val.1 ∘ Fin.castAdd (k+1),rvLeftTag b u.val.2) =
        ((F.fullLiftBaseProjection u).val.1,rvLeftTag b (F.fullLiftBaseProjection u).val.2)
      exact Prod.ext hx.symm (congrArg (rvLeftTag b) hr.symm)
    rw [vf_volume_coprod_density_left,DefinableVFVolumeFamily.fullLift_density,
      DefinableVFVolumeFamily.fullLift_density,hBase]
    exact (volume_family_coprod_density_left F G (F.fullLiftBaseProjection u)).symm
  · have hBase : (F.coprod G).fullLiftBaseProjection (f (vfVolumeCoprodRightMap F.fullLift G.fullLift v)) =
        volumeFamilyCoprodRightMap F G (G.fullLiftBaseProjection v) := by
      apply Subtype.ext
      have h := (F.coprod G).fullLiftBaseProjection_value (f (vfVolumeCoprodRightMap F.fullLift G.fullLift v))
      have hG := G.fullLiftBaseProjection_value v
      have hx := congrArg Prod.fst hG
      have hr := congrArg Prod.snd hG
      refine h.trans ?_
      change (v.val.1 ∘ Fin.castAdd (k+1),rvRightTag a v.val.2) =
        ((G.fullLiftBaseProjection v).val.1,rvRightTag a (G.fullLiftBaseProjection v).val.2)
      exact Prod.ext hx.symm (congrArg (rvRightTag a) hr.symm)
    rw [vf_volume_coprod_density_right,DefinableVFVolumeFamily.fullLift_density,
      DefinableVFVolumeFamily.fullLift_density,hBase]
    exact (volume_family_coprod_density_right F G (G.fullLiftBaseProjection v)).symm

end IntegrationInACVF.Section7
