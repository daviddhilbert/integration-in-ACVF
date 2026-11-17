module

public import Integration7.DefinableAppendedLiftCarriers

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! The selected and arbitrary-map presentations of a family have
identical coefficient-first lift carriers and original densities. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.DefinableGeometry

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {C : BaseContext M} {n a k : ℕ}

theorem selected_to_definable_appended_lift_carrier
    (F : SelectedVFVolumeFamily C n a k) :
    F.appendedFullLift.domain.carrier=F.toDefinable.appendedFullLift.domain.carrier := by
  ext q
  change (q.1,q.2) ∈ F.appendedFullLift.domain.carrier ↔ (q.1,q.2) ∈ F.toDefinable.appendedFullLift.domain.carrier
  rw [mem_appended_family_full_lift,mem_definable_appended_family_lift]
  constructor
  · rintro ⟨hF,ht⟩
    exact ⟨⟨(appendedFamilyBaseCoordinates n k q.1,q.2),hF⟩,rfl,ht⟩
  · rintro ⟨p,hp,ht⟩
    have hr := congrArg Prod.snd hp
    refine ⟨hp ▸ p.property,?_⟩
    change tupleRV (appendedFamilyCoefficientCoordinates n k q.1)=p.val.2 ∘ F.selected at ht
    exact ht.trans (congrArg (fun r => r ∘ F.selected) hr)

def selectedToDefinableAppendedLiftBijection
    (hc : CanonicalStructure.IsCanonical (M := M)) (F : SelectedVFVolumeFamily C n a k) :
    VFVolumeBijection F.appendedFullLift F.toDefinable.appendedFullLift := by
  let h := selected_to_definable_appended_lift_carrier F
  let f : Map F.appendedFullLift.domain F.toDefinable.appendedFullLift.domain := Map.inclusion h.le
  have hf : Function.Bijective f := by
    constructor
    · intro p q he
      have hv := congrArg Subtype.val he
      exact Subtype.ext hv
    · intro q
      exact ⟨⟨q.val,h.ge q.property⟩,rfl⟩
  refine VFVolumeBijection.of_preserving_vf_and_density hc C f hf (fun _ => rfl) ?_
  intro q
  rw [SelectedVFVolumeFamily.appendedFullLift_density,DefinableVFVolumeFamily.appendedFullLift_density]
  have hBase : F.toDefinable.appendedLiftBaseProjection (f q)=
      ⟨(appendedFamilyBaseCoordinates n k q.val.1,q.val.2),
        ((mem_appended_family_full_lift F q.val.1 q.val.2).mp q.property).1⟩ :=
    Subtype.ext (F.toDefinable.appendedLiftBaseProjection_value (f q))
  change F.form.value _=F.form.value (F.toDefinable.appendedLiftBaseProjection (f q))
  rw [hBase]

end IntegrationInACVF.Section7
