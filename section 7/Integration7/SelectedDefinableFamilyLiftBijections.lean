module

public import Integration7.VolumeFamilyLiftCoproductBijections
public import Integration7.SelectedVolumeFamilyAddition
public import Integration7.FixedVFVolumeCoproductBijections

@[expose] public section

/-! Selected-coordinate families and their arbitrary-map presentations
have the same actual VF realization. Consequently, the selected tagged
sum realizes the coproduct of the two original full lifts. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.DefinableGeometry

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {C : BaseContext M} {n a b k : ℕ}

theorem selected_to_definable_family_full_lift_carrier
    (F : SelectedVFVolumeFamily C n a k) :
    F.fullLift.domain.carrier = F.toDefinable.fullLift.domain.carrier := by
  ext w
  change w ∈ (selectedRVVFTailLift F.domain F.selected).carrier ↔
    (w.1,w.2) ∈ F.toDefinable.fullLift.domain.carrier
  rw [mem_selected_rv_vf_tail_lift,mem_definable_volume_family_full_lift]
  constructor
  · rintro ⟨hA,ht⟩
    exact ⟨⟨(w.1 ∘ Fin.castAdd (k+1),w.2),hA⟩,rfl,ht⟩
  · rintro ⟨p,hp,ht⟩
    have hr := congrArg Prod.snd hp
    refine ⟨hp ▸ p.property,?_⟩
    change tupleRV (w.1 ∘ Fin.natAdd n) = w.2 ∘ F.selected
    change tupleRV (w.1 ∘ Fin.natAdd n) = p.val.2 ∘ F.selected at ht
    exact ht.trans (congrArg (fun r => r ∘ F.selected) hr)

def selectedToDefinableFamilyLiftBijection
    (hc : CanonicalStructure.IsCanonical (M := M)) (F : SelectedVFVolumeFamily C n a k) :
    VFVolumeBijection F.fullLift F.toDefinable.fullLift := by
  let he := selected_to_definable_family_full_lift_carrier F
  let f : Map F.fullLift.domain F.toDefinable.fullLift.domain := Map.inclusion he.le
  have hf : Function.Bijective f := by
    constructor
    · intro p q h
      have hv := congrArg Subtype.val h
      exact Subtype.ext hv
    · intro p
      exact ⟨⟨p.val,he.ge p.property⟩,rfl⟩
  refine VFVolumeBijection.of_preserving_vf_and_density hc C f hf (fun _ => rfl) ?_
  intro p
  have hBase : F.toDefinable.fullLiftBaseProjection (f p) = selectedRVVFTailProjection F.domain F.selected p :=
    Subtype.ext (F.toDefinable.fullLiftBaseProjection_value (f p))
  change F.form.value (selectedRVVFTailProjection F.domain F.selected p) =
    F.form.value (F.toDefinable.fullLiftBaseProjection (f p))
  rw [hBase]

def selectedFamilySumLiftBijection
    (hc : CanonicalStructure.IsCanonical (M := M))
    (F : SelectedVFVolumeFamily C n a k) (G : SelectedVFVolumeFamily C n b k) :
    VFVolumeBijection (selectedVolumeFamilySum F G).fullLift (F.fullLift.coprod G.fullLift) :=
  (definableVolumeFamilySelectionLiftBijection hc (F.toDefinable.coprod G.toDefinable)).trans hc C
    (((definableVolumeFamilyLiftCoprodBijection hc F.toDefinable G.toDefinable).symm hc C).trans hc C
      (((selectedToDefinableFamilyLiftBijection hc F).symm hc C).coprod hc C
        ((selectedToDefinableFamilyLiftBijection hc G).symm hc C)))

end IntegrationInACVF.Section7
