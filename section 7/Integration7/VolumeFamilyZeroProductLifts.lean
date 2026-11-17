module

public import Integration7.SelectedVolumeFamilyZeroProducts
public import Integration7.SelectedFamilyFullLifts
public import Integration7.MixedRVFactorZeroLiftCharts
public import Integration7.ZeroFactorVFVolumeProducts

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! Realizing the selected tuple commutes with an ordinary RV[0]
factor. The actual full volume bijection fixes every VF coordinate and
retains the positive family's original density. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.DefinableGeometry

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {C : BaseContext M} {n a k : ℕ}

theorem volume_family_zero_product_full_lift_carrier
    (F : SelectedVFVolumeFamily C n a k) (Z : RVFiniteObject (M := M) (C.base : Set M) 0) :
    (F.prodZero Z).fullLift.domain.carrier = (F.fullLift.prod_zero Z).domain.carrier := by
  trans (mixedRVFactorDomain F.fullLift.domain Z.obj.domain).carrier
  · ext w
    change (w.1,w.2) ∈ (selectedRVVFTailLift (mixedRVFactorDomain F.domain Z.obj.domain)
      (Fin.castAdd Z.obj.arity ∘ F.selected)).carrier ↔
      (w.1,w.2) ∈ (mixedRVFactorDomain (selectedRVVFTailLift F.domain F.selected) Z.obj.domain).carrier
    rw [mem_selected_rv_vf_tail_lift,mem_mixed_rv_factor_domain,mem_mixed_rv_factor_domain,
      mem_selected_rv_vf_tail_lift]
    constructor
    · rintro ⟨⟨hF,hZ⟩,ht⟩
      exact ⟨⟨hF,ht⟩,hZ⟩
    · rintro ⟨⟨hF,ht⟩,hZ⟩
      exact ⟨⟨hF,hZ⟩,ht⟩
  · exact mixed_rv_factor_zero_lift_carrier F.fullLift.domain Z

def volumeFamilyZeroProductLiftBijection
    (hc : CanonicalStructure.IsCanonical (M := M))
    (F : SelectedVFVolumeFamily C n a k) (Z : RVFiniteObject (M := M) (C.base : Set M) 0) :
    VFVolumeBijection (F.prodZero Z).fullLift (F.fullLift.prod_zero Z) := by
  let he := volume_family_zero_product_full_lift_carrier F Z
  let f : Map (F.prodZero Z).fullLift.domain (F.fullLift.prod_zero Z).domain := Map.inclusion he.le
  have hf : Function.Bijective f := by
    constructor
    · intro p q h
      have hv := congrArg Subtype.val h
      exact Subtype.ext hv
    · intro p
      exact ⟨⟨p.val,he.ge p.property⟩,rfl⟩
  refine VFVolumeBijection.of_preserving_vf_and_density hc C f hf (fun _ => rfl) ?_
  intro p
  let u := Map.prodFst F.fullLift.domain (rvLift Z.obj) (mixedUnpack F.fullLift.domain (rvLift Z.obj) (f p))
  have hu := mixed_zero_product_first_value F.fullLift.domain Z (f p)
  change u.val=(p.val.1,p.val.2 ∘ Fin.castAdd Z.obj.arity) at hu
  have hVF := congrArg Prod.fst hu
  have hRV := congrArg Prod.snd hu
  have hBase : F.prodZeroProjection Z (selectedRVVFTailProjection (F.prodZero Z).domain (F.prodZero Z).selected p) =
      selectedRVVFTailProjection F.domain F.selected u := by
    apply Subtype.ext
    have h := F.prodZeroProjection_value Z
      (selectedRVVFTailProjection (F.prodZero Z).domain (F.prodZero Z).selected p)
    refine h.trans ?_
    change (p.val.1 ∘ Fin.castAdd (k+1),p.val.2 ∘ Fin.castAdd Z.obj.arity) =
      (u.val.1 ∘ Fin.castAdd (k+1),u.val.2)
    exact Prod.ext (congrArg (fun x => x ∘ Fin.castAdd (k+1)) hVF.symm) hRV.symm
  change F.form.value (F.prodZeroProjection Z
    (selectedRVVFTailProjection (F.prodZero Z).domain (F.prodZero Z).selected p)) =
      F.form.value (selectedRVVFTailProjection F.domain F.selected u)
  rw [hBase]

end IntegrationInACVF.Section7
