module

public import Integration7.VolumeFamilyZeroProductLifts
public import Integration7.SelectedFamilyFullLifts
public import Integration7.MixedRVFactorZeroLiftCharts
public import Integration7.HKSelectedFamilyWeightedZeroProducts
public import Integration7.HKWeightedVFZeroProducts
public import Integration7.MixedProductCoordinateFormulas

@[expose] public section

/-! Realizing the selected tuple commutes with an ordinary RV[0]
factor. The actual full volume bijection fixes every VF coordinate and
retains the positive family's original density. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry

namespace IntegrationInACVF.Section7.HK
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {C : BaseContext M} {n a k : ℕ}

def weightedVolumeFamilyZeroProductLiftBijection
    (hc : CanonicalStructure.IsCanonical (M := M))
    (F : SelectedVFVolumeFamily C n a k) (Z : ZeroRVVolumeObject (M := M) (C.base : Set M)) :
    VFVolumeBijection (selectedFamilyWeightedZeroProduct F Z).fullLift (positiveVFZeroProduct F.fullLift Z) := by
  let he := volume_family_zero_product_full_lift_carrier F Z.underlying
  let f : Map (selectedFamilyWeightedZeroProduct F Z).fullLift.domain (positiveVFZeroProduct F.fullLift Z).domain := Map.inclusion he.le
  have hf : Function.Bijective f := by
    constructor
    · intro p q h
      have hv := congrArg Subtype.val h
      exact Subtype.ext hv
    · intro p
      exact ⟨⟨p.val,he.ge p.property⟩,rfl⟩
  refine VFVolumeBijection.of_preserving_vf_and_density hc C f hf (fun _ => rfl) ?_
  intro p
  let u := Map.prodFst F.fullLift.domain (rvLift Z.underlying.obj) (mixedUnpack F.fullLift.domain (rvLift Z.underlying.obj) (f p))
  have hu := mixed_zero_product_first_value F.fullLift.domain Z.underlying (f p)
  change u.val=(p.val.1,p.val.2 ∘ Fin.castAdd Z.underlying.obj.arity) at hu
  have hVF := congrArg Prod.fst hu
  have hRV := congrArg Prod.snd hu
  have hBase : F.prodZeroProjection Z.underlying (selectedRVVFTailProjection (selectedFamilyWeightedZeroProduct F Z).domain (selectedFamilyWeightedZeroProduct F Z).selected p) =
      selectedRVVFTailProjection F.domain F.selected u := by
    apply Subtype.ext
    have h := F.prodZeroProjection_value Z.underlying
      (selectedRVVFTailProjection (selectedFamilyWeightedZeroProduct F Z).domain (selectedFamilyWeightedZeroProduct F Z).selected p)
    refine h.trans ?_
    change (p.val.1 ∘ Fin.castAdd (k+1),p.val.2 ∘ Fin.castAdd Z.underlying.obj.arity) =
      (u.val.1 ∘ Fin.castAdd (k+1),u.val.2)
    exact Prod.ext (congrArg (fun x => x ∘ Fin.castAdd (k+1)) hVF.symm) hRV.symm
  let z := Map.prodSnd F.fullLift.domain (rvLift Z.underlying.obj)
    (mixedUnpack F.fullLift.domain (rvLift Z.underlying.obj) (f p))
  let w := selectedRVVFTailProjection (selectedFamilyWeightedZeroProduct F Z).domain
    (selectedFamilyWeightedZeroProduct F Z).selected p
  let v := mixedRVFactorUnpack F.domain Z.underlying.obj.domain w
  have hZ : Map.prodSnd _ _ v=liftLabelMap Z.underlying.obj z := by
    apply Subtype.ext
    have ht := congrArg Prod.snd (mixed_rv_factor_unpack_value F.domain Z.underlying.obj.domain w)
    have hz := congrArg (fun q => q.2.2)
      (mixed_product_unpack_value F.fullLift.domain (rvLift Z.underlying.obj) (f p))
    exact ht.trans hz.symm
  change Map.prodFst _ _ v=selectedRVVFTailProjection F.domain F.selected u at hBase
  change F.form.value (Map.prodFst _ _ v) * Z.form.value (Map.prodSnd _ _ v) =
    F.form.value (selectedRVVFTailProjection F.domain F.selected u) * Z.form.value (liftLabelMap Z.underlying.obj z)
  rw [hBase,hZ]

end IntegrationInACVF.Section7.HK
