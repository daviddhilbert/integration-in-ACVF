module

public import Integration7.VolumeFamilyPositiveCoefficientProducts
public import Integration7.VolumeProductPointwise
public import Integration7.SignedVolumeProductSwap
public import Section4.RVProductRestrictions

@[expose] public section

/-! Positive constant-family multiplication computes the genuine
coefficient-first RV product on every fibre. The domain-label blocks are
swapped by an actual definable map; the volume tuple and density agree. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.DefinableGeometry

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {C : BaseContext M} {n a k p : ℕ}

def positiveVolumeCoefficientInContext (U : PositiveRVVolumeObject (M := M) (C.base : Set M) p)
    (x : Fin n → VFType (M := M)) :
    PositiveRVVolumeObject (M := M) ((vfParameterVolumeContext C x).base : Set M) p :=
  U.extend (fun _ h => vfParameterVolumeContext_contains C x (Or.inl h))

theorem volume_family_constant_row_carrier
    (F : DefinableVFVolumeFamily C n a k) (U : PositiveRVVolumeObject (M := M) (C.base : Set M) p)
    (x : Fin n → VFType (M := M)) :
    ((F.mulConstant U).rowInContext x).underlying.obj.domain.carrier =
      (rvProductDomain (F.rowInContext x).underlying.obj.domain
        (positiveVolumeCoefficientInContext U x).underlying.obj.domain).carrier := by
  ext r
  change (x,r) ∈ (mixedRVFactorDomain F.domain U.underlying.obj.domain).carrier ↔ _
  rw [mem_mixed_rv_factor_domain,mem_rvProductDomain]
  constructor
  · rintro ⟨hF,hU⟩
    exact ⟨r ∘ Fin.castAdd U.underlying.obj.arity,hF,r ∘ Fin.natAdd a,hU,Fin.append_castAdd_natAdd⟩
  · rintro ⟨r,hr,u,hu,he⟩
    change (x,r) ∈ F.domain.carrier at hr
    change u ∈ U.underlying.obj.domain.carrier at hu
    rw [← he]
    change (x,Fin.append (m := a) (n := U.underlying.obj.arity) r u ∘ Fin.castAdd U.underlying.obj.arity) ∈ F.domain.carrier ∧
      Fin.append (m := a) (n := U.underlying.obj.arity) r u ∘ Fin.natAdd a ∈ U.underlying.obj.domain.carrier
    simpa only [Function.comp_def,Fin.append_left,Fin.append_right] using And.intro hr hu

def volumeFamilyPositiveCoefficientRowIso
    (hc : CanonicalStructure.IsCanonical (M := M))
    (F : DefinableVFVolumeFamily C n a k) (U : PositiveRVVolumeObject (M := M) (C.base : Set M) p)
    (x : Fin n → VFType (M := M)) :
    RVVolumeIso ((F.mulConstant U).rowInContext x)
      ((positiveVolumeCoefficientInContext U x).prod (F.rowInContext x)) := by
  let D := vfParameterVolumeContext C x
  let RF := F.rowInContext x
  let RU := positiveVolumeCoefficientInContext U x
  let W := (F.mulConstant U).rowInContext x
  let V := RU.prod RF
  let he := volume_family_constant_row_carrier F U x
  let j : Map (rvProductDomain RF.underlying.obj.domain RU.underlying.obj.domain) W.underlying.obj.domain :=
    Map.inclusion he.ge
  have hj : Function.Bijective j := by
    constructor
    · intro r s h
      have hv := congrArg Subtype.val h
      exact Subtype.ext hv
    · intro r
      exact ⟨⟨r.val,he.le r.property⟩,rfl⟩
  let f : Map V.underlying.obj.domain W.underlying.obj.domain :=
    j.comp (rvProductSwapMap RU.underlying.obj RF.underlying.obj)
  have hf : Function.Bijective f := hj.comp (rvProductSwapMap_bijective RU.underlying.obj RF.underlying.obj)
  have hPoint (u : RU.underlying.obj.domain) (r : RF.underlying.obj.domain) :
      (⟨(x,(f (rvPackPair RU.underlying.obj.domain RF.underlying.obj.domain u r)).val),
        (f (rvPackPair RU.underlying.obj.domain RF.underlying.obj.domain u r)).property⟩ :
          (F.mulConstant U).domain) =
      (mixedRVFactorPack F.domain U.underlying.obj.domain).toImage
        ⟨((x,r.val),u.val),r.property,u.property⟩ := by
    apply Subtype.ext
    change (x,(f (rvPackPair RU.underlying.obj.domain RF.underlying.obj.domain u r)).val) =
      (x,Fin.append r.val u.val)
    refine Prod.ext rfl ?_
    change (rvProductSwapMap RU.underlying.obj RF.underlying.obj
      (rvPackPair RU.underlying.obj.domain RF.underlying.obj.domain u r)).val = Fin.append r.val u.val
    rw [rvProductSwapMap_pair]
    rfl
  have hCoord : ∀ q, W.underlying.obj.value (f q) = V.underlying.obj.value q := by
    intro q
    obtain ⟨u,r,rfl⟩ := exists_rvPackPair RU.underlying.obj.domain RF.underlying.obj.domain q
    rw [positiveProduct_coordinates_pair]
    change (volumeFamilyConstantVolumeMap F U ⟨(x,(f (rvPackPair _ _ u r)).val),_⟩).val = _
    rw [hPoint,volume_family_constant_volume]
    change Fin.append (U.underlying.obj.value (Map.prodSnd _ _
      (mixedRVFactorUnpack F.domain U.underlying.obj.domain ((mixedRVFactorPack F.domain U.underlying.obj.domain).toImage
        ⟨((x,r.val),u.val),r.property,u.property⟩))))
      (F.volume (Map.prodFst _ _ (mixedRVFactorUnpack F.domain U.underlying.obj.domain
        ((mixedRVFactorPack F.domain U.underlying.obj.domain).toImage ⟨((x,r.val),u.val),r.property,u.property⟩)))).val = _
    rw [mixed_rv_factor_unpack_pack]
    rfl
  have hForm : ∀ q, W.form.value (f q) = V.form.value q := by
    intro q
    obtain ⟨u,r,rfl⟩ := exists_rvPackPair RU.underlying.obj.domain RF.underlying.obj.domain q
    rw [positiveProduct_density_pair]
    change (volumeFamilyConstantForm F U).value ⟨(x,(f (rvPackPair _ _ u r)).val),_⟩ = _
    rw [hPoint,volume_family_constant_density]
    change U.form.value (Map.prodSnd _ _ (mixedRVFactorUnpack F.domain U.underlying.obj.domain
      ((mixedRVFactorPack F.domain U.underlying.obj.domain).toImage ⟨((x,r.val),u.val),r.property,u.property⟩))) *
      F.form.value (Map.prodFst _ _ (mixedRVFactorUnpack F.domain U.underlying.obj.domain
      ((mixedRVFactorPack F.domain U.underlying.obj.domain).toImage ⟨((x,r.val),u.val),r.property,u.property⟩))) = _
    rw [mixed_rv_factor_unpack_pack]
    rfl
  exact (RVVolumeIso.of_preserving_coordinates_full hc D
    (rvFiniteIsoOfAmbient (rvIsoOfVolumePreservingBijection f hf hCoord)) hCoord hForm).symm hc D

end IntegrationInACVF.Section7
