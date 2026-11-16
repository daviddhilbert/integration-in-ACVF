module

public import Integration7.OrdinaryFamilyPositiveCoefficients
public import Integration7.VolumeFamilyPositiveCoefficientRows
public import Integration7.PositiveVolumeProductOrdinaryScalars

@[expose] public section

/-! Positive-coefficient multiplication of an ordinary family computes
the actual ordinary row scalar acting on the extended positive class. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.DefinableGeometry
open scoped DirectSum

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {C : BaseContext M} {n a p : ℕ}

theorem ordinary_family_positive_coefficient_row_carrier
    (F : OrdinaryVFVolumeFamily C n a) (U : PositiveRVVolumeObject (M := M) (C.base : Set M) p)
    (x : Fin n → VFType (M := M)) :
    ((F.mulConstant U).rowInContext x).underlying.obj.domain.carrier =
      (rvProductDomain (F.rowInContext x).obj.domain
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

def ordinaryFamilyPositiveCoefficientRowIso
    (hc : CanonicalStructure.IsCanonical (M := M))
    (F : OrdinaryVFVolumeFamily C n a) (U : PositiveRVVolumeObject (M := M) (C.base : Set M) p)
    (x : Fin n → VFType (M := M)) :
    RVVolumeIso ((F.mulConstant U).rowInContext x)
      (PositiveRVVolumeObject.zero_prod (F.rowInContext x) (positiveVolumeCoefficientInContext U x)) := by
  let D := vfParameterVolumeContext C x
  let RF := F.rowInContext x
  let RU := positiveVolumeCoefficientInContext U x
  let W := (F.mulConstant U).rowInContext x
  let V := PositiveRVVolumeObject.zero_prod RF RU
  have he := ordinary_family_positive_coefficient_row_carrier F U x
  let f : Map V.underlying.obj.domain W.underlying.obj.domain := Map.inclusion he.ge
  have hf : Function.Bijective f := by
    constructor
    · intro r s h
      have hv := congrArg (fun q : W.underlying.obj.domain => q.val) h
      exact Subtype.ext hv
    · intro r
      exact ⟨⟨r.val,he.le r.property⟩,rfl⟩
  have hPoint (r : RF.obj.domain) (u : RU.underlying.obj.domain) :
      (⟨(x,(f (rvPackPair RF.obj.domain RU.underlying.obj.domain r u)).val),
        (f (rvPackPair RF.obj.domain RU.underlying.obj.domain r u)).property⟩ : (F.mulConstant U).domain) =
      (mixedRVFactorPack F.domain U.underlying.obj.domain).toImage
        ⟨((x,r.val),u.val),r.property,u.property⟩ := Subtype.ext rfl
  have hCoord : ∀ q, W.underlying.obj.value (f q)=V.underlying.obj.value q := by
    intro q
    obtain ⟨r,u,rfl⟩ := exists_rvPackPair RF.obj.domain RU.underlying.obj.domain q
    rw [zeroPositiveProduct_coordinates,rvUnpack_pair]
    change ((F.mulConstant U).volume ⟨(x,(f (rvPackPair _ _ r u)).val),_⟩).val = _
    rw [hPoint,ordinary_family_positive_coefficient_volume]
    change U.underlying.obj.value (Map.prodSnd _ _ (mixedRVFactorUnpack F.domain U.underlying.obj.domain
      ((mixedRVFactorPack F.domain U.underlying.obj.domain).toImage ⟨((x,r.val),u.val),r.property,u.property⟩))) = _
    rw [mixed_rv_factor_unpack_pack]
    rfl
  have hForm : ∀ q, W.form.value (f q)=V.form.value q := by
    intro q
    obtain ⟨r,u,rfl⟩ := exists_rvPackPair RF.obj.domain RU.underlying.obj.domain q
    rw [zeroPositiveProduct_density,rvUnpack_pair]
    change (F.mulConstant U).form.value ⟨(x,(f (rvPackPair _ _ r u)).val),_⟩ = _
    rw [hPoint,ordinary_family_positive_coefficient_density]
    change U.form.value (Map.prodSnd _ _ (mixedRVFactorUnpack F.domain U.underlying.obj.domain
      ((mixedRVFactorPack F.domain U.underlying.obj.domain).toImage ⟨((x,r.val),u.val),r.property,u.property⟩))) = _
    rw [mixed_rv_factor_unpack_pack]
    rfl
  exact (RVVolumeIso.of_preserving_coordinates_full hc D
    (rvFiniteIsoOfAmbient (rvIsoOfVolumePreservingBijection f hf hCoord)) hCoord hForm).symm hc D

theorem ordinary_family_positive_coefficient_row_class
    (hc : CanonicalStructure.IsCanonical (M := M))
    (F : OrdinaryVFVolumeFamily C n a) (U : PositiveRVVolumeObject (M := M) (C.base : Set M) p)
    (x : Fin n → VFType (M := M)) :
    positiveVolumeBlowupClass hc (vfParameterVolumeContext C x) ((F.mulConstant U).rowInContext x) =
      rvVolumeBlowupClass hc (vfParameterVolumeContext C x) (n := 0) (F.rowInContext x) •
        positiveVolumeBlowupClass hc (vfParameterVolumeContext C x) (positiveVolumeCoefficientInContext U x) := by
  let D := vfParameterVolumeContext C x
  let RF := F.rowInContext x
  let RU := positiveVolumeCoefficientInContext U x
  exact (positiveVolumeBlowupClass_iso hc D (ordinaryFamilyPositiveCoefficientRowIso hc F U x)).trans
    ((positiveVolumeBlowupClass_iso hc D (volumeZeroProductSwapIso hc D RU RF)).symm.trans
      (ordinary_volume_smul_representative hc D RF RU).symm)

end IntegrationInACVF.Section7
