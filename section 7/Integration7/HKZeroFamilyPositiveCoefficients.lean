module

public import Integration7.HKZeroVolumeFamilies
public import Integration7.OrdinaryFamilyPositiveCoefficientRows
public import Integration7.HKZeroCoefficientScalarRows
public import Integration7.DefinableVolumeFamilySelectionRows

@[expose] public section

/-! A positive coefficient multiplies a weighted-zero-valued family on
the literal finite-factor product. Both input forms survive. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.DefinableGeometry

namespace IntegrationInACVF.Section7.HK
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {C : BaseContext M} {n a p : ℕ}

def ZeroVFVolumeFamily.mulConstant (F : ZeroVFVolumeFamily C n a)
    (U : PositiveRVVolumeObject (M := M) (C.base : Set M) p) :
    DefinableVFVolumeFamily C n (a+U.underlying.obj.arity) p :=
  { F.toOrdinary.mulConstant U with
    form := (F.form.prod U.form).pullback (mixedRVFactorUnpack F.domain U.underlying.obj.domain) }

def zeroFamilyPositiveCoefficientRowIso
    (hc : CanonicalStructure.IsCanonical (M := M))
    (F : ZeroVFVolumeFamily C n a) (U : PositiveRVVolumeObject (M := M) (C.base : Set M) p)
    (x : Fin n → VFType (M := M)) :
    RVVolumeIso ((F.mulConstant U).rowInContext x)
      (zeroProduct (F.rowInContext x) (positiveVolumeCoefficientInContext U x)) := by
  let D := vfParameterVolumeContext C x
  let RF := F.rowInContext x
  let RU := positiveVolumeCoefficientInContext U x
  let W := (F.mulConstant U).rowInContext x
  let V := zeroProduct RF RU
  have he := ordinary_family_positive_coefficient_row_carrier F.toOrdinary U x
  let f : Map V.underlying.obj.domain W.underlying.obj.domain := Map.inclusion he.ge
  have hf : Function.Bijective f := by
    constructor
    · intro r s h
      have hv := congrArg (fun q : W.underlying.obj.domain => q.val) h
      exact Subtype.ext hv
    · intro r
      exact ⟨⟨r.val,he.le r.property⟩,rfl⟩
  have hPoint (r : RF.underlying.obj.domain) (u : RU.underlying.obj.domain) :
      (⟨(x,(f (rvPackPair RF.underlying.obj.domain RU.underlying.obj.domain r u)).val),
        (f (rvPackPair RF.underlying.obj.domain RU.underlying.obj.domain r u)).property⟩ : (F.mulConstant U).domain) =
      (mixedRVFactorPack F.domain U.underlying.obj.domain).toImage
        ⟨((x,r.val),u.val),r.property,u.property⟩ := Subtype.ext rfl
  have hCoord : ∀ q, W.underlying.obj.value (f q)=V.underlying.obj.value q := by
    intro q
    obtain ⟨r,u,rfl⟩ := exists_rvPackPair RF.underlying.obj.domain RU.underlying.obj.domain q
    rw [zeroProduct_coordinates,rvUnpack_pair]
    change ((F.toOrdinary.mulConstant U).volume ⟨(x,(f (rvPackPair _ _ r u)).val),_⟩).val = _
    rw [hPoint,ordinary_family_positive_coefficient_volume]
    change U.underlying.obj.value (Map.prodSnd _ _ (mixedRVFactorUnpack F.domain U.underlying.obj.domain
      ((mixedRVFactorPack F.domain U.underlying.obj.domain).toImage ⟨((x,r.val),u.val),r.property,u.property⟩))) = _
    rw [mixed_rv_factor_unpack_pack]
    rfl
  have hForm : ∀ q, W.form.value (f q)=V.form.value q := by
    intro q
    obtain ⟨r,u,rfl⟩ := exists_rvPackPair RF.underlying.obj.domain RU.underlying.obj.domain q
    rw [zeroProduct_density,rvUnpack_pair]
    change (F.mulConstant U).form.value ⟨(x,(f (rvPackPair _ _ r u)).val),_⟩ = _
    rw [hPoint]
    change F.form.value (Map.prodFst _ _ (mixedRVFactorUnpack F.domain U.underlying.obj.domain
      ((mixedRVFactorPack F.domain U.underlying.obj.domain).toImage ⟨((x,r.val),u.val),r.property,u.property⟩))) *
      U.form.value (Map.prodSnd _ _ (mixedRVFactorUnpack F.domain U.underlying.obj.domain
      ((mixedRVFactorPack F.domain U.underlying.obj.domain).toImage ⟨((x,r.val),u.val),r.property,u.property⟩))) = _
    rw [mixed_rv_factor_unpack_pack]
    rfl
  exact (RVVolumeIso.of_preserving_coordinates_full hc D
    (rvFiniteIsoOfAmbient (rvIsoOfVolumePreservingBijection f hf hCoord)) hCoord hForm).symm hc D

theorem zero_family_positive_coefficient_row_class
    (hc : CanonicalStructure.IsCanonical (M := M))
    (F : ZeroVFVolumeFamily C n a) (U : PositiveRVVolumeObject (M := M) (C.base : Set M) p)
    (x : Fin n → VFType (M := M)) :
    positiveVolumeBlowupClass hc (vfParameterVolumeContext C x) ((F.mulConstant U).rowInContext x) =
      rvVolumeBlowupClass hc (vfParameterVolumeContext C x) (n := 0) (F.rowInContext x) •
        positiveVolumeBlowupClass hc (vfParameterVolumeContext C x) (positiveVolumeCoefficientInContext U x) := by
  let D := vfParameterVolumeContext C x
  let RF := F.rowInContext x
  let RU := positiveVolumeCoefficientInContext U x
  exact (positiveVolumeBlowupClass_iso hc D (zeroFamilyPositiveCoefficientRowIso hc F U x)).trans
    ((positiveVolumeBlowupClass_iso hc D (mixedProductSwapIso hc D RU RF)).symm.trans
      ((positiveVolumeBlowupClass_iso hc D (productPositiveZeroIso hc D RU RF)).symm.trans
        (zero_volume_coefficient_smul_eq_right_product hc D (rvVolumeBlowupClass hc D RF)
          (positiveVolumeBlowupClass hc D RU)).symm))

end IntegrationInACVF.Section7.HK
