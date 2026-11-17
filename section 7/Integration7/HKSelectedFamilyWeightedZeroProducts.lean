module

public import Integration7.HKZeroFamilyScalarProducts
public import Integration7.HKZeroCoefficientScalarRows
public import Integration7.VolumeFamilyZeroProductRows

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! Weighted zero coefficients act on positive families by a finite RV
factor, multiplying both forms and retaining all selected coordinates. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.DefinableGeometry

namespace IntegrationInACVF.Section7.HK
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {C : BaseContext M} {n a k : ℕ}

def selectedFamilyWeightedZeroProduct (F : SelectedVFVolumeFamily C n a k)
    (Z : ZeroRVVolumeObject (M := M) (C.base : Set M)) :
    SelectedVFVolumeFamily C n (a+Z.underlying.obj.arity) k where
  domain := mixedRVFactorDomain F.domain Z.underlying.obj.domain
  selected := (F.prodZero Z.underlying).selected
  finite_selected := (F.prodZero Z.underlying).finite_selected
  form := (F.form.prod Z.form).pullback (mixedRVFactorUnpack F.domain Z.underlying.obj.domain)

def selectedFamilyWeightedZeroRowIso
    (hc : CanonicalStructure.IsCanonical (M := M))
    (F : SelectedVFVolumeFamily C n a k) (Z : ZeroRVVolumeObject (M := M) (C.base : Set M))
    (x : Fin n → VFType (M := M)) :
    RVVolumeIso ((selectedFamilyWeightedZeroProduct F Z).rowInContext x)
      (positiveZeroProduct (F.rowInContext x) (zeroVolumeCoefficientInContext Z x)) := by
  let D := vfParameterVolumeContext C x
  let U := (selectedFamilyWeightedZeroProduct F Z).rowInContext x
  let V := positiveZeroProduct (F.rowInContext x) (zeroVolumeCoefficientInContext Z x)
  let he := volume_family_zero_product_row_carrier F Z.underlying x
  let f : Map V.underlying.obj.domain U.underlying.obj.domain := Map.inclusion he.ge
  have hf : Function.Bijective f := by
    constructor
    · intro p q h
      have hval := congrArg Subtype.val h
      exact Subtype.ext hval
    · intro p
      exact ⟨⟨p.val,he.le p.property⟩,rfl⟩
  have hCoord : ∀ p, U.underlying.obj.value (f p) = V.underlying.obj.value p := by
    intro p
    let q := rvUnpack (F.rowInContext x).underlying.obj.domain
      (zeroVolumeCoefficientInContext Z x).underlying.obj.domain p
    have h := congrArg Subtype.val (rvPack_unpack (F.rowInContext x).underlying.obj.domain
      (zeroVolumeCoefficientInContext Z x).underlying.obj.domain p)
    change Fin.append (m := a) (n := Z.underlying.obj.arity) q.val.1 q.val.2 = p.val at h
    rw [positiveZeroProduct_coordinates]
    change p.val ∘ (Fin.castAdd Z.underlying.obj.arity ∘ F.selected) = q.val.1 ∘ F.selected
    funext i
    simpa only [Fin.append_left,Function.comp_apply] using
      (congrFun h (Fin.castAdd Z.underlying.obj.arity (F.selected i))).symm
  have hForm : ∀ p, U.form.value (f p) = V.form.value p := by
    intro p
    let q := rvUnpack (F.rowInContext x).underlying.obj.domain
      (zeroVolumeCoefficientInContext Z x).underlying.obj.domain p
    let t := mixedRVFactorUnpack F.domain Z.underlying.obj.domain
      (⟨(x,p.val),(f p).property⟩ : (selectedFamilyWeightedZeroProduct F Z).domain)
    have ht := mixed_rv_factor_unpack_value F.domain Z.underlying.obj.domain
      (⟨(x,p.val),(f p).property⟩ : (selectedFamilyWeightedZeroProduct F Z).domain)
    have h := congrArg Subtype.val (rvPack_unpack (F.rowInContext x).underlying.obj.domain
      (zeroVolumeCoefficientInContext Z x).underlying.obj.domain p)
    change Fin.append (m := a) (n := Z.underlying.obj.arity) q.val.1 q.val.2 = p.val at h
    have hLeft : q.val.1 = p.val ∘ Fin.castAdd Z.underlying.obj.arity := by
      funext i
      exact (Fin.append_left (m := a) (n := Z.underlying.obj.arity) q.val.1 q.val.2 i).symm.trans
        (congrFun h (Fin.castAdd Z.underlying.obj.arity i))
    have hRight : q.val.2 = p.val ∘ Fin.natAdd a := by
      funext i
      exact (Fin.append_right (m := a) (n := Z.underlying.obj.arity) q.val.1 q.val.2 i).symm.trans
        (congrFun h (Fin.natAdd a i))
    calc
      U.form.value (f p) = F.form.value (Map.prodFst _ _ t) * Z.form.value (Map.prodSnd _ _ t) := rfl
      _ = (F.rowInContext x).form.value (Map.prodFst _ _ q) *
          (zeroVolumeCoefficientInContext Z x).form.value (Map.prodSnd _ _ q) := by
        congr 1
        · change F.form.value (Map.prodFst _ _ t) = F.form.value ⟨(x,q.val.1),q.property.1⟩
          congr 1
          apply Subtype.ext
          exact (congrArg Prod.fst ht).trans (congrArg (fun r => (x,r)) hLeft).symm
        · change Z.form.value (Map.prodSnd _ _ t) = Z.form.value ⟨q.val.2,q.property.2⟩
          congr 1
          apply Subtype.ext
          exact (congrArg Prod.snd ht).trans hRight.symm
      _ = V.form.value p := (positiveZeroProduct_density (F.rowInContext x) (zeroVolumeCoefficientInContext Z x) p).symm
  exact (RVVolumeIso.of_preserving_coordinates_full hc D
    (rvFiniteIsoOfAmbient (rvIsoOfVolumePreservingBijection f hf hCoord)) hCoord hForm).symm hc D

theorem selected_family_weighted_zero_row_scalar
    (hc : CanonicalStructure.IsCanonical (M := M))
    (F : SelectedVFVolumeFamily C n a k) (Z : ZeroRVVolumeObject (M := M) (C.base : Set M))
    (x : Fin n → VFType (M := M)) :
    positiveVolumeBlowupClass hc (vfParameterVolumeContext C x)
      ((selectedFamilyWeightedZeroProduct F Z).rowInContext x) =
      zeroVolumeCoefficientExtend hc C (vfParameterVolumeContext C x)
        (fun _ h => vfParameterVolumeContext_contains C x (Or.inl h)) (rvVolumeBlowupClass hc C Z) •
          positiveVolumeBlowupClass hc (vfParameterVolumeContext C x) (F.rowInContext x) := by
  let D := vfParameterVolumeContext C x
  let z := zeroVolumeCoefficientInContext Z x
  have hRow := positiveVolumeBlowupClass_iso hc D (selectedFamilyWeightedZeroRowIso hc F Z x)
  have hProduct := positiveVolumeBlowupClass_iso hc D (productPositiveZeroIso hc D (F.rowInContext x) z)
  have hScalar := zero_volume_coefficient_smul_eq_right_product hc D (rvVolumeBlowupClass hc D z)
    (positiveVolumeBlowupClass hc D (F.rowInContext x))
  exact hRow.trans (hProduct.symm.trans hScalar.symm)

end IntegrationInACVF.Section7.HK
