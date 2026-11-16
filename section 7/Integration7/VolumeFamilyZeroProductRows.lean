module

public import Integration7.SelectedVolumeFamilyZeroProducts
public import Integration7.SelectedVolumeRowContexts
public import Integration7.VolumeBlowupClasses
public import Section4.RVProductRestrictions

@[expose] public section

/-! Each fibre of the family product by an ordinary RV[0] coefficient
is the actual RV product, with identical selected coordinates and density. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.DefinableGeometry

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {C : BaseContext M} {n a k : ℕ}

def ordinaryVolumeCoefficientInContext (Z : RVFiniteObject (M := M) (C.base : Set M) 0)
    (x : Fin n → VFType (M := M)) :
    RVFiniteObject (M := M) ((vfParameterVolumeContext C x).base : Set M) 0 :=
  Section6.FiniteRV.extendObject
    (fun _ h => vfParameterVolumeContext_contains C x (Or.inl h)) Z

theorem volume_family_zero_product_row_carrier
    (F : SelectedVFVolumeFamily C n a k) (Z : RVFiniteObject (M := M) (C.base : Set M) 0)
    (x : Fin n → VFType (M := M)) :
    ((F.prodZero Z).rowInContext x).underlying.obj.domain.carrier =
      ((F.rowInContext x).prod_zero (ordinaryVolumeCoefficientInContext Z x)).underlying.obj.domain.carrier := by
  ext r
  change (x,r) ∈ (mixedRVFactorDomain F.domain Z.obj.domain).carrier ↔
    r ∈ (rvProductDomain (F.rowInContext x).underlying.obj.domain
      (ordinaryVolumeCoefficientInContext Z x).obj.domain).carrier
  rw [mem_mixed_rv_factor_domain,mem_rvProductDomain]
  constructor
  · rintro ⟨hF,hZ⟩
    exact ⟨r ∘ Fin.castAdd Z.obj.arity,hF,r ∘ Fin.natAdd a,hZ,Fin.append_castAdd_natAdd⟩
  · rintro ⟨u,hu,v,hv,hr⟩
    change (x,u) ∈ F.domain.carrier at hu
    change v ∈ Z.obj.domain.carrier at hv
    rw [← hr]
    change (x,Fin.append (m := a) (n := Z.obj.arity) u v ∘ Fin.castAdd Z.obj.arity) ∈ F.domain.carrier ∧
      Fin.append (m := a) (n := Z.obj.arity) u v ∘ Fin.natAdd a ∈ Z.obj.domain.carrier
    simpa only [rvAppend,Function.comp_def,Fin.append_left,Fin.append_right] using And.intro hu hv

def volumeFamilyZeroProductRowIso
    (hc : CanonicalStructure.IsCanonical (M := M))
    (F : SelectedVFVolumeFamily C n a k) (Z : RVFiniteObject (M := M) (C.base : Set M) 0)
    (x : Fin n → VFType (M := M)) :
    RVVolumeIso ((F.prodZero Z).rowInContext x)
      ((F.rowInContext x).prod_zero (ordinaryVolumeCoefficientInContext Z x)) := by
  let D := vfParameterVolumeContext C x
  let U := (F.prodZero Z).rowInContext x
  let V := (F.rowInContext x).prod_zero (ordinaryVolumeCoefficientInContext Z x)
  let he := volume_family_zero_product_row_carrier F Z x
  let f : Map V.underlying.obj.domain U.underlying.obj.domain := Map.inclusion he.ge
  have hf : Function.Bijective f := by
    constructor
    · intro p q h
      have hv := congrArg Subtype.val h
      exact Subtype.ext hv
    · intro p
      exact ⟨⟨p.val,he.le p.property⟩,rfl⟩
  have hCoord : ∀ p, U.underlying.obj.value (f p) = V.underlying.obj.value p := by
    intro p
    let A := (F.rowInContext x).underlying.obj.domain
    let B := (ordinaryVolumeCoefficientInContext Z x).obj.domain
    let q := rvUnpack A B p
    have h := congrArg (fun z : rvProductDomain A B => z.val) (rvPack_unpack A B p)
    change Fin.append (m := a) (n := Z.obj.arity) q.val.1 q.val.2 = p.val at h
    rw [positiveZeroProduct_coordinates]
    change p.val ∘ (Fin.castAdd Z.obj.arity ∘ F.selected) = q.val.1 ∘ F.selected
    funext i
    simpa only [Fin.append_left,Function.comp_apply] using (congrFun h (Fin.castAdd Z.obj.arity (F.selected i))).symm
  have hForm : ∀ p, U.form.value (f p) = V.form.value p := by
    intro p
    let A := (F.rowInContext x).underlying.obj.domain
    let B := (ordinaryVolumeCoefficientInContext Z x).obj.domain
    let q := rvUnpack A B p
    have h := congrArg (fun z : rvProductDomain A B => z.val) (rvPack_unpack A B p)
    change Fin.append (m := a) (n := Z.obj.arity) q.val.1 q.val.2 = p.val at h
    have hPrefix : p.val ∘ Fin.castAdd Z.obj.arity = q.val.1 := by
      funext i
      simpa only [Fin.append_left,Function.comp_apply] using (congrFun h (Fin.castAdd Z.obj.arity i)).symm
    have hBase : F.prodZeroProjection Z ⟨(x,p.val),(f p).property⟩ = ⟨(x,q.val.1),q.property.1⟩ := by
      apply Subtype.ext
      exact (F.prodZeroProjection_value Z _).trans (Prod.ext rfl hPrefix)
    change F.form.value (F.prodZeroProjection Z ⟨(x,p.val),(f p).property⟩) =
      F.form.value ⟨(x,q.val.1),q.property.1⟩
    rw [hBase]
  exact (RVVolumeIso.of_preserving_coordinates_full hc D
    (rvFiniteIsoOfAmbient (rvIsoOfVolumePreservingBijection f hf hCoord)) hCoord hForm).symm hc D

end IntegrationInACVF.Section7
