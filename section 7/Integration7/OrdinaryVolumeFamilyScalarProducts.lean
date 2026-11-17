module

public import Integration7.OrdinaryVFVolumeFamilies
public import Integration7.SelectedVolumeFamilyZeroProducts
public import Integration7.VolumeFamilyZeroProductRows
public import Integration7.OrdinaryVolumeCoefficientExtensions
public import Integration7.OrdinaryVolumeCoefficientCommSemiring

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! An ordinary coefficient acts on an ordinary family by an actual
finite RV factor, and every row computes the extended coefficient product. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.DefinableGeometry
open scoped DirectSum

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {C : BaseContext M} {n a : ℕ}

def OrdinaryVFVolumeFamily.prodZero (F : OrdinaryVFVolumeFamily C n a)
    (Z : RVFiniteObject (M := M) (C.base : Set M) 0) : OrdinaryVFVolumeFamily C n (a+Z.obj.arity) where
  domain := mixedRVFactorDomain F.domain Z.obj.domain
  finite_labels x := by
    apply (((F.finite_labels x).prod (ordinary_zero_volume_domain_finite Z)).image
      (fun q => Fin.append q.1 q.2)).subset
    intro r hr
    have h := (mem_mixed_rv_factor_domain F.domain Z.obj.domain x r).mp hr
    exact ⟨(r ∘ Fin.castAdd Z.obj.arity,r ∘ Fin.natAdd a),h,Fin.append_castAdd_natAdd⟩

theorem ordinary_volume_family_scalar_row_carrier
    (F : OrdinaryVFVolumeFamily C n a) (Z : RVFiniteObject (M := M) (C.base : Set M) 0)
    (x : Fin n → VFType (M := M)) :
    ((F.prodZero Z).rowInContext x).obj.domain.carrier =
      (rvFiniteProductObject (F.rowInContext x) (ordinaryVolumeCoefficientInContext Z x)).obj.domain.carrier := by
  ext r
  change (x,r) ∈ (mixedRVFactorDomain F.domain Z.obj.domain).carrier ↔
    r ∈ (rvProductDomain (F.rowInContext x).obj.domain (ordinaryVolumeCoefficientInContext Z x).obj.domain).carrier
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

def ordinaryVolumeFamilyScalarRowIso
    (F : OrdinaryVFVolumeFamily C n a) (Z : RVFiniteObject (M := M) (C.base : Set M) 0)
    (x : Fin n → VFType (M := M)) :
    (F.prodZero Z).rowInContext x ≅ rvFiniteProductObject (F.rowInContext x) (ordinaryVolumeCoefficientInContext Z x) := by
  let U := (F.prodZero Z).rowInContext x
  let V := rvFiniteProductObject (F.rowInContext x) (ordinaryVolumeCoefficientInContext Z x)
  have he := ordinary_volume_family_scalar_row_carrier F Z x
  let f : Map U.obj.domain V.obj.domain := Map.inclusion he.le
  have hf : Function.Bijective f := by
    constructor
    · intro u v h
      have hval := congrArg (fun q : V.obj.domain => q.val) h
      exact Subtype.ext hval
    · intro v
      exact ⟨⟨v.val,he.ge v.property⟩,rfl⟩
  exact finiteIsoOfNondegenerateBijection f hf (fun _ i => i.elim0) (fun _ i => i.elim0)

theorem ordinary_volume_family_scalar_row_class
    (hc : CanonicalStructure.IsCanonical (M := M))
    (F : OrdinaryVFVolumeFamily C n a) (Z : RVFiniteObject (M := M) (C.base : Set M) 0)
    (x : Fin n → VFType (M := M)) :
    rvVolumeBlowupClass hc (vfParameterVolumeContext C x) (n := 0) ((F.prodZero Z).rowInContext x) =
      ordinaryVolumeCoefficientExtend hc C (vfParameterVolumeContext C x)
        (fun _ h => vfParameterVolumeContext_contains C x (Or.inl h)) (rvVolumeBlowupClass hc C (n := 0) Z) *
          rvVolumeBlowupClass hc (vfParameterVolumeContext C x) (n := 0) (F.rowInContext x) := by
  rw [mul_comm]
  exact Quotient.sound ⟨ordinaryVolumeFamilyScalarRowIso F Z x⟩

end IntegrationInACVF.Section7
