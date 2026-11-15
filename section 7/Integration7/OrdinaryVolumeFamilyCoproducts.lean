import Integration7.OrdinaryVFVolumeFamilies
import Integration7.FixedVFVolumeCoproducts
import Integration7.AllDegreeVolumeClasses
import Integration7.NondegenerateFiniteIso
import Integration7.OrdinaryVolumeCoefficientCommSemiring

/-! Ordinary degree-zero families are closed under actual disjoint
RV-label coproducts, and their row classes add pointwise. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.DefinableGeometry
open scoped DirectSum

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {C : BaseContext M} {n a b : ℕ}

def OrdinaryVFVolumeFamily.coprod (F : OrdinaryVFVolumeFamily C n a) (G : OrdinaryVFVolumeFamily C n b) :
    OrdinaryVFVolumeFamily C n (1+(a+b)) where
  domain := (fixedVFLeftTagMap F.domain b).image.union (fixedVFRightTagMap G.domain a).image
  finite_labels x := (fixed_vf_left_tag_finite_labels F.domain b F.finite_labels x).union
    (fixed_vf_right_tag_finite_labels G.domain a G.finite_labels x)

theorem ordinary_volume_family_coprod_row_carrier
    (F : OrdinaryVFVolumeFamily C n a) (G : OrdinaryVFVolumeFamily C n b)
    (x : Fin n → VFType (M := M)) :
    ((F.coprod G).rowInContext x).obj.domain.carrier =
      (rvFiniteCoprodObject (F.rowInContext x) (G.rowInContext x)).obj.domain.carrier := by
  ext r
  constructor
  · rintro (⟨u,hu⟩ | ⟨v,hv⟩)
    · left
      change (u.val.1,rvLeftTag b u.val.2)=(x,r) at hu
      have hx := congrArg Prod.fst hu
      have hr := congrArg Prod.snd hu
      have hm : (x,u.val.2) ∈ F.domain.carrier := by
        have h := u.property
        change (u.val.1,u.val.2) ∈ F.domain.carrier at h
        change u.val.1=x at hx
        rw [hx] at h
        exact h
      exact ⟨⟨u.val.2,hm⟩,hr⟩
    · right
      change (v.val.1,rvRightTag a v.val.2)=(x,r) at hv
      have hx := congrArg Prod.fst hv
      have hr := congrArg Prod.snd hv
      have hm : (x,v.val.2) ∈ G.domain.carrier := by
        have h := v.property
        change (v.val.1,v.val.2) ∈ G.domain.carrier at h
        change v.val.1=x at hx
        rw [hx] at h
        exact h
      exact ⟨⟨v.val.2,hm⟩,hr⟩
  · rintro (⟨u,hu⟩ | ⟨v,hv⟩)
    · exact Or.inl ⟨⟨(x,u.val),u.property⟩,Prod.ext rfl hu⟩
    · exact Or.inr ⟨⟨(x,v.val),v.property⟩,Prod.ext rfl hv⟩

def ordinaryVolumeFamilyCoprodRowIso
    (F : OrdinaryVFVolumeFamily C n a) (G : OrdinaryVFVolumeFamily C n b)
    (x : Fin n → VFType (M := M)) :
    (F.coprod G).rowInContext x ≅ rvFiniteCoprodObject (F.rowInContext x) (G.rowInContext x) := by
  let U := (F.coprod G).rowInContext x
  let V := rvFiniteCoprodObject (F.rowInContext x) (G.rowInContext x)
  have hUV := ordinary_volume_family_coprod_row_carrier F G x
  let f : Map U.obj.domain V.obj.domain := Map.inclusion (fun r hr => (Set.ext_iff.mp hUV r).mp hr)
  have hf : Function.Bijective f := by
    constructor
    · intro r s h
      have he := congrArg (fun q : V.obj.domain => q.val) h
      exact Subtype.ext he
    · intro v
      exact ⟨⟨v.val,(Set.ext_iff.mp hUV v.val).mpr v.property⟩,rfl⟩
  exact finiteIsoOfNondegenerateBijection f hf (fun _ i => i.elim0) (fun _ i => i.elim0)

theorem ordinary_volume_family_coprod_row_class
    (hc : CanonicalStructure.IsCanonical (M := M))
    (F : OrdinaryVFVolumeFamily C n a) (G : OrdinaryVFVolumeFamily C n b)
    (x : Fin n → VFType (M := M)) :
    rvVolumeBlowupClass hc (vfParameterVolumeContext C x) (n := 0) ((F.coprod G).rowInContext x) =
      rvVolumeBlowupClass hc (vfParameterVolumeContext C x) (n := 0) (F.rowInContext x) +
        rvVolumeBlowupClass hc (vfParameterVolumeContext C x) (n := 0) (G.rowInContext x) :=
  Quotient.sound ⟨ordinaryVolumeFamilyCoprodRowIso F G x⟩

end IntegrationInACVF.Section7
