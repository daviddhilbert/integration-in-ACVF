import Integration7.HKAEZeroVolumeFunctions
import Integration7.HKVolumeClassCoherence
import Integration7.OrdinaryVolumeFamilyCoproducts
import Integration7.OrdinaryZeroVolumeFamilies

/-! Actual weighted family coproducts, with the pointwise zero coefficient
addition. The form is glued on the actual tagged domains. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.DefinableGeometry

namespace IntegrationInACVF.Section7.HK
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {C : BaseContext M} {n a b : ℕ}

def ZeroVFVolumeFamily.coprod (F : ZeroVFVolumeFamily C (n+1) a)
    (G : ZeroVFVolumeFamily C (n+1) b) : ZeroVFVolumeFamily C (n+1) (1+(a+b)) :=
  let A := F.fullVFObject.coprod G.fullVFObject
  ⟨A.domain,A.finite_labels,A.form⟩

@[simp] theorem ZeroVFVolumeFamily.coprod_full_object (F : ZeroVFVolumeFamily C (n+1) a)
    (G : ZeroVFVolumeFamily C (n+1) b) :
    (F.coprod G).fullVFObject = F.fullVFObject.coprod G.fullVFObject := rfl

def zeroFamilyCoprodRowIso (F : ZeroVFVolumeFamily C (n+1) a)
    (G : ZeroVFVolumeFamily C (n+1) b) (x : Fin (n+1) → VFType (M := M)) :
    ZeroRVVolumeIso ((F.coprod G).rowInContext x)
      (coprod _ 0 (F.rowInContext x) (G.rowInContext x)) := by
  let U := F.rowInContext x
  let V := G.rowInContext x
  let e := ordinaryVolumeFamilyCoprodRowIso F.toOrdinary G.toOrdinary x
  refine ⟨e,?_⟩
  intro r
  rcases zero_coprod_cases U V (finiteIsoMap e r) with ⟨u,hu⟩ | ⟨v,hv⟩
  · let p : F.domain := ⟨(x,u.val),u.property⟩
    have hp : (⟨(x,r.val),r.property⟩ : (F.fullVFObject.coprod G.fullVFObject).domain) =
        vfVolumeCoprodLeftMap F.fullVFObject G.fullVFObject p := by
      apply Subtype.ext
      exact Prod.ext rfl (congrArg Subtype.val hu).symm
    change (F.fullVFObject.coprod G.fullVFObject).form.value ⟨(x,r.val),r.property⟩ =
      (coprod _ 0 U V).form.value (finiteIsoMap e r)
    rw [hp,vf_volume_coprod_density_left]
    exact (coprod_density_left 0 U V u).symm.trans (congrArg (coprod _ 0 U V).form.value hu)
  · let p : G.domain := ⟨(x,v.val),v.property⟩
    have hp : (⟨(x,r.val),r.property⟩ : (F.fullVFObject.coprod G.fullVFObject).domain) =
        vfVolumeCoprodRightMap F.fullVFObject G.fullVFObject p := by
      apply Subtype.ext
      exact Prod.ext rfl (congrArg Subtype.val hv).symm
    change (F.fullVFObject.coprod G.fullVFObject).form.value ⟨(x,r.val),r.property⟩ =
      (coprod _ 0 U V).form.value (finiteIsoMap e r)
    rw [hp,vf_volume_coprod_density_right]
    exact (coprod_density_right 0 U V v).symm.trans (congrArg (coprod _ 0 U V).form.value hv)

theorem zero_family_coprod_row_class (hc : CanonicalStructure.IsCanonical (M := M))
    (F : ZeroVFVolumeFamily C (n+1) a) (G : ZeroVFVolumeFamily C (n+1) b)
    (x : Fin (n+1) → VFType (M := M)) :
    rvVolumeBlowupClass hc (vfParameterVolumeContext C x) (n := 0) ((F.coprod G).rowInContext x) =
      rvVolumeBlowupClass hc (vfParameterVolumeContext C x) (n := 0) (F.rowInContext x) +
        rvVolumeBlowupClass hc (vfParameterVolumeContext C x) (n := 0) (G.rowInContext x) :=
  Quotient.sound ⟨zeroFamilyCoprodRowIso F G x⟩

def zeroFamily (C : BaseContext M) (n : ℕ) : ZeroVFVolumeFamily C n 0 :=
  ZeroVFVolumeFamily.ofOrdinary (ordinaryZeroVolumeFamily C n)

theorem zero_family_row_class (hc : CanonicalStructure.IsCanonical (M := M))
    (C : BaseContext M) (n : ℕ) (x : Fin n → VFType (M := M)) :
    rvVolumeBlowupClass hc (vfParameterVolumeContext C x) (n := 0) ((zeroFamily C n).rowInContext x) = 0 := by
  let U := (zeroFamily C n).rowInContext x
  let V := empty ((vfParameterVolumeContext C x).base : Set M) 0
  let f : Map U.underlying.obj.domain V.underlying.obj.domain := Map.fromEmpty rfl V.underlying.obj.domain
  exact Quotient.sound ⟨ZeroRVVolumeIso.ofBijection f (Map.bijective_of_empty f rfl rfl)
    (fun u => u.property.elim)⟩

end IntegrationInACVF.Section7.HK
