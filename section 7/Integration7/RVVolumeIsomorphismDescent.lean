import Integration7.RVJacobianAlmostEverywhereDescent
import Integration7.RVVolumeLiftIsomorphism
import Integration7.VolumeIsoParameterExtension

/-! A volume isomorphism over a containing context descends whenever
its actual essential bijection is already defined over the original base. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.Section7
open SpecialTransformations.DefinableGeometry

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {k : ℕ}

def RVVolumeIso.descend
    (hc : CanonicalStructure.IsCanonical (M := M)) (C D : BaseContext M)
    (hCD : (C.base : Set M) ⊆ (D.base : Set M))
    {U V : PositiveRVVolumeObject (M := M) (C.base : Set M) k}
    (f : RVVolumeIso (U.extend hCD) (V.extend hCD)) (e : U.essential ≅ V.essential)
    (hmap : ∀ u : (U.extend hCD).essential.obj.domain,
      (finiteIsoMap f.iso u).val = (finiteIsoMap e ⟨u.val,u.property⟩).val) : RVVolumeIso U V := by
  have hpoint (u : (U.extend hCD).essential.obj.domain) :
      (⟨(finiteIsoMap f.iso u).val,(finiteIsoMap f.iso u).property⟩ : V.essential.obj.domain) =
        finiteIsoMap e ⟨u.val,u.property⟩ := Subtype.ext (hmap u)
  have hCorr : (volumeCorrespondence (finiteIsoMap f.iso)).carrier =
      (volumeCorrespondence (finiteIsoMap e)).carrier := by
    ext z
    constructor
    · rintro ⟨u,rfl⟩
      refine ⟨⟨u.val,u.property⟩,?_⟩
      change productTuple (U.essential.obj.value ⟨u.val,u.property⟩)
        (V.essential.obj.value (finiteIsoMap e ⟨u.val,u.property⟩)) =
        productTuple (U.essential.obj.value ⟨u.val,u.property⟩)
        (V.essential.obj.value ⟨(finiteIsoMap f.iso u).val,(finiteIsoMap f.iso u).property⟩)
      rw [hpoint]
    · rintro ⟨u,rfl⟩
      refine ⟨⟨u.val,u.property⟩,?_⟩
      change productTuple (U.essential.obj.value u)
        (V.essential.obj.value ⟨(finiteIsoMap f.iso ⟨u.val,u.property⟩).val,
          (finiteIsoMap f.iso ⟨u.val,u.property⟩).property⟩) =
        productTuple (U.essential.obj.value u) (V.essential.obj.value (finiteIsoMap e u))
      rw [hpoint]
  refine ⟨e,?_,?_⟩
  · intro u
    have h := f.gamma ⟨u.val,u.property⟩
    change Values.vrv (U.essentialForm.value u) =
      Values.vrv (V.essentialForm.value
        ⟨(finiteIsoMap f.iso ⟨u.val,u.property⟩).val,(finiteIsoMap f.iso ⟨u.val,u.property⟩).property⟩) *
        (rvGammaJacobian (U.essential.obj.value u)
          (V.essential.obj.value ⟨(finiteIsoMap f.iso ⟨u.val,u.property⟩).val,
            (finiteIsoMap f.iso ⟨u.val,u.property⟩).property⟩) _ _).val at h
    simpa only [hpoint] using h
  · have hRV : RVAlmostEverywhere (U.essential.obj.domain.extend hCD) (k+1) (fun u =>
        IsRVJacobianAt (volumeCorrespondence (finiteIsoMap e)).carrier
          (U.essential.obj.value ⟨u.val,u.property⟩) (V.essential.obj.value (finiteIsoMap e ⟨u.val,u.property⟩))
          ((volumeRatioMap e ⟨u.val,u.property⟩).val 0)) := by
      apply f.rv.mono
      intro u hu
      rw [hCorr] at hu
      change IsRVJacobianAt (volumeCorrespondence (finiteIsoMap e)).carrier
        (U.essential.obj.value ⟨u.val,u.property⟩)
        (V.essential.obj.value ⟨(finiteIsoMap f.iso u).val,(finiteIsoMap f.iso u).property⟩)
        (U.essentialForm.value ⟨u.val,u.property⟩ /
          V.essentialForm.value ⟨(finiteIsoMap f.iso u).val,(finiteIsoMap f.iso u).property⟩) at hu
      simpa only [volumeRatioMap_value,volumeRatio,hpoint] using hu
    simpa only [volumeRatioMap_value] using
      rv_jacobian_ae_descend hc C D hCD (Nat.zero_lt_succ k) e U.essential_nonzero V.essential_nonzero
      (volumeRatioMap e) hRV

end IntegrationInACVF.Section7
