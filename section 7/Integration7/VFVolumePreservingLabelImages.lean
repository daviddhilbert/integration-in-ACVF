module

public import Integration7.VFVolumeBijections

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! An injective definable relabelling that fixes all VF coordinates
gives a genuine full VF volume image. Finite RV fibres and the original
density are transported through its actual definable inverse. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.DefinableGeometry

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {k b : ℕ}

theorem positive_vf_fixed_base_points_finite (U : PositiveVFVolumeObject (M := M) S k)
    (x : (rawVFSpace (M := M) (k+1)).Carrier) : {q : U.domain | q.val.1=x}.Finite := by
  apply (U.finite_labels x).of_injOn (f := fun q : U.domain => q.val.2)
  · intro q hq
    exact Eq.mp (congrArg (fun y => (y,q.val.2) ∈ U.domain.carrier) hq) q.property
  · intro q hq r hr he
    exact Subtype.ext (Prod.ext (hq.trans hr.symm) he)

theorem vf_label_image_to_image_bijective
    {U : PositiveVFVolumeObject (M := M) S k}
    (f : Map U.domain (DefSet.univ (rawMixedSpace (M := M) (k+1) b) S)) (hf : Function.Injective f) :
    Function.Bijective f.toImage := by
  constructor
  · intro q r h
    have hv := congrArg Subtype.val h
    exact hf (Subtype.ext hv)
  · rintro ⟨q,r,hr⟩
    exact ⟨r,Subtype.ext hr⟩

def PositiveVFVolumeObject.vfPreservingImage (U : PositiveVFVolumeObject (M := M) S k)
    (f : Map U.domain (DefSet.univ (rawMixedSpace (M := M) (k+1) b) S)) (hf : Function.Injective f)
    (hVF : ∀ q, (f q).val.1=q.val.1) : PositiveVFVolumeObject (M := M) S k where
  arity := b
  domain := f.image
  finite_labels x := by
    apply ((positive_vf_fixed_base_points_finite U x).image (fun q => (f q).val.2)).subset
    rintro r ⟨q,hq⟩
    have hx := congrArg Prod.fst hq
    have hr := congrArg Prod.snd hq
    exact ⟨q,(hVF q).symm.trans hx,hr⟩
  form := U.form.pullback (f.toImage.inverse (vf_label_image_to_image_bijective f hf))

def vfPreservingLabelImageBijection
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (U : PositiveVFVolumeObject (M := M) (C.base : Set M) k)
    (f : Map U.domain (DefSet.univ (rawMixedSpace (M := M) (k+1) b) (C.base : Set M)))
    (hf : Function.Injective f) (hVF : ∀ q, (f q).val.1=q.val.1) :
    VFVolumeBijection U (U.vfPreservingImage f hf hVF) :=
  VFVolumeBijection.of_preserving_vf_and_density hc C f.toImage (vf_label_image_to_image_bijective f hf) hVF
    (fun q => by
      have h := Map.inverse_apply f.toImage (vf_label_image_to_image_bijective f hf) q
      exact congrArg U.form.value h.symm)

end IntegrationInACVF.Section7
