module

public import Integration7.FixedVFVolumeCoproducts
public import Integration7.VFVolumeBijections

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! Adding either disjoint RV tag is a full volume bijection and fixes
every VF coordinate. The tagged forms are literal pullbacks. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {k : ℕ}

def PositiveVFVolumeObject.leftTagged (U : PositiveVFVolumeObject (M := M) S k) (b : ℕ) :
    PositiveVFVolumeObject (M := M) S k where
  arity := 1+(U.arity+b)
  domain := (fixedVFLeftTagMap U.domain b).image
  finite_labels := fixed_vf_left_tag_finite_labels U.domain b U.finite_labels
  form := U.form.pullback (fixedVFUntagLeft U.domain b)

def PositiveVFVolumeObject.rightTagged (V : PositiveVFVolumeObject (M := M) S k) (a : ℕ) :
    PositiveVFVolumeObject (M := M) S k where
  arity := 1+(a+V.arity)
  domain := (fixedVFRightTagMap V.domain a).image
  finite_labels := fixed_vf_right_tag_finite_labels V.domain a V.finite_labels
  form := V.form.pullback (fixedVFUntagRight V.domain a)

def vfVolumeLeftTagBijection
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (U : PositiveVFVolumeObject (M := M) (C.base : Set M) k) (b : ℕ) :
    VFVolumeBijection U (U.leftTagged b) :=
  VFVolumeBijection.of_preserving_vf_and_density hc C
    (fixedVFLeftTagMap U.domain b).toImage
    (fixed_vf_left_tag_to_image_bijective U.domain b) (fun _ => rfl)
    (fun p => (congrArg U.form.value (Map.inverse_apply _ _ p)).symm)

def vfVolumeRightTagBijection
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (V : PositiveVFVolumeObject (M := M) (C.base : Set M) k) (a : ℕ) :
    VFVolumeBijection V (V.rightTagged a) :=
  VFVolumeBijection.of_preserving_vf_and_density hc C
    (fixedVFRightTagMap V.domain a).toImage
    (fixed_vf_right_tag_to_image_bijective V.domain a) (fun _ => rfl)
    (fun p => (congrArg V.form.value (Map.inverse_apply _ _ p)).symm)

end IntegrationInACVF.Section7
