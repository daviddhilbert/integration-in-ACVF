module

public import Integration7.HKSupportedZeroFunctionAddition

@[expose] public section

/-! A VF base bijection commutes with the actual RV-tagged coproduct.
Both transformed summands retain the same inverse-Jacobian density factor. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.DefinableGeometry

namespace IntegrationInACVF.Section7.HK
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {C : BaseContext M} {n a b : ℕ}
variable {X Y : DefSet (rawVFSpace (M := M) (n+1)) (C.base : Set M)}
variable (F : ZeroVFVolumeFamily C (n+1) a) (G : ZeroVFVolumeFamily C (n+1) b)
variable (φ : Map X Y) (hφ : Function.Bijective φ)
variable (hF : ∀ p : F.domain, p.val.1 ∈ X.carrier) (hG : ∀ p : G.domain, p.val.1 ∈ X.carrier)

theorem zero_base_coprod_left_value (u : F.domain) :
    ((mixedVFBaseMap φ (F.coprod G).domain (zero_family_coprod_supported F G hF hG)).toImage
      (vfVolumeCoprodLeftMap F.fullVFObject G.fullVFObject u)).val =
    (vfVolumeCoprodLeftMap (F.jacobianPushforward φ hφ hF).fullVFObject
      (G.jacobianPushforward φ hφ hG).fullVFObject ((mixedVFBaseMap φ F.domain hF).toImage u)).val := rfl

theorem zero_base_coprod_right_value (v : G.domain) :
    ((mixedVFBaseMap φ (F.coprod G).domain (zero_family_coprod_supported F G hF hG)).toImage
      (vfVolumeCoprodRightMap F.fullVFObject G.fullVFObject v)).val =
    (vfVolumeCoprodRightMap (F.jacobianPushforward φ hφ hF).fullVFObject
      (G.jacobianPushforward φ hφ hG).fullVFObject ((mixedVFBaseMap φ G.domain hG).toImage v)).val := rfl

theorem zero_jacobian_coprod_domain :
    ((F.coprod G).jacobianPushforward φ hφ (zero_family_coprod_supported F G hF hG)).domain.carrier =
      ((F.jacobianPushforward φ hφ hF).coprod (G.jacobianPushforward φ hφ hG)).domain.carrier := by
  let A := F.jacobianPushforward φ hφ hF
  let B := G.jacobianPushforward φ hφ hG
  ext q
  constructor
  · rintro ⟨p,rfl⟩
    rcases vf_volume_coprod_cases F.fullVFObject G.fullVFObject p with ⟨u,rfl⟩ | ⟨v,rfl⟩
    · exact Eq.mpr (congrArg (fun z : (rawMixedSpace (M := M) (n+1) (1+(a+b))).Carrier =>
        z ∈ (A.coprod B).domain.carrier) (zero_base_coprod_left_value F G φ hφ hF hG u))
        (vfVolumeCoprodLeftMap A.fullVFObject B.fullVFObject ((mixedVFBaseMap φ F.domain hF).toImage u)).property
    · exact Eq.mpr (congrArg (fun z : (rawMixedSpace (M := M) (n+1) (1+(a+b))).Carrier =>
        z ∈ (A.coprod B).domain.carrier) (zero_base_coprod_right_value F G φ hφ hF hG v))
        (vfVolumeCoprodRightMap A.fullVFObject B.fullVFObject ((mixedVFBaseMap φ G.domain hG).toImage v)).property
  · intro hq
    rcases vf_volume_coprod_cases A.fullVFObject B.fullVFObject ⟨q,hq⟩ with ⟨u,hu⟩ | ⟨v,hv⟩
    · obtain ⟨p,hp⟩ := u.property
      have he : (mixedVFBaseMap φ F.domain hF).toImage p = u := Subtype.ext hp
      refine ⟨vfVolumeCoprodLeftMap F.fullVFObject G.fullVFObject p,?_⟩
      exact (zero_base_coprod_left_value F G φ hφ hF hG p).trans
        ((congrArg (fun z => (vfVolumeCoprodLeftMap A.fullVFObject B.fullVFObject z).val) he).trans
          (congrArg Subtype.val hu))
    · obtain ⟨p,hp⟩ := v.property
      have he : (mixedVFBaseMap φ G.domain hG).toImage p = v := Subtype.ext hp
      refine ⟨vfVolumeCoprodRightMap F.fullVFObject G.fullVFObject p,?_⟩
      exact (zero_base_coprod_right_value F G φ hφ hF hG p).trans
        ((congrArg (fun z => (vfVolumeCoprodRightMap A.fullVFObject B.fullVFObject z).val) he).trans
          (congrArg Subtype.val hv))

theorem zero_jacobian_coprod_density
    (q : ((F.coprod G).jacobianPushforward φ hφ (zero_family_coprod_supported F G hF hG)).domain) :
    ((F.coprod G).jacobianPushforward φ hφ (zero_family_coprod_supported F G hF hG)).form.value q =
      ((F.jacobianPushforward φ hφ hF).coprod (G.jacobianPushforward φ hφ hG)).form.value
        ⟨q.val,(zero_jacobian_coprod_domain F G φ hφ hF hG).le q.property⟩ := by
  let A := F.jacobianPushforward φ hφ hF
  let B := G.jacobianPushforward φ hφ hG
  obtain ⟨p,rfl⟩ := (mixed_vf_base_map_to_image_bijective φ hφ.1 (F.coprod G).domain
    (zero_family_coprod_supported F G hF hG)).2 q
  rcases vf_volume_coprod_cases F.fullVFObject G.fullVFObject p with ⟨u,rfl⟩ | ⟨v,rfl⟩
  · have he : (⟨_,(zero_jacobian_coprod_domain F G φ hφ hF hG).le
        ((mixedVFBaseMap φ (F.coprod G).domain (zero_family_coprod_supported F G hF hG)).toImage
          (vfVolumeCoprodLeftMap F.fullVFObject G.fullVFObject u)).property⟩ : (A.coprod B).domain) =
        vfVolumeCoprodLeftMap A.fullVFObject B.fullVFObject ((mixedVFBaseMap φ F.domain hF).toImage u) :=
      Subtype.ext (zero_base_coprod_left_value F G φ hφ hF hG u)
    rw [he]
    change ((F.coprod G).jacobianPushforward φ hφ (zero_family_coprod_supported F G hF hG)).form.value _ =
      (A.fullVFObject.coprod B.fullVFObject).form.value
        (vfVolumeCoprodLeftMap A.fullVFObject B.fullVFObject ((mixedVFBaseMap φ F.domain hF).toImage u))
    rw [vf_volume_coprod_density_left,(F.coprod G).jacobianPushforward_density]
    change (pureVFInverseJacobianDensityForm φ hφ).value (φ ⟨u.val.1,hF u⟩) *
      (F.fullVFObject.coprod G.fullVFObject).form.value (vfVolumeCoprodLeftMap F.fullVFObject G.fullVFObject u) =
      (F.jacobianPushforward φ hφ hF).form.value ((mixedVFBaseMap φ F.domain hF).toImage u)
    rw [vf_volume_coprod_density_left,F.jacobianPushforward_density]
    rfl
  · have he : (⟨_,(zero_jacobian_coprod_domain F G φ hφ hF hG).le
        ((mixedVFBaseMap φ (F.coprod G).domain (zero_family_coprod_supported F G hF hG)).toImage
          (vfVolumeCoprodRightMap F.fullVFObject G.fullVFObject v)).property⟩ : (A.coprod B).domain) =
        vfVolumeCoprodRightMap A.fullVFObject B.fullVFObject ((mixedVFBaseMap φ G.domain hG).toImage v) :=
      Subtype.ext (zero_base_coprod_right_value F G φ hφ hF hG v)
    rw [he]
    change ((F.coprod G).jacobianPushforward φ hφ (zero_family_coprod_supported F G hF hG)).form.value _ =
      (A.fullVFObject.coprod B.fullVFObject).form.value
        (vfVolumeCoprodRightMap A.fullVFObject B.fullVFObject ((mixedVFBaseMap φ G.domain hG).toImage v))
    rw [vf_volume_coprod_density_right,(F.coprod G).jacobianPushforward_density]
    change (pureVFInverseJacobianDensityForm φ hφ).value (φ ⟨v.val.1,hG v⟩) *
      (F.fullVFObject.coprod G.fullVFObject).form.value (vfVolumeCoprodRightMap F.fullVFObject G.fullVFObject v) =
      (G.jacobianPushforward φ hφ hG).form.value ((mixedVFBaseMap φ G.domain hG).toImage v)
    rw [vf_volume_coprod_density_right,G.jacobianPushforward_density]
    rfl

end IntegrationInACVF.Section7.HK
