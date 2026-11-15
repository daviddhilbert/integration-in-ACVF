import Integration7.PositiveVFVolumeProducts
import Integration7.VFVolumeLifts
import Integration7.MixedDomainProductJacobians
import Integration7.VFAlmostEverywhereProductLeft

/-! The actual Cartesian product with an ordinary degree-zero lift.
No density is assigned to the zero factor; the positive density is retained. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n : ℕ}

def PositiveVFVolumeObject.prod_zero (U : PositiveVFVolumeObject (M := M) S n)
    (Z : RVFiniteObject (M := M) S 0) : PositiveVFVolumeObject (M := M) S n where
  arity := U.arity+Z.obj.arity
  domain := mixedProductDomain (n := n+1) (m := 0) U.domain (rvLift Z.obj)
  finite_labels := finiteRVFibres_product (U := U.underlying.obj.obj)
    (V := (rvLiftFiniteObject (rawRVSpace (M := M) 1) Z).obj.obj) U.finite_labels
    (rvLift_finite_rv_fibres Z.obj Z.property)
  form := U.form.pullback ((Map.prodFst U.domain (rvLift Z.obj)).comp
    (mixedUnpack (n := n+1) (m := 0) U.domain (rvLift Z.obj)))

theorem positive_vf_zero_product_density_pair
    (U : PositiveVFVolumeObject (M := M) S n) (Z : RVFiniteObject (M := M) S 0)
    (u : U.domain) (z : rvLift Z.obj) :
    (U.prod_zero Z).form.value
      ((mixedPack U.domain (rvLift Z.obj)).toImage ⟨(u.val,z.val),u.property,z.property⟩) = U.form.value u := by
  change U.form.value (Map.prodFst U.domain (rvLift Z.obj)
    (mixedUnpack U.domain (rvLift Z.obj) ((mixedPack U.domain (rvLift Z.obj)).toImage
      ⟨(u.val,z.val),u.property,z.property⟩))) = _
  rw [mixedUnpack_pack]
  rfl

theorem preserves_vf_volume_zero_product
    {U V : PositiveVFVolumeObject (M := M) S n} {Z T : RVFiniteObject (M := M) S 0}
    (f : Map U.domain V.domain) (g : Map (rvLift Z.obj) (rvLift T.obj))
    (hf : PreservesVFVolume U.form V.form f) :
    PreservesVFVolume (U.prod_zero Z).form (V.prod_zero T).form (mixedDomainProductMap f g) := by
  apply (vf_almost_everywhere_product_left U.domain (rvLift Z.obj) hf).mono
  intro w h
  let uv := mixedUnpack U.domain (rvLift Z.obj) w
  let u := Map.prodFst U.domain (rvLift Z.obj) uv
  let z := Map.prodSnd U.domain (rvLift Z.obj) uv
  obtain ⟨J,hJ,hD⟩ := h
  have hw : (mixedPack U.domain (rvLift Z.obj)).toImage ⟨(u.val,z.val),u.property,z.property⟩ = w :=
    mixedPack_unpack U.domain (rvLift Z.obj) w
  have hJac := has_mixed_vf_jacobian_domain_product f g u z J 1 hJ
    (hasMixedVFJacobianAt_zero_arity g z)
  rw [mul_one,hw] at hJac
  refine ⟨J,hJac,?_⟩
  change U.form.value u = V.form.value
    (Map.prodFst V.domain (rvLift T.obj) (mixedUnpack V.domain (rvLift T.obj)
      (mixedDomainProductMap f g w))) * CanonicalRV.encodedRv J
  rw [← hw,mixed_domain_product_map_pair,mixedUnpack_pack]
  exact hD

def VFVolumeBijection.prod_zero
    {U V : PositiveVFVolumeObject (M := M) S n} {Z T : RVFiniteObject (M := M) S 0}
    (f : VFVolumeBijection U V) (g : Map (rvLift Z.obj) (rvLift T.obj)) (hg : Function.Bijective g) :
    VFVolumeBijection (U.prod_zero Z) (V.prod_zero T) where
  map := mixedDomainProductMap f.map g
  bijective := mixed_domain_product_map_bijective f.map g f.bijective hg
  preserves := preserves_vf_volume_zero_product f.map g f.preserves

end IntegrationInACVF.Section7
