module

public import Integration7.HKZeroVolumeLifts
public import Integration7.ZeroFactorVFVolumeIsomorphisms

@[expose] public section

/-! Cartesian product with a measured zero lift retains both densities.
Its product maps use determinant one on the empty VF block and exact
weight preservation on that factor. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry

namespace IntegrationInACVF.Section7.HK
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n : ℕ}

def positiveVFZeroProduct (U : PositiveVFVolumeObject (M := M) S n)
    (Z : ZeroRVVolumeObject (M := M) S) : PositiveVFVolumeObject (M := M) S n :=
  { U.prod_zero Z.underlying with
    form := (U.form.prod (zeroLift Z).form).pullback
      (mixedUnpack U.domain (rvLift Z.underlying.obj)) }

theorem positiveVFZeroProduct_density_pair
    (U : PositiveVFVolumeObject (M := M) S n) (Z : ZeroRVVolumeObject (M := M) S)
    (u : U.domain) (z : rvLift Z.underlying.obj) :
    (positiveVFZeroProduct U Z).form.value
      ((mixedPack U.domain (rvLift Z.underlying.obj)).toImage ⟨(u.val,z.val),u.property,z.property⟩) =
      U.form.value u * (zeroLift Z).form.value z := by
  change (U.form.prod (zeroLift Z).form).value (mixedUnpack U.domain (rvLift Z.underlying.obj)
    ((mixedPack U.domain (rvLift Z.underlying.obj)).toImage ⟨(u.val,z.val),u.property,z.property⟩)) = _
  rw [mixedUnpack_pack]
  rfl

theorem preserves_weighted_vf_zero_product
    {U V : PositiveVFVolumeObject (M := M) S n} {Z T : ZeroRVVolumeObject (M := M) S}
    (f : Map U.domain V.domain) (g : Map (rvLift Z.underlying.obj) (rvLift T.underlying.obj))
    (hf : PreservesVFVolume U.form V.form f)
    (hρ : ∀ z, (zeroLift Z).form.value z = (zeroLift T).form.value (g z)) :
    PreservesVFVolume (positiveVFZeroProduct U Z).form (positiveVFZeroProduct V T).form
      (mixedDomainProductMap f g) := by
  apply (vf_almost_everywhere_product_left U.domain (rvLift Z.underlying.obj) hf).mono
  intro w h
  let uv := mixedUnpack U.domain (rvLift Z.underlying.obj) w
  let u := Map.prodFst U.domain (rvLift Z.underlying.obj) uv
  let z := Map.prodSnd U.domain (rvLift Z.underlying.obj) uv
  obtain ⟨J,hJ,hD⟩ := h
  have hw : (mixedPack U.domain (rvLift Z.underlying.obj)).toImage
      ⟨(u.val,z.val),u.property,z.property⟩ = w := mixedPack_unpack _ _ w
  have hJac := has_mixed_vf_jacobian_domain_product f g u z J 1 hJ
    (hasMixedVFJacobianAt_zero_arity g z)
  rw [mul_one,hw] at hJac
  refine ⟨J,hJac,?_⟩
  rw [← hw,mixed_domain_product_map_pair,positiveVFZeroProduct_density_pair,
    positiveVFZeroProduct_density_pair,hD,hρ z]
  ac_rfl

def weightedVFZeroProductBijection
    {U V : PositiveVFVolumeObject (M := M) S n} {Z T : ZeroRVVolumeObject (M := M) S}
    (f : VFVolumeBijection U V) (g : Map (rvLift Z.underlying.obj) (rvLift T.underlying.obj))
    (hg : Function.Bijective g)
    (hρ : ∀ z, (zeroLift Z).form.value z = (zeroLift T).form.value (g z)) :
    VFVolumeBijection (positiveVFZeroProduct U Z) (positiveVFZeroProduct V T) :=
  ⟨mixedDomainProductMap f.map g,mixed_domain_product_map_bijective f.map g f.bijective hg,
    preserves_weighted_vf_zero_product f.map g f.preserves hρ⟩

end IntegrationInACVF.Section7.HK
