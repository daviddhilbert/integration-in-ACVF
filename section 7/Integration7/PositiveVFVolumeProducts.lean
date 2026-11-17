module

public import Integration7.VFVolumeObjects
public import Integration7.VolumeFormProducts
public import Section4.VFProducts

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! The actual Cartesian product of positive VF volume objects, with
concatenated VF/RV tuples and the product of the original densities. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n m : ℕ}

def PositiveVFVolumeObject.prod
    (U : PositiveVFVolumeObject (M := M) S n) (V : PositiveVFVolumeObject (M := M) S m) :
    PositiveVFVolumeObject (M := M) S ((n+1)+m) where
  arity := U.arity+V.arity
  domain := mixedProductDomain (n := n+1) (m := m+1) U.domain V.domain
  finite_labels := finiteRVFibres_product (U := U.underlying.obj.obj) (V := V.underlying.obj.obj)
    U.finite_labels V.finite_labels
  form := (U.form.prod V.form).pullback (mixedUnpack (n := n+1) (m := m+1) U.domain V.domain)

theorem positive_vf_volume_product_density
    (U : PositiveVFVolumeObject (M := M) S n) (V : PositiveVFVolumeObject (M := M) S m)
    (u : U.domain) (v : V.domain) :
    (U.prod V).form.value ((mixedPack U.domain V.domain).toImage ⟨(u.val,v.val),u.property,v.property⟩) =
      U.form.value u * V.form.value v := by
  change (U.form.prod V.form).value (mixedUnpack U.domain V.domain
    ((mixedPack U.domain V.domain).toImage ⟨(u.val,v.val),u.property,v.property⟩)) = _
  rw [mixedUnpack_pack]
  rfl

end IntegrationInACVF.Section7
