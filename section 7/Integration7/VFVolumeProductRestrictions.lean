import Integration7.PositiveVFVolumeProducts
import Integration7.VFVolumeBijections

/-! Restricting the two actual Cartesian factors retains the original
product density, pointwise on the concatenated product domain. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.DefinableGeometry

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n m a b : ℕ}

theorem mixed_product_domain_subset
    {A L : DefSet (rawMixedSpace (M := M) n a) S}
    {B K : DefSet (rawMixedSpace (M := M) m b) S}
    (hL : L.carrier ⊆ A.carrier) (hK : K.carrier ⊆ B.carrier) :
    (mixedProductDomain L K).carrier ⊆ (mixedProductDomain A B).carrier := by
  intro p hp
  have h := (mem_mixedProductDomain L K p).mp hp
  exact (mem_mixedProductDomain A B p).mpr ⟨hL h.1,hK h.2⟩

theorem vf_volume_product_restrict_density
    (U : PositiveVFVolumeObject (M := M) S n) (V : PositiveVFVolumeObject (M := M) S m)
    (L : DefSet (rawMixedSpace (M := M) (n+1) U.arity) S)
    (K : DefSet (rawMixedSpace (M := M) (m+1) V.arity) S)
    (hL : L.carrier ⊆ U.domain.carrier) (hK : K.carrier ⊆ V.domain.carrier)
    (p : ((U.restrict L hL).prod (V.restrict K hK)).domain) :
    (U.prod V).form.value ⟨p.val,mixed_product_domain_subset hL hK p.property⟩ =
      ((U.restrict L hL).prod (V.restrict K hK)).form.value p := by
  obtain ⟨uv,rfl⟩ := (mixedPackToImage_bijective L K).2 p
  let u := Map.prodFst L K uv
  let v := Map.prodSnd L K uv
  calc
    _ = U.form.value ⟨u.val,hL u.property⟩ * V.form.value ⟨v.val,hK v.property⟩ :=
      positive_vf_volume_product_density U V ⟨u.val,hL u.property⟩ ⟨v.val,hK v.property⟩
    _ = _ := (positive_vf_volume_product_density (U.restrict L hL) (V.restrict K hK) u v).symm

def vfVolumeProductRestrictionBijection
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (U : PositiveVFVolumeObject (M := M) (C.base : Set M) n)
    (V : PositiveVFVolumeObject (M := M) (C.base : Set M) m)
    (L : DefSet (rawMixedSpace (M := M) (n+1) U.arity) (C.base : Set M))
    (K : DefSet (rawMixedSpace (M := M) (m+1) V.arity) (C.base : Set M))
    (hL : L.carrier ⊆ U.domain.carrier) (hK : K.carrier ⊆ V.domain.carrier) :
    VFVolumeBijection ((U.restrict L hL).prod (V.restrict K hK))
      ((U.prod V).restrict ((U.restrict L hL).prod (V.restrict K hK)).domain
        (mixed_product_domain_subset hL hK)) :=
  VFVolumeBijection.of_preserving_vf_and_density hc C (Map.id _) Function.bijective_id
    (fun _ => rfl) (fun p => (vf_volume_product_restrict_density U V L K hL hK p).symm)

end IntegrationInACVF.Section7
