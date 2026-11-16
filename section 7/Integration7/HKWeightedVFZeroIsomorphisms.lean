import Integration7.HKWeightedVFZeroProducts

/-! Actual cofull VF volume isomorphisms remain so after Cartesian
product with any exact-weight-preserving measured zero coefficient. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.DefinableGeometry

namespace IntegrationInACVF.Section7.HK
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n : ℕ}

def weightedVFZeroRestrictionBijection
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (U : PositiveVFVolumeObject (M := M) (C.base : Set M) n)
    (Z : ZeroRVVolumeObject (M := M) (C.base : Set M))
    (L : DefSet (rawMixedSpace (M := M) (n+1) U.arity) (C.base : Set M))
    (hL : L.carrier ⊆ U.domain.carrier) :
    VFVolumeBijection (positiveVFZeroProduct (U.restrict L hL) Z)
      ((positiveVFZeroProduct U Z).restrict (positiveVFZeroProduct (U.restrict L hL) Z).domain
        (mixed_product_domain_subset hL (Set.Subset.refl _))) := by
  refine VFVolumeBijection.of_preserving_vf_and_density hc C
    (U := positiveVFZeroProduct (U.restrict L hL) Z)
    (V := (positiveVFZeroProduct U Z).restrict (positiveVFZeroProduct (U.restrict L hL) Z).domain
      (mixed_product_domain_subset hL (Set.Subset.refl _)))
    (Map.id _) Function.bijective_id (fun _ => rfl) ?_
  intro p
  obtain ⟨uv,rfl⟩ := (mixedPackToImage_bijective L (rvLift Z.underlying.obj)).2 p
  let u := Map.prodFst L (rvLift Z.underlying.obj) uv
  let z := Map.prodSnd L (rvLift Z.underlying.obj) uv
  calc
    _ = (U.restrict L hL).form.value u * (zeroLift Z).form.value z :=
      positiveVFZeroProduct_density_pair (U.restrict L hL) Z u z
    _ = _ := (positiveVFZeroProduct_density_pair U Z ⟨u.val,hL u.property⟩ z).symm

def weightedVFZeroProductIso
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    {U V : PositiveVFVolumeObject (M := M) (C.base : Set M) n}
    {Z T : ZeroRVVolumeObject (M := M) (C.base : Set M)}
    (f : VFVolumeIso U V) (e : ZeroRVVolumeIso Z T) :
    VFVolumeIso (positiveVFZeroProduct U Z) (positiveVFZeroProduct V T) := by
  let g := ordinaryFiniteAmbientIso (zeroLiftIso e).iso
  let P := positiveVFZeroProduct (U.restrict f.source f.source_subset) Z
  let Q := positiveVFZeroProduct (V.restrict f.target f.target_subset) T
  have hP := mixed_product_domain_subset f.source_subset (Set.Subset.refl (rvLift Z.underlying.obj).carrier)
  have hQ := mixed_product_domain_subset f.target_subset (Set.Subset.refl (rvLift T.underlying.obj).carrier)
  have hPS := vf_product_cofull_left (rvLift Z.underlying.obj)
    (⟨f.source_subset,f.source_complement_small⟩ : VFCofull U.domain f.source)
  have hQS := vf_product_cofull_left (rvLift T.underlying.obj)
    (⟨f.target_subset,f.target_complement_small⟩ : VFCofull V.domain f.target)
  refine ⟨P.domain,Q.domain,hP,hQ,hPS.small,hQS.small,?_⟩
  exact ((weightedVFZeroRestrictionBijection hc C U Z f.source f.source_subset).symm hc C).trans hc C
    ((weightedVFZeroProductBijection f.bijection g.hom (DefinableSetCat.bijective_of_iso g)
      (zeroLiftIso e).density).trans hc C
        (weightedVFZeroRestrictionBijection hc C V T f.target f.target_subset))

end IntegrationInACVF.Section7.HK
