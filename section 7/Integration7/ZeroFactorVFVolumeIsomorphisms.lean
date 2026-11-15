import Integration7.ZeroFactorVFVolumeProducts
import Integration7.VFCofullSubdomains
import Integration7.OrdinaryFiniteCoproductIsomorphisms
import Integration7.OrdinaryZeroLiftIsomorphisms
import Integration7.VFVolumeIsomorphisms

/-! Products with an ordinary RV[0] coefficient preserve actual
almost-everywhere VF volume isomorphisms and ordinary coefficient isomorphisms. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.DefinableGeometry

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n m a b : ℕ}

theorem vf_product_cofull_left
    {A L : DefSet (rawMixedSpace (M := M) n a) S}
    (B : DefSet (rawMixedSpace (M := M) m b) S) (hL : VFCofull A L) :
    VFCofull (mixedProductDomain A B) (mixedProductDomain L B) := by
  have hP : VFAlmostEverywhere A (fun u => u.val ∈ L.carrier) := by
    refine ⟨A.sdiff L,Set.diff_subset,hL.small,?_⟩
    intro u hu
    by_contra h
    exact hu ⟨u.property,h⟩
  obtain ⟨E,hE,hdE,hP⟩ := vf_almost_everywhere_product_left A B hP
  refine ⟨mixed_product_domain_subset hL.subset (Set.Subset.refl _),
    (vfDim_mono_same_arity ?_).trans_lt hdE⟩
  intro p hp
  by_contra he
  have h := hP ⟨p,hp.1⟩ he
  let uv := mixedUnpack A B ⟨p,hp.1⟩
  let u := Map.prodFst A B uv
  let v := Map.prodSnd A B uv
  apply hp.2
  let z := (mixedPack L B).toImage ⟨(u.val,v.val),h,v.property⟩
  have hz : z.val = p := congrArg Subtype.val (mixedPack_unpack A B ⟨p,hp.1⟩)
  exact hz ▸ z.property

def vfVolumeZeroProductRestrictionBijection
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (U : PositiveVFVolumeObject (M := M) (C.base : Set M) n)
    (Z : RVFiniteObject (M := M) (C.base : Set M) 0)
    (L : DefSet (rawMixedSpace (M := M) (n+1) U.arity) (C.base : Set M))
    (hL : L.carrier ⊆ U.domain.carrier) :
    VFVolumeBijection ((U.restrict L hL).prod_zero Z)
      ((U.prod_zero Z).restrict ((U.restrict L hL).prod_zero Z).domain
        (mixed_product_domain_subset hL (Set.Subset.refl _))) := by
  refine VFVolumeBijection.of_preserving_vf_and_density hc C
    (U := (U.restrict L hL).prod_zero Z)
    (V := (U.prod_zero Z).restrict ((U.restrict L hL).prod_zero Z).domain
      (mixed_product_domain_subset hL (Set.Subset.refl _)))
    (Map.id _) Function.bijective_id (fun _ => rfl) ?_
  intro p
  obtain ⟨uv,rfl⟩ := (mixedPackToImage_bijective L (rvLift Z.obj)).2 p
  let u := Map.prodFst L (rvLift Z.obj) uv
  let z := Map.prodSnd L (rvLift Z.obj) uv
  calc
    _ = (U.restrict L hL).form.value u := positive_vf_zero_product_density_pair (U.restrict L hL) Z u z
    _ = _ := (positive_vf_zero_product_density_pair U Z ⟨u.val,hL u.property⟩ z).symm

def VFVolumeIso.prod_zero
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    {U V : PositiveVFVolumeObject (M := M) (C.base : Set M) n}
    {Z T : RVFiniteObject (M := M) (C.base : Set M) 0}
    (f : VFVolumeIso U V) (e : Z ≅ T) : VFVolumeIso (U.prod_zero Z) (V.prod_zero T) := by
  let g := ordinaryFiniteAmbientIso (ordinaryZeroLiftIsoOfRVIso e)
  let P := (U.restrict f.source f.source_subset).prod_zero Z
  let Q := (V.restrict f.target f.target_subset).prod_zero T
  have hP := mixed_product_domain_subset f.source_subset (Set.Subset.refl (rvLift Z.obj).carrier)
  have hQ := mixed_product_domain_subset f.target_subset (Set.Subset.refl (rvLift T.obj).carrier)
  have hPS := vf_product_cofull_left (rvLift Z.obj)
    (⟨f.source_subset,f.source_complement_small⟩ : VFCofull U.domain f.source)
  have hQS := vf_product_cofull_left (rvLift T.obj)
    (⟨f.target_subset,f.target_complement_small⟩ : VFCofull V.domain f.target)
  refine ⟨P.domain,Q.domain,hP,hQ,hPS.small,hQS.small,?_⟩
  exact ((vfVolumeZeroProductRestrictionBijection hc C U Z f.source f.source_subset).symm hc C).trans hc C
    ((f.bijection.prod_zero g.hom (DefinableSetCat.bijective_of_iso g)).trans hc C
      (vfVolumeZeroProductRestrictionBijection hc C V T f.target f.target_subset))

end IntegrationInACVF.Section7
