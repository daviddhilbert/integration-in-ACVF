import Integration7.GammaNamedRVProductDistributivity
import Integration7.VolumeProductDistributivity
import Integration7.RVVolumeProducts
import Integration7.GammaEssentialVolumeGraphs

/-! Gamma graphs of products of positive RV volume isomorphisms and of the
positive distributivity isomorphism. The product isomorphism acts on the
essential product domain factorwise, so its graph is the product of the two
Gamma graphs. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry SpecialTransformations.Section9
open SpecialTransformations.Section5 (Point GammaSetDefinable GammaGraphDefinable gammaLogicInput)
open IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {B : Base (M := M)} {n m : ℕ}

theorem productEssentialInverseChart_val {S : Set M}
    (U : PositiveRVVolumeObject (M := M) S n) (V : PositiveRVVolumeObject (M := M) S m)
    (p : U.essential.obj.domain.prod V.essential.obj.domain) :
    (productEssentialInverseChart U V p).val = Fin.append p.val.1 p.val.2 := rfl

theorem productEssentialChart_fst_val {S : Set M}
    (U : PositiveRVVolumeObject (M := M) S n) (V : PositiveRVVolumeObject (M := M) S m)
    (w : (U.prod V).essential.obj.domain) :
    (Map.prodFst _ _ (productEssentialChart U V w)).val =
      fun j => w.val (Fin.castAdd V.underlying.obj.arity j) :=
  rvUnpack_fst_val U.underlying.obj.domain V.underlying.obj.domain
    ⟨w.val,rvEssentialLabels_subset (U.prod V).underlying.obj w.property⟩

theorem productEssentialChart_snd_val {S : Set M}
    (U : PositiveRVVolumeObject (M := M) S n) (V : PositiveRVVolumeObject (M := M) S m)
    (w : (U.prod V).essential.obj.domain) :
    (Map.prodSnd _ _ (productEssentialChart U V w)).val =
      fun j => w.val (Fin.natAdd U.underlying.obj.arity j) :=
  rvUnpack_snd_val U.underlying.obj.domain V.underlying.obj.domain
    ⟨w.val,rvEssentialLabels_subset (U.prod V).underlying.obj w.property⟩

theorem RVVolumeIso.GammaDefinable.prod
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    {U U' : PositiveRVVolumeObject (M := M) (C.base : Set M) n}
    {V V' : PositiveRVVolumeObject (M := M) (C.base : Set M) m}
    {f : RVVolumeIso U U'} {g : RVVolumeIso V V'} (hf : f.GammaDefinable B) (hg : g.GammaDefinable B) :
    (f.prod hc C g).GammaDefinable B := by
  apply GammaGraphDefinable.congr (gamma_rv_relation_product hf hg)
  intro p q
  constructor
  · rintro ⟨⟨u,hu,hfu⟩,⟨v,hv,hgv⟩⟩
    let w := productEssentialInverseChart U V ⟨(u.val,v.val),u.property,v.property⟩
    have hw : w.val = p.2 := by
      rw [productEssentialInverseChart_val]
      change Fin.append u.val v.val = p.2
      rw [hu,hv]
      exact Fin.append_castAdd_natAdd
    refine ⟨w,hw,?_⟩
    change (f.productMap g w).val = q.2
    have hc' : productEssentialChart U V w = ⟨(u.val,v.val),u.property,v.property⟩ :=
      productEssentialChart_inverse U V _
    change (productEssentialInverseChart U' V'
      (Map.prodMap (finiteIsoMap f.iso) (finiteIsoMap g.iso) (productEssentialChart U V w))).val = q.2
    rw [hc',productEssentialInverseChart_val]
    change Fin.append (finiteIsoMap f.iso u).val (finiteIsoMap g.iso v).val = q.2
    rw [hfu,hgv]
    exact Fin.append_castAdd_natAdd
  · rintro ⟨w,hw,hq⟩
    change (f.productMap g w).val = q.2 at hq
    change (productEssentialInverseChart U' V'
      (Map.prodMap (finiteIsoMap f.iso) (finiteIsoMap g.iso) (productEssentialChart U V w))).val = q.2 at hq
    rw [productEssentialInverseChart_val] at hq
    refine ⟨⟨Map.prodFst _ _ (productEssentialChart U V w),?_,?_⟩,
      ⟨Map.prodSnd _ _ (productEssentialChart U V w),?_,?_⟩⟩
    · rw [productEssentialChart_fst_val,hw]
    · funext j
      rw [← hq]
      exact (Fin.append_left _ _ j).symm
    · rw [productEssentialChart_snd_val,hw]
    · funext j
      rw [← hq]
      exact (Fin.append_right _ _ j).symm

theorem gamma_volume_product_coprod_fold_iso
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    {U : PositiveRVVolumeObject (M := M) (C.base : Set M) n}
    {V W : PositiveRVVolumeObject (M := M) (C.base : Set M) m}
    (hU : VolumeObjectGamma U B) (hV : VolumeObjectGamma V B) (hW : VolumeObjectGamma W B) :
    (volumeProductCoprodFoldIso hc C U V W).GammaDefinable B := by
  have hUV := (HK.RVVolumeObject.Gamma.positive_iff _).mp
    (HK.RVVolumeObject.Gamma.product (n := n+1) (m := m+1) hc
      ((HK.RVVolumeObject.Gamma.positive_iff U).mpr hU) ((HK.RVVolumeObject.Gamma.positive_iff V).mpr hV))
  have hUW := (HK.RVVolumeObject.Gamma.positive_iff _).mp
    (HK.RVVolumeObject.Gamma.product (n := n+1) (m := m+1) hc
      ((HK.RVVolumeObject.Gamma.positive_iff U).mpr hU) ((HK.RVVolumeObject.Gamma.positive_iff W).mpr hW))
  exact gamma_volume_iso_of_preserving_coordinates_full hc C _
    (volumeProductCoprodFold_coordinates U V W) (volumeProductCoprodFold_density U V W)
    (gamma_essential_volume_domain _ (hUV.coprod hUW).coordinates)
    ((gamma_rv_product_coprod_fold hc U.underlying.obj V.underlying.obj W.underlying.obj
      hU.domain_graph hV.domain_graph hW.domain_graph).congr (fun _ => rfl))

theorem gamma_volume_product_right_distrib_iso
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    {U : PositiveRVVolumeObject (M := M) (C.base : Set M) n}
    {V W : PositiveRVVolumeObject (M := M) (C.base : Set M) m}
    (hU : VolumeObjectGamma U B) (hV : VolumeObjectGamma V B) (hW : VolumeObjectGamma W B) :
    (volumeProductRightDistribIso hc C U V W).GammaDefinable B :=
  (gamma_volume_product_coprod_fold_iso hc C hU hV hW).symm hc C B

end IntegrationInACVF.Section7
