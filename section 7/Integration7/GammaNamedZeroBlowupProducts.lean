import Integration7.GammaNamedBlowupProducts
import Integration7.HKWeightedZeroBlowupCongruence
import Integration7.HKRVProductBridges
import Integration7.ElementaryZeroVolumeProducts

/-! Weighted degree-zero factors and positive Gamma volume blowups. Multiplying
a Gamma blowup by a Gamma degree-zero object (with its density) on either
side gives a Gamma blowup, so mixed products preserve Gamma blowup
equivalence. The mixed product isomorphisms act factorwise or by the
coordinate swap, hence have Gamma graphs. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry SpecialTransformations.Section9
open SpecialTransformations.Section5 (Point GammaSetDefinable GammaGraphDefinable gammaLogicInput)
open IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7
open IntegrationInACVF.Section7.HK
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {B : Base (M := M)} {S : Set M} {k : ℕ}

set_option allowUnsafeReducibility true in
attribute [local reducible] zeroProduct positiveZeroProduct multiplyForm
  PositiveRVVolumeObject.zero_prod PositiveRVVolumeObject.prod_zero rvFiniteProductObject

theorem gamma_scalar_value_congr {a : ℕ} {A : DefSet (rawRVSpace (M := M) a) S}
    {f g : Map A (DefSet.univ (rawRVSpace (M := M) 1) S)} (hf : RVMapGamma f B)
    (h : ∀ u, (f u).val 0 = (g u).val 0) : RVMapGamma g B := by
  apply hf.congr
  intro u
  funext j
  have hj : j = 0 := Subsingleton.elim _ _
  subst hj
  exact h u

theorem VolumeObjectGamma.zeroProd (hc : CanonicalStructure.IsCanonical (M := M))
    {Z : ZeroRVVolumeObject (M := M) S} {U : PositiveRVVolumeObject (M := M) S k}
    (hZ : Z.Gamma B) (hU : VolumeObjectGamma U B) : VolumeObjectGamma (zeroProduct Z U) B := by
  have hW := gamma_rv_product_domain_of hZ.domain hU.domain_graph
  have hfst := gamma_rv_unpack_fst hc Z.underlying.obj.domain U.underlying.obj.domain hW
  have hsnd := gamma_rv_unpack_snd hc Z.underlying.obj.domain U.underlying.obj.domain hW
  refine ⟨(hsnd.comp hU.coordinates).congr (fun x => (zeroProduct_coordinates Z U x).symm),?_⟩
  exact gamma_scalar_value_congr (RVMapGamma.scalarMul hc (hfst.comp hZ.density) (hsnd.comp hU.density))
    (fun x => (zeroProduct_density Z U x).symm)

theorem VolumeObjectGamma.posZeroProd (hc : CanonicalStructure.IsCanonical (M := M))
    {U : PositiveRVVolumeObject (M := M) S k} {Z : ZeroRVVolumeObject (M := M) S}
    (hU : VolumeObjectGamma U B) (hZ : Z.Gamma B) : VolumeObjectGamma (positiveZeroProduct U Z) B := by
  have hW := gamma_rv_product_domain_of hU.domain_graph hZ.domain
  have hfst := gamma_rv_unpack_fst hc U.underlying.obj.domain Z.underlying.obj.domain hW
  have hsnd := gamma_rv_unpack_snd hc U.underlying.obj.domain Z.underlying.obj.domain hW
  refine ⟨(hfst.comp hU.coordinates).congr (fun x => (HK.positiveZeroProduct_coordinates U Z x).symm),?_⟩
  exact gamma_scalar_value_congr (RVMapGamma.scalarMul hc (hfst.comp hU.density) (hsnd.comp hZ.density))
    (fun x => (HK.positiveZeroProduct_density U Z x).symm)

theorem gamma_mixed_product_swap_iso (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    {U : PositiveRVVolumeObject (M := M) (C.base : Set M) k} {Z : ZeroRVVolumeObject (M := M) (C.base : Set M)}
    (hU : VolumeObjectGamma U B) (hZ : Z.Gamma B) : (mixedProductSwapIso hc C U Z).GammaDefinable B := by
  have hUZ := hU.posZeroProd hc hZ
  exact gamma_volume_iso_of_preserving_coordinates_full hc C _
    (volumeZeroProductSwap_coordinates U Z.underlying)
    (by
      intro x
      change (zeroProduct Z U).form.value (rvProductSwapMap U.underlying.obj Z.underlying.obj x) =
        (HK.positiveZeroProduct U Z).form.value x
      obtain ⟨u,z,rfl⟩ := exists_rvPackPair U.underlying.obj.domain Z.underlying.obj.domain x
      rw [rvProductSwapMap_pair, zeroProduct_density, HK.positiveZeroProduct_density, rvUnpack_pair, rvUnpack_pair]
      exact mul_comm _ _)
    (gamma_essential_volume_domain _ hUZ.coordinates)
    ((gamma_rv_coordinate_map hc _ _ hUZ.domain_graph
      (rv_product_swap_raw U.underlying.obj Z.underlying.obj)).congr (fun _ => rfl))

theorem gamma_positive_zero_product_iso (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    {U V : PositiveRVVolumeObject (M := M) (C.base : Set M) k}
    {Z T : ZeroRVVolumeObject (M := M) (C.base : Set M)}
    {f : RVVolumeIso U V} {g : ZeroRVVolumeIso Z T} (hf : f.GammaDefinable B) (hg : g.GammaDefinable B) :
    (positiveZeroProductIso hc C f g).GammaDefinable B := by
  apply GammaGraphDefinable.congr (gamma_rv_relation_product hf hg)
  intro p q
  constructor
  · rintro ⟨⟨u,hu,hfu⟩,⟨z,hz,hgz⟩⟩
    let w := zeroProductEssentialInverseChart U Z.underlying ⟨(u.val,z.val),u.property,z.property⟩
    have hw : w.val = p.2 := by
      change Fin.append u.val z.val = p.2
      rw [hu,hz]
      exact Fin.append_castAdd_natAdd
    refine ⟨w,hw,?_⟩
    have hc' : zeroProductEssentialChart U Z.underlying w = ⟨(u.val,z.val),u.property,z.property⟩ :=
      zeroProductEssentialChart_inverse U Z.underlying _
    change (zeroProductEssentialInverseChart V T.underlying
      (Map.prodMap (finiteIsoMap f.iso) (finiteIsoMap g.iso) (zeroProductEssentialChart U Z.underlying w))).val = q.2
    rw [hc']
    change Fin.append (finiteIsoMap f.iso u).val (finiteIsoMap g.iso z).val = q.2
    rw [hfu,hgz]
    exact Fin.append_castAdd_natAdd
  · rintro ⟨w,hw,hq⟩
    change (zeroProductEssentialInverseChart V T.underlying
      (Map.prodMap (finiteIsoMap f.iso) (finiteIsoMap g.iso) (zeroProductEssentialChart U Z.underlying w))).val = q.2 at hq
    change Fin.append _ _ = q.2 at hq
    have h1 : (Map.prodFst _ _ (zeroProductEssentialChart U Z.underlying w)).val =
        fun j => w.val (Fin.castAdd Z.underlying.obj.arity j) :=
      rvUnpack_fst_val U.underlying.obj.domain Z.underlying.obj.domain
        ⟨w.val,rvEssentialLabels_subset (U.prod_zero Z.underlying).underlying.obj w.property⟩
    have h2 : (Map.prodSnd _ _ (zeroProductEssentialChart U Z.underlying w)).val =
        fun j => w.val (Fin.natAdd U.underlying.obj.arity j) :=
      rvUnpack_snd_val U.underlying.obj.domain Z.underlying.obj.domain
        ⟨w.val,rvEssentialLabels_subset (U.prod_zero Z.underlying).underlying.obj w.property⟩
    refine ⟨⟨Map.prodFst _ _ (zeroProductEssentialChart U Z.underlying w),?_,?_⟩,
      ⟨Map.prodSnd _ _ (zeroProductEssentialChart U Z.underlying w),?_,?_⟩⟩
    · rw [h1,hw]
    · funext j
      rw [← hq]
      exact (Fin.append_left _ _ j).symm
    · rw [h2,hw]
    · funext j
      rw [← hq]
      exact (Fin.append_right _ _ j).symm

theorem gamma_zero_product_iso (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    {U V : PositiveRVVolumeObject (M := M) (C.base : Set M) k}
    {Z T : ZeroRVVolumeObject (M := M) (C.base : Set M)}
    (hU : VolumeObjectGamma U B) (hV : VolumeObjectGamma V B) (hZ : Z.Gamma B) (hT : T.Gamma B)
    {g : ZeroRVVolumeIso Z T} {f : RVVolumeIso U V} (hg : g.GammaDefinable B) (hf : f.GammaDefinable B) :
    (zeroProductIso hc C g f).GammaDefinable B :=
  (((gamma_mixed_product_swap_iso hc C hU hZ).symm hc C B).trans hc C B
    (gamma_positive_zero_product_iso hc C hf hg)).trans hc C B (gamma_mixed_product_swap_iso hc C hV hT)

theorem gamma_volume_zero_product_right_distrib_iso (hc : CanonicalStructure.IsCanonical (M := M))
    (C : BaseContext M) {Z : ZeroRVVolumeObject (M := M) (C.base : Set M)}
    {U V : PositiveRVVolumeObject (M := M) (C.base : Set M) k}
    (hZ : Z.Gamma B) (hU : VolumeObjectGamma U B) (hV : VolumeObjectGamma V B) :
    (volumeZeroProductRightDistribIso hc C Z U V).GammaDefinable B := by
  have hZU := hU.zeroProd hc hZ
  have hZV := hV.zeroProd hc hZ
  refine RVVolumeIso.GammaDefinable.symm hc C B ?_
  exact gamma_volume_iso_of_preserving_coordinates_full hc C _
    (volumeZeroProductCoprodFold_coordinates Z U V) (volumeZeroProductCoprodFold_density Z U V)
    (gamma_essential_volume_domain _ (hZU.coprod hZV).coordinates)
    ((gamma_rv_product_coprod_fold hc Z.underlying.obj U.underlying.obj V.underlying.obj
      hZ.domain hU.domain_graph hV.domain_graph).congr (fun _ => rfl))

theorem GammaBlowupCenter.zeroProd {Z : ZeroRVVolumeObject (M := M) S}
    {U : PositiveRVVolumeObject (M := M) S k} (h : GammaBlowupCenter U B) :
    GammaBlowupCenter (zeroProduct Z U) B := by
  intro x
  rw [zeroProduct_coordinates]
  exact h _

theorem gamma_weighted_zero_packed_chart (hc : CanonicalStructure.IsCanonical (M := M))
    {U W : PositiveRVVolumeObject (M := M) S k} (b : ElementaryBlowup U W)
    (Z : ZeroRVVolumeObject (M := M) S) (hZ : Z.Gamma B)
    (hb : RVMapGamma b.packedChartMap B) :
    RVMapGamma (weightedZeroElementary b Z).packedChartMap B := by
  apply gamma_rv_product_map_select hc (gamma_rv_identity_map hc _ hZ.domain) hb _
    (Fin.cast (Nat.add_assoc _ _ _))
  intro x
  obtain ⟨z,w,rfl⟩ := exists_rvPackPair Z.underlying.obj.domain W.underlying.obj.domain x
  rw [rvUnpack_pair]
  change ((rvPack _ _).toImage (b.zeroProductChart Z.underlying (rvPackPair _ _ z w))).val = _
  rw [b.zeroProductChart_pair]
  change Fin.append (Fin.append z.val (b.projection w).val) (b.parameter w).val =
    Fin.append z.val (Fin.append (b.chartMap w).val.1 (b.chartMap w).val.2) ∘ _
  rw [Fin.append_assoc]
  rfl

theorem VolumeBlowup.GammaDefinable.weightedZero
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    {U V : PositiveRVVolumeObject (M := M) (C.base : Set M) k} {b : VolumeBlowup U V}
    (hb : b.GammaDefinable B) {Z : ZeroRVVolumeObject (M := M) (C.base : Set M)} (hZ : Z.Gamma B)
    (hU : VolumeObjectGamma U B) (hV : VolumeObjectGamma V B) :
    (weightedZeroBlowup hc C b Z).GammaDefinable B :=
  ⟨hb.locus.zeroProd hc hZ,hb.complement.zeroProd hc hZ,hb.blown.zeroProd hc hZ,
    gamma_weighted_zero_packed_chart hc b.elementary Z hZ hb.elementary,
    hb.centerAlgebraic.zeroProd,
    (gamma_zero_product_iso hc C hU (hb.locus.coprod hb.complement) hZ hZ hZ.refl_iso hb.source).trans hc C B
      (gamma_volume_zero_product_right_distrib_iso hc C hZ hb.locus hb.complement),
    (gamma_zero_product_iso hc C hV (hb.blown.coprod hb.complement) hZ hZ hZ.refl_iso hb.target).trans hc C B
      (gamma_volume_zero_product_right_distrib_iso hc C hZ hb.blown hb.complement)⟩

def GammaVolumeObjects.zeroProd (hc : CanonicalStructure.IsCanonical (M := M))
    (Z : GammaZeroRVObjects B S) (U : GammaVolumeObjects B S k) : GammaVolumeObjects B S k :=
  ⟨HK.zeroProduct Z.val U.val,U.property.zeroProd hc Z.property⟩

def GammaVolumeObjects.posZeroProd (hc : CanonicalStructure.IsCanonical (M := M))
    (U : GammaVolumeObjects B S k) (Z : GammaZeroRVObjects B S) : GammaVolumeObjects B S k :=
  ⟨HK.positiveZeroProduct U.val Z.val,U.property.posZeroProd hc Z.property⟩

theorem GammaIteratedVolumeBlowup.weightedZero
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    {U V : GammaVolumeObjects B (C.base : Set M) k} {d : ℕ}
    (h : GammaIteratedVolumeBlowup B (C.base : Set M) k d U V) (Z : GammaZeroRVObjects B (C.base : Set M)) :
    GammaIteratedVolumeBlowup B (C.base : Set M) k d (U.zeroProd hc Z) (V.zeroProd hc Z) := by
  induction h with
  | refl U => exact .refl _
  | @step d U V W b h ih =>
    obtain ⟨b,hb⟩ := b
    exact .step (V := V.zeroProd hc Z)
      ⟨weightedZeroBlowup hc C b Z.val,hb.weightedZero hc C Z.property U.property V.property⟩ ih

theorem GammaVolumeBlowupEquivalent.weightedZero
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    {U V : GammaVolumeObjects B (C.base : Set M) k}
    (h : GammaVolumeBlowupEquivalent B (C.base : Set M) k U V) (Z : GammaZeroRVObjects B (C.base : Set M)) :
    GammaVolumeBlowupEquivalent B (C.base : Set M) k (U.zeroProd hc Z) (V.zeroProd hc Z) := by
  obtain ⟨a,b,U',V',hU,hV,e,he⟩ := h
  exact ⟨a,b,U'.zeroProd hc Z,V'.zeroProd hc Z,hU.weightedZero hc C Z,hV.weightedZero hc C Z,
    zeroProductIso hc C (ZeroRVVolumeIso.refl Z.val) e,
    gamma_zero_product_iso hc C U'.property V'.property Z.property Z.property Z.property.refl_iso he⟩

theorem GammaVolumeBlowupEquivalent.weightedPositiveZero
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    {U V : GammaVolumeObjects B (C.base : Set M) k}
    (h : GammaVolumeBlowupEquivalent B (C.base : Set M) k U V) (Z : GammaZeroRVObjects B (C.base : Set M)) :
    GammaVolumeBlowupEquivalent B (C.base : Set M) k (U.posZeroProd hc Z) (V.posZeroProd hc Z) := by
  have e1 : GammaVolumeBlowupEquivalent B (C.base : Set M) k (U.posZeroProd hc Z) (U.zeroProd hc Z) :=
    GammaVolumeBlowupEquivalent.of_iso C B (U := U.posZeroProd hc Z) (V := U.zeroProd hc Z)
      (mixedProductSwapIso hc C U.val Z.val) (gamma_mixed_product_swap_iso hc C U.property Z.property)
  have e2 : GammaVolumeBlowupEquivalent B (C.base : Set M) k (V.zeroProd hc Z) (V.posZeroProd hc Z) :=
    GammaVolumeBlowupEquivalent.of_iso C B (U := V.zeroProd hc Z) (V := V.posZeroProd hc Z)
      ((mixedProductSwapIso hc C V.val Z.val).symm hc C)
      ((gamma_mixed_product_swap_iso hc C V.property Z.property).symm hc C B)
  exact (e1.trans hc C B (h.weightedZero hc C Z)).trans hc C B e2

end IntegrationInACVF.Section7
