module

public import Integration7.TwoOrderProductPreparations
public import Integration7.SmallDimensionContractionNormalization

@[expose] public section

/-! Actual normalized finite RV volume objects of the constructed two
orders, and their original-Gamma normalization maps. The raw product
comparison therefore gives a comparison of these normalized objects. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5 SpecialTransformations.Section9
open IntegrationInACVF.Section5

namespace IntegrationInACVF.Section7.TwoOrderProductPreparations
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {P : Base (M := M)} {S : Set M} {d : ℕ}
variable {X Y : DefSet (M := M) S 2 0} {D E : DefSet (M := M) S 1 0}
variable {r t : RV (M := M)} {z : Fin d → RV (M := M)} {hz : ∀ j, (z j).val ∈ S}
variable {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ) (hsmall : Cardinal.mk P.real < κ)
variable (hc : CanonicalStructure.IsCanonical (M := M)) (F : TwoOrderProductPreparations X Y D E r t z hz P)

def headRawFiniteRVObject (hr : r.val ∈ S) : RVFiniteObject (M := M) F.codes 2 :=
  rvClassProductRawFiniteRVObject hc (extendBase X F.contains) (extendBase E F.contains) F.eTarget
    F.eSpecial F.headSaturated r (F.contains hr) z (fun j => F.contains (hz j)) F.headPreparation
    (constant_label_prepared_pullback_finite_volume hκ hs hsmall F.headPreparation)

def tailRawFiniteRVObject (ht : t.val ∈ S) : RVFiniteObject (M := M) F.codes 2 :=
  swappedRVClassProductRawFiniteRVObject hc (extendBase Y F.contains) (extendBase D F.contains) F.dTarget
    F.dSpecial F.tailSaturated t (F.contains ht) z (fun j => F.contains (hz j)) F.tailPreparation
    (constant_label_prepared_pullback_finite_volume hκ hs hsmall F.tailPreparation)

def headNormalizedVolumeObject (hr : r.val ∈ S) (η : RV (M := M)) (hη : η.val ∈ S) (hη0 : η ≠ 0) :
    PositiveRVVolumeObject (M := M) F.codes 1 :=
  (normalizedUnitVolumeContraction hc F.headContraction (F.headRawFiniteRVObject hκ hs hsmall hc hr).property).rescale
    η (F.contains hη) hη0

def tailNormalizedVolumeObject (ht : t.val ∈ S) (η : RV (M := M)) (hη : η.val ∈ S) (hη0 : η ≠ 0) :
    PositiveRVVolumeObject (M := M) F.codes 1 :=
  (normalizedUnitVolumeContraction hc F.tailContraction (F.tailRawFiniteRVObject hκ hs hsmall hc ht).property).rescale
    η (F.contains hη) hη0

theorem head_unit_volume_dimension_le_one (hr : r.val ∈ S) :
    rvDim (rawUnitVolumeContraction hc F.headContraction
      (F.headRawFiniteRVObject hκ hs hsmall hc hr).property).essential.obj.domain ≤ 1 := by
  let R := rawUnitVolumeContraction hc F.headContraction (F.headRawFiniteRVObject hκ hs hsmall hc hr).property
  apply constant_head_volume_dimension_le_one R.essential r
  intro u
  have h := rv_class_product_raw_projection_volume hc (extendBase X F.contains) (extendBase E F.contains) F.eTarget
    F.eSpecial F.headSaturated r (F.contains hr) z (fun j => F.contains (hz j)) F.headPreparation
    (constant_label_prepared_pullback_finite_volume hκ hs hsmall F.headPreparation)
    ⟨u.val,rvEssentialLabels_subset R.underlying.obj u.property⟩
  exact (congrFun h 0).symm

theorem tail_unit_volume_dimension_le_one (ht : t.val ∈ S) :
    rvDim (rawUnitVolumeContraction hc F.tailContraction
      (F.tailRawFiniteRVObject hκ hs hsmall hc ht).property).essential.obj.domain ≤ 1 := by
  let R := rawUnitVolumeContraction hc F.tailContraction (F.tailRawFiniteRVObject hκ hs hsmall hc ht).property
  apply constant_tail_volume_dimension_le_one R.essential t
  intro u
  have h := swapped_rv_class_product_raw_projection_volume (extendBase Y F.contains) (extendBase D F.contains) F.dTarget
    F.dSpecial F.tailSaturated t z (fun j => F.contains (hz j)) F.tailPreparation hc (F.contains ht)
    (constant_label_prepared_pullback_finite_volume hκ hs hsmall F.tailPreparation)
    ⟨u.val,rvEssentialLabels_subset R.underlying.obj u.property⟩
  exact (congrFun h 1).symm

def headNormalizationVolumeIso (hr : r.val ∈ S) (η : RV (M := M)) (hη : η.val ∈ S) (hη0 : η ≠ 0) :
    RVVolumeIso (F.headVolumeObject hκ hs hsmall hc hr η hη hη0)
      (F.headNormalizedVolumeObject hκ hs hsmall hc hr η hη hη0) :=
  (smallDimensionNormalizationVolumeIso hc F.headContraction (F.headRawFiniteRVObject hκ hs hsmall hc hr).property
    ((F.head_unit_volume_dimension_le_one hκ hs hsmall hc hr).trans_lt (by decide))).rescale η (F.contains hη) hη0

def tailNormalizationVolumeIso (ht : t.val ∈ S) (η : RV (M := M)) (hη : η.val ∈ S) (hη0 : η ≠ 0) :
    RVVolumeIso (F.tailVolumeObject hκ hs hsmall hc ht η hη hη0)
      (F.tailNormalizedVolumeObject hκ hs hsmall hc ht η hη hη0) :=
  (smallDimensionNormalizationVolumeIso hc F.tailContraction (F.tailRawFiniteRVObject hκ hs hsmall hc ht).property
    ((F.tail_unit_volume_dimension_le_one hκ hs hsmall hc ht).trans_lt (by decide))).rescale η (F.contains hη) hη0

theorem head_normalization_volume_iso_gamma (hPS : P.real ⊆ S)
    (hr : r.val ∈ S) (η : RV (M := M)) (hη : η.val ∈ S) (hη0 : η ≠ 0) :
    (F.headNormalizationVolumeIso hκ hs hsmall hc hr η hη hη0).GammaDefinable P :=
  (small_dimension_normalization_volume_iso_gamma hc F.headContraction
    (F.headRawFiniteRVObject hκ hs hsmall hc hr).property
    ((F.head_unit_volume_dimension_le_one hκ hs hsmall hc hr).trans_lt (by decide)) (hPS.trans F.contains)
    (gamma_headImage F.headPreparation.target
      (GammaChainDefinable.target P F.headPreparation.special.chain F.headPreparation.gamma))).rescale η (F.contains hη) hη0

theorem tail_normalization_volume_iso_gamma (hPS : P.real ⊆ S)
    (ht : t.val ∈ S) (η : RV (M := M)) (hη : η.val ∈ S) (hη0 : η ≠ 0) :
    (F.tailNormalizationVolumeIso hκ hs hsmall hc ht η hη hη0).GammaDefinable P :=
  (small_dimension_normalization_volume_iso_gamma hc F.tailContraction
    (F.tailRawFiniteRVObject hκ hs hsmall hc ht).property
    ((F.tail_unit_volume_dimension_le_one hκ hs hsmall hc ht).trans_lt (by decide)) (hPS.trans F.contains)
    (gamma_headImage F.tailPreparation.target
      (GammaChainDefinable.target P F.tailPreparation.special.chain F.tailPreparation.gamma))).rescale η (F.contains hη) hη0

theorem normalized_volume_comparison (hPS : P.real ⊆ S)
    (hr : r.val ∈ S) (ht : t.val ∈ S) (η : RV (M := M)) (hη : η.val ∈ S) (hη0 : η ≠ 0)
    (i : RVVolumeIso (F.headVolumeObject hκ hs hsmall hc hr η hη hη0)
      (F.tailVolumeObject hκ hs hsmall hc ht η hη hη0)) (hi : i.GammaDefinable P) :
    ∃ j : RVVolumeIso (F.headNormalizedVolumeObject hκ hs hsmall hc hr η hη hη0)
      (F.tailNormalizedVolumeObject hκ hs hsmall hc ht η hη hη0), j.GammaDefinable P := by
  let eH := F.headNormalizationVolumeIso hκ hs hsmall hc hr η hη hη0
  let eT := F.tailNormalizationVolumeIso hκ hs hsmall hc ht η hη hη0
  have heH := F.head_normalization_volume_iso_gamma hκ hs hsmall hc hPS hr η hη hη0
  have heT := F.tail_normalization_volume_iso_gamma hκ hs hsmall hc hPS ht η hη hη0
  have hdH : rvDim (F.headNormalizedVolumeObject hκ hs hsmall hc hr η hη hη0).essential.obj.domain < 2 :=
    (rvDim_eq_of_bijective (finiteIsoMap eH.iso) (finiteIsoMap_bijective eH.iso)).symm.trans_lt
      ((F.head_unit_volume_dimension_le_one hκ hs hsmall hc hr).trans_lt (by decide))
  exact ⟨((eH.symmOfSmallDimension hdH).transOfSmallDimension i hdH).transOfSmallDimension eT hdH,
    ((heH.symmOfSmallDimension hdH).transOfSmallDimension hi hdH).transOfSmallDimension heT hdH⟩

end IntegrationInACVF.Section7.TwoOrderProductPreparations
