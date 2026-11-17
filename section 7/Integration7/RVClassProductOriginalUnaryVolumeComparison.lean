module

public import Integration7.RVClassProductRawVolumeObjects
public import Integration7.SwappedRVClassProductRawVolumeObjects
public import Integration7.ConstantLabelPreparedVolumeComparisons
public import Integration7.FixedHeadEssentialVolumeIsomorphisms
public import Integration7.FixedTailEssentialVolumeIsomorphisms
public import Integration7.SmallDimensionVolumeIsoOperations

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! The raw RV volume object of the constructed product standard
contraction is compared all the way to the original unary preparation,
including its essential restriction, over the original Gamma base. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.DefinableGeometry.Space.prod
  SpecialTransformations.Section4.realSpace SpecialTransformations.Milestone0.sortEval
  SpecialTransformations.Section4.vfSpace SpecialTransformations.Section4.rvSpace
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5 SpecialTransformations.Section9
open IntegrationInACVF.Section5 IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {P : Base (M := M)} {S : Set M} {b d : ℕ}

theorem rv_class_product_original_unary_volume_comparison {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ) (hsmall : Cardinal.mk P.real < κ)
    (hc : CanonicalStructure.IsCanonical (M := M)) (hPS : P.real ⊆ S)
    (A : DefSet (M := M) S 2 0) (B : DefSet (M := M) S 1 0)
    (B' : DefSet (M := M) S 1 b) (T : SpecialBijection B B')
    (hT : GammaChainDefinable P T.chain) (hB' : IsRVPullback (carrier B'))
    (hSat : HeadSaturated (carrier A)) (r : RV (M := M)) (hr : r.val ∈ S) (hr0 : r.val ≠ iRVZero)
    (t : Fin d → RV (M := M)) (ht : ∀ i, (t i).val ∈ S)
    (L : ConstantRVLabelSpecialPreparation T (headImage (fixedRVLabelDomain A t ht))
      (Fin.append (fun _ : Fin 1 => r) (Fin.append (Fin.elim0 : Fin 0 → RV (M := M)) t)) P)
    (η : RV (M := M)) (hη : η.val ∈ S) (hη0 : η ≠ 0) :
    let hLF := constant_label_prepared_pullback_finite_volume hκ hs hsmall L
    let hBF := gamma_special_pullback_finite_volume hκ hs hsmall T hT hB' (fun _ => Set.toFinite _)
    let V := canonicalFiniteRVObject hc ⟨pullbackObject B',hBF⟩
    ∃ e : RVVolumeIso
      ((rvClassProductRawVolumeObject hc A B B' T hSat r hr t ht L hLF).rescale η hη hη0)
      ((prependFixedRVVolume (rvFiniteEssential V) r hr (VolumeForm.one _)).rescale η hη hη0),
      e.GammaDefinable P := by
  intro hLF hBF V
  let R := rvClassProductRawVolumeObject hc A B B' T hSat r hr t ht L hLF
  have hHead (u : R.essential.obj.domain) : R.essential.obj.value u 0 = r := by
    let v : R.underlying.obj.domain := ⟨u.val,rvEssentialLabels_subset R.underlying.obj u.property⟩
    exact (congrFun (rv_class_product_raw_projection_volume hc A B B' T hSat r hr t ht L hLF v) 0).symm
  have hd : rvDim R.essential.obj.domain < 2 :=
    lt_of_le_of_lt (constant_head_volume_dimension_le_one R.essential r hHead) (by decide)
  obtain ⟨e₀,he₀⟩ := rv_class_product_raw_volume_comparison hc A B B' T hSat r hr t ht L hLF hPS η hη hη0
  obtain ⟨e₁,he₁⟩ := constant_label_prepared_product_volume_comparison hκ hs hsmall hc hPS
    hT hB' L r hr hr0 η hη hη0
  have hVE := gamma_essential_volume_domain (⟨V,VolumeForm.one _⟩ : PositiveRVVolumeObject (M := M) S 0)
    (canonical_gamma_object_volume_graph hc (FiniteRV.gammaPullbackAt hPS B'
      (GammaChainDefinable.target P T.chain hT) hBF))
  let e₂ := (fixedHeadEssentialVolumeIso V r hr hr0).rescale η hη hη0
  have he₂ := (fixed_head_essential_volume_iso_gamma V r hr hr0 hVE).rescale η hη hη0
  exact ⟨(e₀.transOfSmallDimension e₁ hd).transOfSmallDimension e₂ hd,
    (he₀.transOfSmallDimension he₁ hd).transOfSmallDimension he₂ hd⟩

theorem swapped_rv_class_product_original_unary_volume_comparison {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ) (hsmall : Cardinal.mk P.real < κ)
    (hc : CanonicalStructure.IsCanonical (M := M)) (hPS : P.real ⊆ S)
    (Z : DefSet (M := M) S 2 0) (B : DefSet (M := M) S 1 0)
    (B' : DefSet (M := M) S 1 b) (T : SpecialBijection B B')
    (hT : GammaChainDefinable P T.chain) (hB' : IsRVPullback (carrier B'))
    (hSat : HeadSaturated (carrier (vfPermutationImage Z (Equiv.swap 0 1)))) (r : RV (M := M)) (hr : r.val ∈ S) (hr0 : r.val ≠ iRVZero)
    (t : Fin d → RV (M := M)) (ht : ∀ i, (t i).val ∈ S)
    (L : ConstantRVLabelSpecialPreparation T (headImage (fixedRVLabelDomain (vfPermutationImage Z (Equiv.swap 0 1)) t ht))
      (Fin.append (fun _ : Fin 1 => r) (Fin.append (Fin.elim0 : Fin 0 → RV (M := M)) t)) P)
    (η : RV (M := M)) (hη : η.val ∈ S) (hη0 : η ≠ 0) :
    let hLF := constant_label_prepared_pullback_finite_volume hκ hs hsmall L
    let hBF := gamma_special_pullback_finite_volume hκ hs hsmall T hT hB' (fun _ => Set.toFinite _)
    let V := canonicalFiniteRVObject hc ⟨pullbackObject B',hBF⟩
    ∃ e : RVVolumeIso
      ((swappedRVClassProductRawVolumeObject hc Z B B' T hSat r hr t ht L hLF).rescale η hη hη0)
      ((appendFixedRVVolume (rvFiniteEssential V) r hr (VolumeForm.one _)).rescale η hη hη0),
      e.GammaDefinable P := by
  intro hLF hBF V
  let R := swappedRVClassProductRawVolumeObject hc Z B B' T hSat r hr t ht L hLF
  have hTail (u : R.essential.obj.domain) : R.essential.obj.value u 1 = r := by
    let v : R.underlying.obj.domain := ⟨u.val,rvEssentialLabels_subset R.underlying.obj u.property⟩
    exact (congrFun (swapped_rv_class_product_raw_projection_volume Z B B' T hSat r t ht L hc hr hLF v) 1).symm
  have hd : rvDim R.essential.obj.domain < 2 :=
    lt_of_le_of_lt (constant_tail_volume_dimension_le_one R.essential r hTail) (by decide)
  obtain ⟨e₀,he₀⟩ := swapped_rv_class_product_raw_volume_comparison hc Z B B' T hSat r hr t ht L hLF hPS η hη hη0
  obtain ⟨e₁,he₁⟩ := constant_label_prepared_tail_product_volume_comparison hκ hs hsmall hc hPS
    hT hB' L r hr hr0 η hη hη0
  have hVE := gamma_essential_volume_domain (⟨V,VolumeForm.one _⟩ : PositiveRVVolumeObject (M := M) S 0)
    (canonical_gamma_object_volume_graph hc (FiniteRV.gammaPullbackAt hPS B'
      (GammaChainDefinable.target P T.chain hT) hBF))
  let e₂ := (fixedTailEssentialVolumeIso V r hr hr0).rescale η hη hη0
  have he₂ := (fixed_tail_essential_volume_iso_gamma V r hr hr0 hVE).rescale η hη hη0
  exact ⟨(e₀.transOfSmallDimension e₁ hd).transOfSmallDimension e₂ hd,
    (he₀.transOfSmallDimension he₁ hd).transOfSmallDimension he₂ hd⟩

end IntegrationInACVF.Section7
