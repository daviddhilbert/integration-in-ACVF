import Integration7.GammaFunHeadPositiveLinearity
import Integration7.GammaZeroCoefficientFibreCharts
import Integration7.GammaFunAllDegreeActions

/-! **Head integrals commute with weighted degree-zero coefficients** (positive functions). The
head fibre of a weighted degree-zero product is the weighted product of the head fibre; the
comparison runs as for positive coefficients through the native zero-coefficient family and the
zero-coefficient contraction chart, over the VF field closure of the row base. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section5 (Point GammaSetDefinable GammaGraphDefinable gammaLogicInput carrier VF RV GammaChainDefinable headImage)
open IntegrationInACVF.Section5 IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {G : Base (M := M)} {n a k : ℕ}

/-- Membership in the head fibre of a weighted degree-zero product. -/
theorem mem_head_fibre_weighted_zero {C D : BaseContext M} (Z : HK.ZeroRVVolumeObject (M := M) (C.base : Set M))
    (F : SelectedVFVolumeFamily C (n+1) a k) (x : Fin n → VFType (M := M))
    (hD : ((vfParameterVolumeContext C x).base : Set M) ⊆ (D.base : Set M))
    (hCD : (C.base : Set M) ⊆ (D.base : Set M)) (q : Point (M := M) 1 (a+Z.underlying.obj.arity)) :
    q ∈ (((HK.selectedFamilyWeightedZeroProduct F Z).headFibre x).extendContext hD).domain.carrier ↔
      q ∈ (HK.selectedFamilyWeightedZeroProduct ((F.headFibre x).extendContext hD) (Z.extend hCD)).domain.carrier := by
  change (Fin.cons (q.1 0) x,q.2) ∈ (mixedRVFactorDomain F.domain Z.underlying.obj.domain).carrier ↔ _
  rw [mem_mixed_rv_factor_domain]
  exact (mem_mixed_rv_factor_domain ((F.headFibre x).extendContext hD).domain
    (Z.extend hCD).underlying.obj.domain q.1 q.2).symm

theorem head_fibre_weighted_zero_row_class (hc : CanonicalStructure.IsCanonical (M := M)) {C D : BaseContext M}
    {Z : HK.ZeroRVVolumeObject (M := M) (C.base : Set M)}
    {F : SelectedVFVolumeFamily C (n+1) a k} (x : Fin n → VFType (M := M))
    (hD : ((vfParameterVolumeContext C x).base : Set M) ⊆ (D.base : Set M))
    (hCD : (C.base : Set M) ⊆ (D.base : Set M))
    (h₁ : (((HK.selectedFamilyWeightedZeroProduct F Z).headFibre x).extendContext hD).Gamma G)
    (h₂ : (HK.selectedFamilyWeightedZeroProduct ((F.headFibre x).extendContext hD) (Z.extend hCD)).Gamma G)
    (y : Fin 1 → VFType (M := M)) :
    gammaVolumeBlowupClass hc (vfParameterVolumeContext D y) (rowGammaBase G y)
        ⟨(((HK.selectedFamilyWeightedZeroProduct F Z).headFibre x).extendContext hD).rowInContext y,h₁.row hc y⟩ =
      gammaVolumeBlowupClass hc (vfParameterVolumeContext D y) (rowGammaBase G y)
        ⟨(HK.selectedFamilyWeightedZeroProduct ((F.headFibre x).extendContext hD) (Z.extend hCD)).rowInContext y,
          h₂.row hc y⟩ := by
  refine gamma_class_eq_of_select hc _ _ _ _ id (fun t ht => (mem_head_fibre_weighted_zero Z F x hD hCD (y,t)).mp ht)
    (fun s hs => ⟨s,(mem_head_fibre_weighted_zero Z F x hD hCD (y,s)).mpr hs,rfl⟩) (fun _ _ _ _ h => h)
    (fun _ => rfl) (fun t => ?_)
  have hL := weighted_zero_product_density ((F.headFibre x).extendContext hD) (Z.extend hCD)
    ⟨(y,t.val),(mem_head_fibre_weighted_zero Z F x hD hCD (y,t.val)).mp t.property⟩
  have hR := weighted_zero_product_density F Z ⟨(Fin.cons (y 0) x,t.val),t.property⟩
  change (HK.selectedFamilyWeightedZeroProduct ((F.headFibre x).extendContext hD) (Z.extend hCD)).form.value
      ⟨(y,t.val),_⟩ = (HK.selectedFamilyWeightedZeroProduct F Z).form.value ⟨(Fin.cons (y 0) x,t.val),t.property⟩
  rw [hL,hR]
  rfl

theorem CommonContextVolumeEquivalent.zeroProd (hc : CanonicalStructure.IsCanonical (M := M)) {C : BaseContext M}
    {U V : GammaVolumeObjects G (C.base : Set M) k} (h : CommonContextVolumeEquivalent G C U V)
    (Z : HK.GammaZeroRVObjects G (C.base : Set M)) :
    CommonContextVolumeEquivalent G C (U.zeroProd hc Z) (V.zeroProd hc Z) := by
  obtain ⟨D,hCD,h⟩ := h
  exact ⟨D,hCD,h.weightedZero hc D ⟨Z.val.extend hCD,Z.property.extend hCD⟩⟩

end IntegrationInACVF.Section7

namespace IntegrationInACVF.Section7.GammaFun
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n k : ℕ}
variable (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
variable (Ξ : Set (Values.Gamma (M := M))) (hΞ : Cardinal.mk Ξ < C.κ)
variable (hGenerated : VFGammaGeneratedBase (gammaNamedBase C Ξ))

set_option quotPrecheck false
local notation "𝔅" => gammaNamedBase C Ξ
local notation "𝔇" => gammaNamedCodeContext C Ξ hΞ
local notation "𝔖" => ((gammaNamedCodeContext C Ξ hΞ).base : Set M)

variable (γ : Values.Gamma (M := M)) (hγ : γ ∈ Ξ) (hγ1 : 1 < γ)

include hγ hγ1 in
set_option maxHeartbeats 1600000 in
/-- **Rows of head integrals of weighted degree-zero coefficient products** at every VF point. -/
theorem head_zero_coef_common (Z : HK.GammaZeroRVObjects 𝔅 𝔖) (F : Presentation C Ξ hΞ (n+1) k)
    (x : Fin (n+1) → VFType (M := M)) :
    CommonContextVolumeEquivalent (rowGammaBase 𝔅 x) (vfParameterVolumeContext 𝔇 x)
      ⟨((F.zeroCoef hc C Ξ hΞ Z).headIntegral hc C Ξ hΞ hGenerated).family.rowInContext x,
        ((F.zeroCoef hc C Ξ hΞ Z).headIntegral hc C Ξ hΞ hGenerated).gamma.row hc x⟩
      (GammaVolumeObjects.posZeroProd hc
        ⟨(F.headIntegral hc C Ξ hΞ hGenerated).family.rowInContext x,
          (F.headIntegral hc C Ξ hΞ hGenerated).gamma.row hc x⟩ (zeroRowCoefficient Z x)) := by
  let S := F.zeroCoef hc C Ξ hΞ Z
  let Cx := vfParameterVolumeContext 𝔇 x
  let Bx := rowGammaBase 𝔅 x
  let D := frozenHeadVolumeContext hc 𝔇 x
  have hD : (Cx.base : Set M) ⊆ (D.base : Set M) := frozen_head_volume_context_contains hc 𝔇 x
  have hBxCx : Bx.real ⊆ (Cx.base : Set M) := Set.union_subset
    ((gamma_named_code_context_base C Ξ hΞ).trans (fun y hy => vfParameterVolumeContext_contains 𝔇 x (Or.inl hy)))
    (fun y hy => vfParameterVolumeContext_contains 𝔇 x (Or.inr hy))
  let G' := vfFieldNamedBase Bx
  have hG'D : G'.real ⊆ (D.base : Set M) := vf_field_named_base_subset_definably_closed hc Cx Bx hBxCx
  have hBG' : Bx.real ⊆ G'.real := Set.subset_union_left
  let H := vfFieldBaseReduction Bx
  have hCD : 𝔖 ⊆ (D.base : Set M) := fun y hy => hD (vfParameterVolumeContext_contains 𝔇 x (Or.inl hy))
  let Fx := (F.family.headFibre x).extendContext hD
  have hFx : Fx.Gamma Bx := F.gamma.headFibre hc x hD
  have hFx' : Fx.Gamma G' := ⟨hFx.domain.mono hBG' (Set.Subset.refl _),hFx.densityGraph.mono hBG' (Set.Subset.refl _)⟩
  have h𝔅G' : (𝔅).real ⊆ G'.real := Set.subset_union_left.trans hBG'
  let ZD : HK.ZeroRVVolumeObject (M := M) (D.base : Set M) := Z.val.extend hCD
  have hZD : ZD.Gamma G' := (Z.property.extend hCD).changeBase (GammaBaseDominated.of_subset h𝔅G' (Set.Subset.refl _))
  let Fx' := Fx.densityGraph
  have hFxd : Fx'.Gamma G' := hFx'.densityGraphFamily hc
  obtain ⟨b,BT,TF,hTF,hBT⟩ := gamma_field_unary_special_preparation D G' (vfFieldNamedBase_field Bx) hG'D
    (nativeMixedVolumeDomain hc Fx'.domain) (by rw [nativeMixedVolumeDomain_carrier]; exact hFxd.domain)
  have hNamesD := frozen_head_volume_context_common_names hc 𝔇 Ξ (named_code_context_common_names C Ξ hΞ) x
  have hG'Ξ : G'.real ⊆ (⟨(D.base : Set M),Ξ⟩ : Base (M := M)).real := hG'D
  have hTF' : GammaChainDefinable (⟨(D.base : Set M),Ξ⟩ : Base (M := M)) TF.chain :=
    gamma_chain_mono hG'Ξ (Set.Subset.refl _) _ hTF
  -- the native zero-coefficient family
  let Rz := HK.zeroRVNativeDensityDomain hc D ZD
  let N := HK.zeroRVNativeDensityObject hc D ZD
  have hN : N.Gamma G' := hZD.zeroRVNativeDensity hc D
  let J := HK.nativeZeroCoefficientFamily hc D Fx' Rz (Fin.last ZD.underlying.obj.arity)
    (ordinary_rv_native_labels_finite hc D ZD.densityGraph.underlying) (HK.zero_rv_native_density_nonzero hc D ZD)
  have hJ : J.Gamma G' := hFxd.weightedZero hc hN
  obtain ⟨L0⟩ := gamma_native_zero_coefficient_preparation_exists hc D Ξ hNamesD Fx' Rz _
    (ordinary_rv_native_labels_finite hc D ZD.densityGraph.underlying) (HK.zero_rv_native_density_nonzero hc D ZD)
    (Fin.last _) Fx.densityGraph_form_last TF hTF hBT hJ
  let L := L0.monoBase hG'Ξ (Set.Subset.refl _)
  let E2 := unarySpecialStandardContraction L.special L.pullback
  have hE2 : GammaProgramDefinable G' E2.program := gamma_unary_special_standard_contraction L0.special L0.pullback L0.gamma
  let Φ1 := (S.family.headFibre x).extendContext hD
  have hΦ1 : Φ1.Gamma G' := by
    have h := S.gamma.headFibre hc x hD
    exact ⟨h.domain.mono hBG' (Set.Subset.refl _),h.densityGraph.mono hBG' (Set.Subset.refl _)⟩
  let R1 := headFibreStandardContraction hc 𝔇 D S.family (S.headPrep hc C Ξ hΞ hGenerated) x hD
  have hR1 : GammaProgramDefinable G' R1.program :=
    gamma_program_mono hBG' (Set.Subset.refl _) _ (gamma_head_fibre_standard_contraction hc 𝔇 D S.family _
      (S.headPrep_map hc C Ξ hΞ hGenerated) (S.headPrep_target hc C Ξ hΞ hGenerated) x hD)
  have hRows : ∀ y, GammaRowsEquivalent hc D G' hΦ1 hJ y := by
    intro y
    let Dy := vfParameterVolumeContext D y
    have hDy : (D.base : Set M) ⊆ (Dy.base : Set M) := fun _ h => vfParameterVolumeContext_contains D y (Or.inl h)
    have hΨ := hFx'.weightedZero hc hZD
    have eA := head_fibre_weighted_zero_row_class hc (Z := Z.val) (F := F.family) x hD hCD hΦ1 hΨ y
    have eB := gamma_weighted_zero_row_class hc hFx' ⟨ZD,hZD⟩ y
    have eC := gamma_weighted_zero_row_class hc hFxd ⟨N,hN⟩ y
    have hf : ((Fx.densityGraphRowIso hc y).symm hc Dy).GammaDefinable (rowGammaBase G' y) :=
      (hFx'.densityGraphRowIso hc y).symm hc Dy _
    have hg : (((HK.zeroRVNativeDensityIso hc D ZD).symm).extend hDy).GammaDefinable (rowGammaBase G' y) :=
      ((zero_rv_native_density_iso_gamma hc D hZD).symm).mono Set.subset_union_left (Set.Subset.refl _)
    have hprod : GammaVolumeBlowupEquivalent (rowGammaBase G' y) (Dy.base : Set M) k
        (GammaVolumeObjects.posZeroProd hc ⟨Fx'.rowInContext y,hFxd.row hc y⟩ (zeroRowCoefficient ⟨N,hN⟩ y))
        (GammaVolumeObjects.posZeroProd hc ⟨Fx.rowInContext y,hFx'.row hc y⟩ (zeroRowCoefficient ⟨ZD,hZD⟩ y)) :=
      GammaVolumeBlowupEquivalent.of_iso Dy _ (HK.positiveZeroProductIso hc Dy _ _)
        (gamma_positive_zero_product_iso hc Dy hf hg)
    have eD := (gammaVolumeBlowupClass_eq_iff hc Dy _).mpr hprod
    exact (gammaVolumeBlowupClass_eq_iff hc Dy _).mp (eA.trans (eB.trans (eC.trans eD).symm))
  have h75 := gamma_family_lemma_7_5 hc D G' hG'D hΞ γ hγ hγ1 hΦ1 hJ hRows R1 E2 hR1 hE2
  have hRowS := (((F.zeroCoef hc C Ξ hΞ Z).headIntegral hc C Ξ hΞ hGenerated).gamma.row hc x).extend hD
  have hA : CommonContextVolumeEquivalent G' D ⟨_,hRowS.baseMono hBG' (Set.Subset.refl _)⟩
      ⟨Φ1.standardAppendObject hc G'.gamma R1,standard_append_volume_object_gamma_of hc D G'.gamma G' _ _ _ _ _ R1 hR1⟩ :=
    CommonContextVolumeEquivalent.of_iso (headFibreIntegralVolumeIso hc 𝔇 D Ξ S.family _ x hD)
      ((head_fibre_integral_volume_iso_gamma hc 𝔇 D Ξ S.family _ x hD hRowS).baseMono hBG' (Set.Subset.refl _))
  have hUPH : VolumeObjectGamma (unaryPreparedHeadVolumeObject hc D Ξ TF hBT hTF' Fx'.selected (Fin.last _)
      Fx.densityGraph_label_nonzero Fx'.finite_selected) G' :=
    GammaNamed.native_coordinate_density_volume_object_gamma hc D G' _
      (gamma_headImage BT (GammaChainDefinable.target G' TF.chain hTF)) _ _ _ _
  have hLT : GammaSetDefinable G' (carrier (headImage L.target)) :=
    gamma_headImage L0.target (GammaChainDefinable.target G' L0.special.chain L0.gamma)
  have hC : CommonContextVolumeEquivalent G' D
      ⟨J.standardAppendObject hc G'.gamma E2,standard_append_volume_object_gamma_of hc D G'.gamma G' _ _ _ _ _ E2 hE2⟩
      (GammaVolumeObjects.zeroProd hc ⟨N,hN⟩ ⟨_,hUPH⟩) :=
    CommonContextVolumeEquivalent.of_iso _
      (zero_coefficient_contraction_product_iso_gamma hc D Ξ hNamesD Fx' Rz _
        (ordinary_rv_native_labels_finite hc D ZD.densityGraph.underlying) (HK.zero_rv_native_density_nonzero hc D ZD)
        (Fin.last _) Fx.densityGraph_label_nonzero TF hBT hTF' L
        (standard_append_volume_object_gamma_of hc D G'.gamma G' _ _ _ _ _ E2 hE2) hLT)
  have hD1 : CommonContextVolumeEquivalent G' D (GammaVolumeObjects.zeroProd hc ⟨N,hN⟩ ⟨_,hUPH⟩)
      (GammaVolumeObjects.zeroProd hc ⟨ZD,hZD⟩ ⟨_,hUPH⟩) :=
    CommonContextVolumeEquivalent.of_iso (HK.zeroProductIso hc D (HK.zeroRVNativeDensityIso hc D ZD).symm
        (RVVolumeIso.refl hc D _))
      (gamma_zero_product_iso hc D hUPH hUPH hN hZD (zero_rv_native_density_iso_gamma hc D hZD).symm
        (hUPH.identity_iso hc D))
  let RF := headFibreStandardContraction hc 𝔇 D F.family (F.headPrep hc C Ξ hΞ hGenerated) x hD
  have hRF : GammaProgramDefinable G' RF.program :=
    gamma_program_mono hBG' (Set.Subset.refl _) _ (gamma_head_fibre_standard_contraction hc 𝔇 D F.family _
      (F.headPrep_map hc C Ξ hΞ hGenerated) (F.headPrep_target hc C Ξ hΞ hGenerated) x hD)
  let ET := unarySpecialStandardContraction TF hBT
  have hET : GammaProgramDefinable G' ET.program := gamma_unary_special_standard_contraction TF hBT hTF
  have hRefl : ∀ y, GammaRowsEquivalent hc D G' hFx' hFx' y :=
    fun y => GammaVolumeBlowupEquivalent.refl hc _ _ _
  have hD2 := gamma_family_lemma_7_5 hc D G' hG'D hΞ γ hγ hγ1 hFx' hFx' hRefl ET RF hET hRF
  have hD3 : CommonContextVolumeEquivalent G' D ⟨_,hUPH⟩
      ⟨Fx.standardAppendObject hc G'.gamma ET,standard_append_volume_object_gamma_of hc D G'.gamma G' _ _ _ _ _ ET hET⟩ :=
    CommonContextVolumeEquivalent.of_iso ((unaryPreparedHeadVolumeIso hc D Ξ TF hBT hTF' Fx'.selected (Fin.last _)
      Fx.densityGraph_label_nonzero Fx'.finite_selected).symm hc D)
      ((unary_prepared_head_volume_iso_gamma hc D Ξ TF hBT hTF' _ _ _ _
        (standard_append_volume_object_gamma_of hc D G'.gamma G' _ _ _ _ _ ET hET)).symm hc D G')
  have hRowF := ((F.headIntegral hc C Ξ hΞ hGenerated).gamma.row hc x).extend hD
  have hE : CommonContextVolumeEquivalent G' D
      ⟨Fx.standardAppendObject hc G'.gamma RF,standard_append_volume_object_gamma_of hc D G'.gamma G' _ _ _ _ _ RF hRF⟩
      ⟨_,hRowF.baseMono hBG' (Set.Subset.refl _)⟩ :=
    CommonContextVolumeEquivalent.of_iso ((headFibreIntegralVolumeIso hc 𝔇 D Ξ F.family _ x hD).symm hc D)
      (((head_fibre_integral_volume_iso_gamma hc 𝔇 D Ξ F.family _ x hD hRowF).baseMono hBG' (Set.Subset.refl _)).symm hc D G')
  have hHead := (hD3.trans hc hD2).trans hc hE
  have hRowF' := hRowF.baseMono hBG' (Set.Subset.refl _)
  have hSwap : CommonContextVolumeEquivalent G' D (GammaVolumeObjects.zeroProd hc ⟨ZD,hZD⟩ ⟨_,hRowF'⟩)
      (GammaVolumeObjects.posZeroProd hc ⟨_,hRowF'⟩ ⟨ZD,hZD⟩) :=
    CommonContextVolumeEquivalent.of_iso ((HK.mixedProductSwapIso hc D _ ZD).symm hc D)
      ((gamma_mixed_product_swap_iso hc D hRowF' hZD).symm hc D G')
  have hAll := (((hA.trans hc h75).trans hc hC).trans hc hD1).trans hc ((hHead.zeroProd hc ⟨ZD,hZD⟩).trans hc hSwap)
  have hRed := hAll.reduce H
  exact CommonContextVolumeEquivalent.of_extend_context hD hRed

include hγ hγ1 in
/-- **Head integrals commute with weighted degree-zero coefficients** (almost everywhere, positive functions). -/
theorem presentation_head_zero_coef_ae (Z : HK.GammaZeroRVObjects 𝔅 𝔖) (F : Presentation C Ξ hΞ (n+1) k) :
    AEEquivalent hc C Ξ hΞ ((F.zeroCoef hc C Ξ hΞ Z).headIntegral hc C Ξ hΞ hGenerated)
      ((F.headIntegral hc C Ξ hΞ hGenerated).zeroCoef hc C Ξ hΞ Z) := by
  apply ae_equivalent_of_rows
  intro x
  refine Eq.trans ?_ (gamma_weighted_zero_row_class hc (F.headIntegral hc C Ξ hΞ hGenerated).gamma Z x).symm
  exact (gammaVolumeBlowupClass_eq_iff hc _ _).mpr
    ((head_zero_coef_common hc C Ξ hΞ hGenerated γ hγ hγ1 Z F x).descend hc _
      (row_context_names 𝔇 𝔅 (gamma_named_code_context_names C Ξ hΞ) x))

end IntegrationInACVF.Section7.GammaFun
