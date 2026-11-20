import Integration7.GammaHeadCoefficientRows
import Integration7.GammaFunPositiveActions
import Integration7.GammaFunHeadIntegrals
import Integration7.FrozenHeadVolumeIntegrals
import Integration7.GammaVFProducts

/-! **Head integrals commute with positive coefficients** (positive functions). At every VF point,
the head-integral row of a coefficient product is Gamma-equivalent to the coefficient times the
head-integral row. The comparison runs in the definably closed extension of the row context over
the VF field closure of the row base (which gives Gamma unary special preparations with Gamma
chains), and is reduced back to the row base. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section5 (Point GammaSetDefinable GammaGraphDefinable gammaLogicInput carrier VF RV GammaChainDefinable headImage)
open IntegrationInACVF.Section5 IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {B B' : Base (M := M)} {k : ℕ}

theorem VolumeObjectGamma.baseMono {S : Set M} {U : PositiveRVVolumeObject (M := M) S k} (hU : VolumeObjectGamma U B)
    (hr : B.real ⊆ B'.real) (hg : B.gamma ⊆ B'.gamma) : VolumeObjectGamma U B' :=
  hU.changeBase (GammaBaseDominated.of_subset hr hg)

theorem RVVolumeIso.GammaDefinable.baseMono {S : Set M} {U V : PositiveRVVolumeObject (M := M) S k}
    {e : RVVolumeIso U V} (he : e.GammaDefinable B) (hr : B.real ⊆ B'.real) (hg : B.gamma ⊆ B'.gamma) :
    e.GammaDefinable B' :=
  (GammaBaseDominated.of_subset hr hg).definable he

theorem CommonContextVolumeEquivalent.of_extend_context {C D : BaseContext M}
    (hCD : (C.base : Set M) ⊆ (D.base : Set M)) {U V : GammaVolumeObjects B (C.base : Set M) k}
    (h : CommonContextVolumeEquivalent B D (U.extend hCD) (V.extend hCD)) : CommonContextVolumeEquivalent B C U V := by
  obtain ⟨E,hDE,h⟩ := h
  exact ⟨E,hCD.trans hDE,h⟩

theorem CommonContextVolumeEquivalent.reduce {C : BaseContext M} (H : GammaDefinableBaseReduction B' B)
    {U V : GammaVolumeObjects B' (C.base : Set M) k} (h : CommonContextVolumeEquivalent B' C U V) :
    CommonContextVolumeEquivalent B C (H.volumeObjects U) (H.volumeObjects V) := by
  obtain ⟨D,hCD,h⟩ := h
  exact ⟨D,hCD,H.volumeCommon h⟩

theorem SelectedVFVolumeFamily.Gamma.densityGraphFamily (hc : CanonicalStructure.IsCanonical (M := M)) {C : BaseContext M}
    {n a : ℕ} {F : SelectedVFVolumeFamily C n a k} (hF : F.Gamma B) : F.densityGraph.Gamma B :=
  ⟨hF.densityGraph,gamma_coordinate_volume_density_graph hc (hF.native_domain hc) F.densityGraph.form (Fin.last a)
    F.densityGraph_form_last⟩

end IntegrationInACVF.Section7

namespace IntegrationInACVF.Section7.GammaFun
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n k p : ℕ}
variable (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
variable (Ξ : Set (Values.Gamma (M := M))) (hΞ : Cardinal.mk Ξ < C.κ)
variable (hGenerated : VFGammaGeneratedBase (gammaNamedBase C Ξ))

set_option quotPrecheck false
local notation "𝔅" => gammaNamedBase C Ξ
local notation "𝔇" => gammaNamedCodeContext C Ξ hΞ
local notation "𝔖" => ((gammaNamedCodeContext C Ξ hΞ).base : Set M)

theorem named_code_context_common_names : commonRealNames (⟨𝔖,Ξ⟩ : Base (M := M)) ⊆ 𝔖 := by
  rintro d (hd | hd)
  · exact hd
  · exact gamma_named_code_context_names C Ξ hΞ (Or.inr hd)

variable (γ : Values.Gamma (M := M)) (hγ : γ ∈ Ξ) (hγ1 : 1 < γ)

include hγ hγ1 in
set_option maxHeartbeats 1600000 in
/-- **Rows of head integrals of positive coefficient products** at every VF point. -/
theorem head_left_product_common (U : GammaVolumeObjects 𝔅 𝔖 p) (F : Presentation C Ξ hΞ (n+1) k)
    (x : Fin (n+1) → VFType (M := M)) :
    CommonContextVolumeEquivalent (rowGammaBase 𝔅 x) (vfParameterVolumeContext 𝔇 x)
      ⟨((F.leftProduct hc C Ξ hΞ U).headIntegral hc C Ξ hΞ hGenerated).family.rowInContext x,
        ((F.leftProduct hc C Ξ hΞ U).headIntegral hc C Ξ hΞ hGenerated).gamma.row hc x⟩
      ((rowCoefficient C Ξ hΞ U x).prod hc
        ⟨(F.headIntegral hc C Ξ hΞ hGenerated).family.rowInContext x,
          (F.headIntegral hc C Ξ hΞ hGenerated).gamma.row hc x⟩) := by
  let S := F.leftProduct hc C Ξ hΞ U
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
  -- the head fibres
  let Fx := (F.family.headFibre x).extendContext hD
  have hFx : Fx.Gamma Bx := F.gamma.headFibre hc x hD
  have hFx' : Fx.Gamma G' := ⟨hFx.domain.mono hBG' (Set.Subset.refl _),hFx.densityGraph.mono hBG' (Set.Subset.refl _)⟩
  have h𝔅G' : (𝔅).real ⊆ G'.real := Set.subset_union_left.trans hBG'
  let UD : PositiveRVVolumeObject (M := M) (D.base : Set M) p := U.val.extend hCD
  have hUD : VolumeObjectGamma UD G' := (U.property.extend hCD).baseMono h𝔅G' (Set.Subset.refl _)
  let Fx' := Fx.densityGraph
  have hFxd : Fx'.Gamma G' := hFx'.densityGraphFamily hc
  -- a Gamma unary special preparation of the retained fibre over the field-named base
  obtain ⟨b,BT,TF,hTF,hBT⟩ := gamma_field_unary_special_preparation D G' (vfFieldNamedBase_field Bx) hG'D
    (nativeMixedVolumeDomain hc Fx'.domain) (by rw [nativeMixedVolumeDomain_carrier]; exact hFxd.domain)
  have hNamesD := frozen_head_volume_context_common_names hc 𝔇 Ξ (named_code_context_common_names C Ξ hΞ) x
  have hG'Ξ : G'.real ⊆ (⟨(D.base : Set M),Ξ⟩ : Base (M := M)).real := hG'D
  have hTF' : GammaChainDefinable (⟨(D.base : Set M),Ξ⟩ : Base (M := M)) TF.chain :=
    gamma_chain_mono hG'Ξ (Set.Subset.refl _) _ hTF
  -- the native coefficient family
  let R := rvCoordinateDensityNativeDomain hc D UD
  let σR : Fin (p+1) → Fin ((p+1)+(UD.underlying.obj.arity+1)) := Fin.castAdd (UD.underlying.obj.arity+1)
  let εR := Fin.natAdd (p+1) (Fin.last UD.underlying.obj.arity)
  let J := nativeCoordinateCoefficientFamily hc D Fx' R σR εR (rv_coordinate_density_native_finite hc D UD)
    (rv_coordinate_density_native_nonzero hc D UD)
  have hV : VolumeObjectGamma (rvCoordinateDensityNativeObject hc D UD) G' :=
    VolumeObjectGamma.rvCoordinateDensityNative hc D hUD
  have hJ : J.Gamma G' := hFxd.coordinateSelectedCoefficient hc hV σR (fun _ => rfl)
  obtain ⟨L0⟩ := gamma_native_coefficient_preparation_exists hc D Ξ hNamesD Fx' R σR εR
    (rv_coordinate_density_native_finite hc D UD) (rv_coordinate_density_native_nonzero hc D UD) (Fin.last _)
    Fx.densityGraph_form_last TF hTF hBT hJ
  let L := L0.monoBase hG'Ξ (Set.Subset.refl _)
  let E2 := unarySpecialStandardContraction L.special L.pullback
  have hE2 : GammaProgramDefinable G' E2.program := gamma_unary_special_standard_contraction L0.special L0.pullback L0.gamma
  -- the head fibre of the coefficient product and its fibre contraction
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
    have hΨ := hFx'.leftProduct hc hUD
    have eA := head_fibre_left_product_row_class hc (U := U.val) (F := F.family) x hD hCD hΦ1 hΨ y
    have eB := gamma_left_product_row_class hc hUD hFx' y
    have eC := coordinate_selected_coefficient_row_class hc hFxd hV σR (fun _ => rfl) y
    have h1 : GammaVolumeBlowupEquivalent (rowGammaBase G' y) (Dy.base : Set M) p
        (GammaVolumeObjects.changeBase (B := rowGammaBase G' y) (GammaVolumeObjects.extend ⟨_,hV⟩ hDy)
          (GammaBaseDominated.of_subset Set.subset_union_left (Set.Subset.refl _)))
        (GammaVolumeObjects.changeBase (B := rowGammaBase G' y) (GammaVolumeObjects.extend ⟨UD,hUD⟩ hDy)
          (GammaBaseDominated.of_subset Set.subset_union_left (Set.Subset.refl _))) :=
      GammaVolumeBlowupEquivalent.of_iso Dy _ (((rvCoordinateDensityNativeIso hc D UD).symm hc D).extend hDy)
        ((((rv_coordinate_density_native_iso_gamma hc D hUD).symm hc D G').extend hDy).baseMono
          Set.subset_union_left (Set.Subset.refl _))
    have h2 : GammaVolumeBlowupEquivalent (rowGammaBase G' y) (Dy.base : Set M) k
        ⟨Fx'.rowInContext y,hFxd.row hc y⟩ ⟨Fx.rowInContext y,hFx'.row hc y⟩ :=
      GammaVolumeBlowupEquivalent.of_iso Dy _ ((Fx.densityGraphRowIso hc y).symm hc Dy)
        ((hFx'.densityGraphRowIso hc y).symm hc Dy _)
    have hprod := (h1.product_right hc Dy ⟨Fx'.rowInContext y,hFxd.row hc y⟩).trans hc Dy _
      (h2.product_left hc Dy _)
    have eD := (gammaVolumeBlowupClass_eq_iff hc Dy _).mpr hprod
    exact (gammaVolumeBlowupClass_eq_iff hc Dy _).mp (eA.trans (eB.trans (eC.trans eD).symm))
  have h75 := gamma_family_lemma_7_5 hc D G' hG'D hΞ γ hγ hγ1 hΦ1 hJ hRows R1 E2 hR1 hE2
  -- step A: head row of the product as a fibre standard append object
  have hRowS := (((F.leftProduct hc C Ξ hΞ U).headIntegral hc C Ξ hΞ hGenerated).gamma.row hc x).extend hD
  have hA : CommonContextVolumeEquivalent G' D ⟨_,hRowS.baseMono hBG' (Set.Subset.refl _)⟩
      ⟨Φ1.standardAppendObject hc G'.gamma R1,standard_append_volume_object_gamma_of hc D G'.gamma G' _ _ _ _ _ R1 hR1⟩ :=
    CommonContextVolumeEquivalent.of_iso (headFibreIntegralVolumeIso hc 𝔇 D Ξ S.family _ x hD)
      ((head_fibre_integral_volume_iso_gamma hc 𝔇 D Ξ S.family _ x hD hRowS).baseMono hBG' (Set.Subset.refl _))
  -- step C: the coefficient chart
  have hUPH : VolumeObjectGamma (unaryPreparedHeadVolumeObject hc D Ξ TF hBT hTF' Fx'.selected (Fin.last _)
      Fx.densityGraph_label_nonzero Fx'.finite_selected) G' :=
    GammaNamed.native_coordinate_density_volume_object_gamma hc D G' _
      (gamma_headImage BT (GammaChainDefinable.target G' TF.chain hTF)) _ _ _ _
  have hLT : GammaSetDefinable G' (carrier (headImage L.target)) :=
    gamma_headImage L0.target (GammaChainDefinable.target G' L0.special.chain L0.gamma)
  have hC : CommonContextVolumeEquivalent G' D
      ⟨J.standardAppendObject hc G'.gamma E2,standard_append_volume_object_gamma_of hc D G'.gamma G' _ _ _ _ _ E2 hE2⟩
      ⟨_,hV.prod hc hUPH⟩ :=
    CommonContextVolumeEquivalent.of_iso _
      (coordinate_coefficient_contraction_product_iso_gamma hc D Ξ hNamesD Fx' R σR εR
        (rv_coordinate_density_native_finite hc D UD) (rv_coordinate_density_native_nonzero hc D UD) (Fin.last _)
        Fx.densityGraph_label_nonzero TF hBT hTF' L
        (standard_append_volume_object_gamma_of hc D G'.gamma G' _ _ _ _ _ E2 hE2) hLT)
  -- step D: coefficient factor
  have hD1 : CommonContextVolumeEquivalent G' D ⟨_,hV⟩ ⟨UD,hUD⟩ :=
    CommonContextVolumeEquivalent.of_iso ((rvCoordinateDensityNativeIso hc D UD).symm hc D)
      ((rv_coordinate_density_native_iso_gamma hc D hUD).symm hc D G')
  -- step D: head factor
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
  -- step E: back to the head row of the family
  have hRowF := ((F.headIntegral hc C Ξ hΞ hGenerated).gamma.row hc x).extend hD
  have hE : CommonContextVolumeEquivalent G' D
      ⟨Fx.standardAppendObject hc G'.gamma RF,standard_append_volume_object_gamma_of hc D G'.gamma G' _ _ _ _ _ RF hRF⟩
      ⟨_,hRowF.baseMono hBG' (Set.Subset.refl _)⟩ :=
    CommonContextVolumeEquivalent.of_iso ((headFibreIntegralVolumeIso hc 𝔇 D Ξ F.family _ x hD).symm hc D)
      (((head_fibre_integral_volume_iso_gamma hc 𝔇 D Ξ F.family _ x hD hRowF).baseMono hBG' (Set.Subset.refl _)).symm hc D G')
  have hHead := (hD3.trans hc hD2).trans hc hE
  have hAll := ((hA.trans hc h75).trans hc hC).trans hc (hD1.prod hc hHead)
  have hRed := hAll.reduce H
  exact CommonContextVolumeEquivalent.of_extend_context hD hRed

include hγ hγ1 in
/-- **Head integrals commute with positive coefficients** (almost everywhere, positive functions). -/
theorem presentation_head_left_product_ae (U : GammaVolumeObjects 𝔅 𝔖 p) (F : Presentation C Ξ hΞ (n+1) k) :
    AEEquivalent hc C Ξ hΞ ((F.leftProduct hc C Ξ hΞ U).headIntegral hc C Ξ hΞ hGenerated)
      ((F.headIntegral hc C Ξ hΞ hGenerated).leftProduct hc C Ξ hΞ U) := by
  apply ae_equivalent_of_rows
  intro x
  rw [presentation_left_product_row_class]
  exact (gammaVolumeBlowupClass_eq_iff hc _ _).mpr
    ((head_left_product_common hc C Ξ hΞ hGenerated γ hγ hγ1 U F x).descend hc _
      (row_context_names 𝔇 𝔅 (gamma_named_code_context_names C Ξ hΞ) x))

include hγ hγ1 in
/-- **Head integrals are linear for positive coefficients** on positive almost-everywhere functions. -/
theorem ae_head_integral_positive_coefficient (c : GammaVolumeBlowupClasses hc 𝔇 𝔅 p)
    (f : AEFunction hc C Ξ hΞ (n+1) k) :
    aeHeadIntegral hc C Ξ hΞ hGenerated γ hγ hγ1 (aePositiveCoefficientAction hc C Ξ hΞ p c f) =
      aePositiveCoefficientAction hc C Ξ hΞ p c (aeHeadIntegral hc C Ξ hΞ hGenerated γ hγ hγ1 f) := by
  induction c using Quotient.inductionOn with
  | h U =>
    induction f using Quotient.inductionOn with
    | h F => exact Quotient.sound (presentation_head_left_product_ae hc C Ξ hΞ hGenerated γ hγ hγ1 U F)

end IntegrationInACVF.Section7.GammaFun
