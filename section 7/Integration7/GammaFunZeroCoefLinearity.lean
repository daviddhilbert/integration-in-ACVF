import Integration7.GammaVFZeroProducts
import Integration7.HKWeightedFamilyZeroProductLifts

/-! **Weighted degree-zero coefficients: linearity of the Gamma-named integral.** The canonical
and appended Gamma-named integrals of the weighted degree-zero product `F • Z` of a Gamma-named
positive presentation are the positive-zero products of the integrals of `F` with `Z`. The proof
compares full VF lifts (`fullLift (F • Z) ≅ fullLift F ⊗ Z`) and uses the contraction of weighted
degree-zero factors; coordinate permutations and degree casts commute with positive-zero
products by coordinate-preserving identifications. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section9
open SpecialTransformations.Section5 (Point GammaSetDefinable GammaGraphDefinable gammaLogicInput carrier VF RV)
open IntegrationInACVF.Section5 IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {B : Base (M := M)} {p q : ℕ}
variable (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)

theorem class_pos_zero_permute (P : GammaVolumeObjects B (C.base : Set M) p) (Z : HK.GammaZeroRVObjects B (C.base : Set M))
    (e : Equiv.Perm (Fin (p+1))) :
    gammaVolumeBlowupClass hc C B ((P.posZeroProd hc Z).permuteVolume hc C e) =
      gammaVolumeBlowupClass hc C B ((P.permuteVolume hc C e).posZeroProd hc Z) :=
  gamma_class_eq_of_select hc C B _ _ id (fun _ h => h) (fun s hs => ⟨s,hs,rfl⟩) (fun _ _ _ _ h => h)
    (fun t => by
      change (HK.positiveZeroProduct (P.val.permuteVolume e) Z.val).underlying.obj.value ⟨t.val,t.property⟩ =
        (HK.positiveZeroProduct P.val Z.val).underlying.obj.value ⟨t.val,t.property⟩ ∘ e
      rw [HK.positiveZeroProduct_coordinates,HK.positiveZeroProduct_coordinates]
      rfl)
    (fun t => by
      change (HK.positiveZeroProduct (P.val.permuteVolume e) Z.val).form.value ⟨t.val,t.property⟩ =
        (HK.positiveZeroProduct P.val Z.val).form.value ⟨t.val,t.property⟩
      rw [HK.positiveZeroProduct_density,HK.positiveZeroProduct_density]
      rfl)

theorem class_pos_zero_reindex (P : GammaVolumeObjects B (C.base : Set M) p) (Z : HK.GammaZeroRVObjects B (C.base : Set M))
    (h : q = p) :
    gammaVolumeBlowupClass hc C B ((P.posZeroProd hc Z).reindexDegree h) =
      gammaVolumeBlowupClass hc C B ((P.reindexDegree h).posZeroProd hc Z) :=
  gamma_class_eq_of_select hc C B _ _ id (fun _ h => h) (fun s hs => ⟨s,hs,rfl⟩) (fun _ _ _ _ h => h)
    (fun t => by
      change (HK.positiveZeroProduct (P.val.reindexDegree h) Z.val).underlying.obj.value ⟨t.val,t.property⟩ =
        (HK.positiveZeroProduct P.val Z.val).underlying.obj.value ⟨t.val,t.property⟩ ∘ (finCongr (congrArg Nat.succ h))
      rw [HK.positiveZeroProduct_coordinates,HK.positiveZeroProduct_coordinates]
      rfl)
    (fun t => by
      change (HK.positiveZeroProduct (P.val.reindexDegree h) Z.val).form.value ⟨t.val,t.property⟩ =
        (HK.positiveZeroProduct P.val Z.val).form.value ⟨t.val,t.property⟩
      rw [HK.positiveZeroProduct_density,HK.positiveZeroProduct_density]
      rfl)

theorem class_eq_of_reindex_eq {U V : GammaVolumeObjects B (C.base : Set M) p} (h : q = p)
    (hUV : gammaVolumeBlowupClass hc C B (U.reindexDegree h) = gammaVolumeBlowupClass hc C B (V.reindexDegree h)) :
    gammaVolumeBlowupClass hc C B U = gammaVolumeBlowupClass hc C B V :=
  eq_of_heq ((gamma_class_reindex_heq hc C B h U).symm.trans ((heq_of_eq hUV).trans (gamma_class_reindex_heq hc C B h V)))

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

set_option maxHeartbeats 6400000 in
include hGenerated hγ hγ1 in
/-- The full VF lift of a presentation contracts to its canonical integral object, up to the
degree identification. -/
theorem presentation_full_lift_contraction (F : Presentation C Ξ hΞ n k)
    (T : StandardContraction (nativeMixedVolumeDomain hc F.family.densityGraph.domain) (Equiv.refl _))
    (hT : GammaProgramDefinable 𝔅 T.program) {υ : Equiv.Perm (Fin (((n+1)+k)+1))}
    (E : StandardContraction (nativeMixedVolumeDomain hc F.family.fullLift.densityGraph.domain) υ)
    (hE : GammaProgramDefinable 𝔅 E.program) :
    CommonContextVolumeEquivalent 𝔅 𝔇
      ⟨F.family.fullLift.standardContractionObject hc 𝔇 (𝔅).gamma E,
        GammaNamed.standard_contraction_object_gamma hc 𝔇 𝔅 (gamma_named_code_context_base C Ξ hΞ) _
          (F.gamma.fullLift hc) E hE⟩
      ((F.integralObject hc C Ξ hΞ T hT).reindexDegree (family_realization_degree_eq n k)) := by
  have hBC := gamma_named_code_context_base C Ξ hΞ
  have hreal := small_gamma_named_real C Ξ hΞ
  have hNames := gamma_named_code_context_names C Ξ hΞ
  have hGeneric : ∀ {p : ℕ} (x : Fin p → SpecialTransformations.Section5.VF (M := M)),
      AlgebraicIndependent (vfParameterField (𝔅).real) x → AlgebraicIndependent (vfParameterField 𝔖) x :=
    fun x hx => gamma_named_code_context_generic C Ξ hΞ hc x hx
  let h0 := family_realization_degree_eq n k
  have hX := F.gamma.fullLift hc
  obtain ⟨eX,heX⟩ := gamma_full_lift_density_graph_iso hc 𝔇 F.gamma
  let A := nativeMixedVolumeDomain hc F.family.densityGraph.domain
  have hAg : GammaSetDefinable 𝔅 (carrier A) := F.gamma.native_domain hc
  have hW := realization_gamma hc C Ξ hΞ A hAg F.family.densityGraph.selected F.family.densityGraph.finite_selected
    (Fin.last F.arity) F.family.densityGraph_label_nonzero
  let W := selectedCoordinateVolumeRealization hc A F.family.densityGraph.selected
    F.family.densityGraph.finite_selected (Fin.last F.arity) F.family.densityGraph_label_nonzero
  let X' := F.family.densityGraph.fullLift
  have hX' : VFVolumeObjectGamma X' 𝔅 :=
    VFVolumeObjectGamma.of_heq h0 (family_density_graph_full_lift_realization_heq hc F.family) hW
  obtain ⟨EX',hEX',_,_,_⟩ := generated_base_standard_contraction_exists (B := 𝔅) (𝔇).saturated (𝔇).model00
    hreal hGenerated hBC (nativeMixedVolumeDomain hc X'.densityGraph.domain) hX'.densityGraph (Equiv.refl _)
  obtain ⟨EW,hEW,_,_,_⟩ := generated_base_standard_contraction_exists (B := 𝔅) (𝔇).saturated (𝔇).model00
    hreal hGenerated hBC (nativeMixedVolumeDomain hc W.densityGraph.domain) hW.densityGraph (Equiv.refl _)
  have c3 := GammaNamed.gamma_vf_iso_contraction_comparison hc 𝔇 𝔅 hBC hΞ hGenerated hNames hGeneric γ hγ hγ1
    F.family.fullLift X' hX hX' eX heX E EX' hE hEX'
  have c4 := GammaNamed.gamma_heq_contraction hc 𝔇 𝔅 hBC hΞ hGenerated hNames hGeneric γ hγ hγ1 h0
    (family_density_graph_full_lift_realization_heq hc F.family) hX' hW EX' EW hEX' hEW
  have c5 := GammaNamed.gamma_selected_realization_contraction hc 𝔇 𝔅 hBC hΞ hGenerated hNames hGeneric γ hγ hγ1
    A hAg F.family.densityGraph.selected F.family.densityGraph.finite_selected (Fin.last F.arity)
    F.family.densityGraph_label_nonzero T hT hW EW hEW
  exact c3.trans hc (c4.trans hc ((c5.symm hc).reindexDegree hc h0))

set_option maxHeartbeats 6400000 in
include hγ hγ1 in
/-- **Weighted degree-zero coefficient linearity of the canonical integral.** -/
theorem presentation_zero_coef_integral (Z : HK.GammaZeroRVObjects 𝔅 𝔖) (F : Presentation C Ξ hΞ n k) :
    (F.zeroCoef hc C Ξ hΞ Z).integral hc C Ξ hΞ hGenerated =
      gammaVolumeBlowupClass hc 𝔇 𝔅 ((F.integralObject hc C Ξ hΞ (F.contraction hc C Ξ hΞ hGenerated)
        (F.contraction_gamma hc C Ξ hΞ hGenerated)).posZeroProd hc Z) := by
  have hBC := gamma_named_code_context_base C Ξ hΞ
  have hreal := small_gamma_named_real C Ξ hΞ
  have hNames := gamma_named_code_context_names C Ξ hΞ
  have hGeneric : ∀ {p : ℕ} (x : Fin p → SpecialTransformations.Section5.VF (M := M)),
      AlgebraicIndependent (vfParameterField (𝔅).real) x → AlgebraicIndependent (vfParameterField 𝔖) x :=
    fun x hx => gamma_named_code_context_generic C Ξ hΞ hc x hx
  let h0 := family_realization_degree_eq n k
  let S := F.zeroCoef hc C Ξ hΞ Z
  let XS := S.family.fullLift
  let XF := F.family.fullLift
  have hXS := S.gamma.fullLift hc
  have hXF := F.gamma.fullLift hc
  have hXZ : VFVolumeObjectGamma (HK.positiveVFZeroProduct XF Z.val) 𝔅 := hXF.weightedZero hc Z.property
  obtain ⟨ES,hES,_,_,_⟩ := generated_base_standard_contraction_exists (B := 𝔅) (𝔇).saturated (𝔇).model00
    hreal hGenerated hBC (nativeMixedVolumeDomain hc XS.densityGraph.domain) hXS.densityGraph (Equiv.refl _)
  obtain ⟨EF,hEF,_,_,_⟩ := generated_base_standard_contraction_exists (B := 𝔅) (𝔇).saturated (𝔇).model00
    hreal hGenerated hBC (nativeMixedVolumeDomain hc XF.densityGraph.domain) hXF.densityGraph (Equiv.refl _)
  obtain ⟨EZ,hEZ,_,_,_⟩ := generated_base_standard_contraction_exists (B := 𝔅) (𝔇).saturated (𝔇).model00
    hreal hGenerated hBC (nativeMixedVolumeDomain hc (HK.positiveVFZeroProduct XF Z.val).densityGraph.domain)
    hXZ.densityGraph (Equiv.refl _)
  have hIso : (VFVolumeIso.of_bijection (HK.weightedVolumeFamilyZeroProductLiftBijection hc F.family Z.val)).GammaDefinable 𝔅 :=
    ⟨hXS.domain,hXZ.domain,vf_identity_map_gamma _ (fun _ => rfl) hXS.domain⟩
  have a1 := presentation_full_lift_contraction hc C Ξ hΞ hGenerated γ hγ hγ1 S (S.contraction hc C Ξ hΞ hGenerated)
    (S.contraction_gamma hc C Ξ hΞ hGenerated) ES hES
  have a2 := GammaNamed.gamma_vf_iso_contraction_comparison hc 𝔇 𝔅 hBC hΞ hGenerated hNames hGeneric γ hγ hγ1
    XS _ hXS hXZ _ hIso ES EZ hES hEZ
  have a3 := GammaNamed.gamma_weighted_zero_contraction hc 𝔇 𝔅 hBC hΞ hGenerated hNames hGeneric γ hγ hγ1
    XF hXF Z hXZ EF EZ hEF hEZ
  have a4 := (presentation_full_lift_contraction hc C Ξ hΞ hGenerated γ hγ hγ1 F (F.contraction hc C Ξ hΞ hGenerated)
    (F.contraction_gamma hc C Ξ hΞ hGenerated) EF hEF).posZeroProd hc Z
  have hAll := (((a1.symm hc).trans hc a2).trans hc a3).trans hc a4
  apply class_eq_of_reindex_eq hc 𝔇 h0
  refine ((gammaVolumeBlowupClass_eq_iff hc 𝔇 𝔅).mpr (hAll.descend hc 𝔇 hNames)).trans ?_
  exact (class_pos_zero_reindex hc 𝔇 _ Z h0).symm

set_option maxHeartbeats 3200000 in
include hγ hγ1 in
/-- **Weighted degree-zero coefficient linearity of the appended integral.** -/
theorem presentation_zero_coef_appended_integral (Z : HK.GammaZeroRVObjects 𝔅 𝔖) (F : Presentation C Ξ hΞ n k) :
    (F.zeroCoef hc C Ξ hΞ Z).appendedIntegral hc C Ξ hΞ hGenerated =
      gammaVolumeBlowupClass hc 𝔇 𝔅 ((F.appendedObject hc C Ξ hΞ (F.contraction hc C Ξ hΞ hGenerated)
        (F.contraction_gamma hc C Ξ hΞ hGenerated)).posZeroProd hc Z) := by
  let e := (appendedToOriginalVolumePermutation (n+1) k).symm
  let hS := selected_append_degree_eq n k
  let I := F.integralObject hc C Ξ hΞ (F.contraction hc C Ξ hΞ hGenerated) (F.contraction_gamma hc C Ξ hΞ hGenerated)
  rw [presentation_appended_integral_eq_permute,presentation_zero_coef_integral hc C Ξ hΞ hGenerated γ hγ hγ1,
    gamma_class_reindex_class,gamma_class_permute_class]
  change gammaVolumeBlowupClass hc 𝔇 𝔅 (((I.posZeroProd hc Z).reindexDegree hS).permuteVolume hc 𝔇 e) = _
  have h1 := class_pos_zero_reindex hc 𝔇 I Z hS
  have h1' : gammaVolumeBlowupClass hc 𝔇 𝔅 (((I.posZeroProd hc Z).reindexDegree hS).permuteVolume hc 𝔇 e) =
      gammaVolumeBlowupClass hc 𝔇 𝔅 (((I.reindexDegree hS).posZeroProd hc Z).permuteVolume hc 𝔇 e) := by
    rw [← gamma_class_permute_class,← gamma_class_permute_class,h1]
  rw [h1',class_pos_zero_permute]
  apply (gammaVolumeBlowupClass_eq_iff hc 𝔇 𝔅).mpr
  exact (gamma_selected_appended_permuted hc 𝔇 𝔅 _ _ _ _ _ (F.contraction hc C Ξ hΞ hGenerated)
    (F.contraction_gamma hc C Ξ hΞ hGenerated)).weightedPositiveZero hc 𝔇 Z

end IntegrationInACVF.Section7.GammaFun
