import Integration7.GammaCoefficientLiftIsos
import Integration7.GammaFunPositiveActions

/-! **Coefficient linearity of the Gamma-named appended integral (positive degrees).** The
appended-convention Gamma-named integral of the coefficient-first product `U • F` of a Gamma positive
RV coefficient `U` and a Gamma-named positive presentation `F` is the class of the product of `U`
with the appended object of `F`, up to the arithmetic degree identification. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section9
open SpecialTransformations.Section5 (Point GammaSetDefinable GammaGraphDefinable gammaLogicInput carrier VF RV)
open IntegrationInACVF.Section5 IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7.GammaNamed
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {k : ℕ}

set_option maxHeartbeats 3200000 in
/-- A Gamma standard contraction of the lift of a Gamma RV object is common-context equivalent to
the object. -/
theorem gamma_lift_standard_contraction (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (G : Base (M := M)) (hGC : G.real ⊆ (C.base : Set M)) (hΞ : Cardinal.mk G.gamma < C.κ)
    (hGenerated : VFGammaGeneratedBase G) (hNames : commonRealNames G ⊆ (C.base : Set M))
    (hGeneric : ∀ {p : ℕ} (x : Fin p → VF (M := M)), AlgebraicIndependent (vfParameterField G.real) x →
      AlgebraicIndependent (vfParameterField (C.base : Set M)) x)
    (γ : Values.Gamma (M := M)) (hγ : γ ∈ G.gamma) (hγ1 : 1 < γ)
    (U : GammaVolumeObjects G (C.base : Set M) k) {σ : Equiv.Perm (Fin (k+1))}
    (E : StandardContraction (nativeMixedVolumeDomain hc (rvVolumeLift U.val).densityGraph.domain) σ)
    (hE : GammaProgramDefinable G E.program) :
    CommonContextVolumeEquivalent G C
      ⟨(rvVolumeLift U.val).standardContractionObject hc C G.gamma E,
        standard_contraction_object_gamma hc C G hGC _ (rv_volume_lift_gamma hc C hGC U.property) E hE⟩ U := by
  obtain ⟨P,⟨e,he⟩,hP⟩ := gamma_lift_contraction_comparison hc C G hGC hΞ hGenerated hNames hGeneric γ hγ hγ1
    (rvVolumeLift U.val) (rv_volume_lift_gamma hc C hGC U.property) E hE
  have hK := rv_volume_lift_common_context_kernel hc C G hGC hΞ hGenerated hNames hGeneric γ hγ hγ1 P U
    (e.symm hc C) (he.symm hc C)
  exact (hP.symm hc).trans hc hK

end IntegrationInACVF.Section7.GammaNamed

namespace IntegrationInACVF.Section7.GammaFun
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n k p : ℕ}
variable (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
variable (Ξ : Set (Values.Gamma (M := M))) (hΞ : Cardinal.mk Ξ < C.κ)
variable (hGenerated : VFGammaGeneratedBase (gammaNamedBase C Ξ))

set_option quotPrecheck false
local notation "𝔅" => gammaNamedBase C Ξ
local notation "𝔇" => gammaNamedCodeContext C Ξ hΞ
local notation "𝔖" => ((gammaNamedCodeContext C Ξ hΞ).base : Set M)

variable (γ : Values.Gamma (M := M)) (hγ : γ ∈ Ξ) (hγ1 : 1 < γ)

set_option maxHeartbeats 6400000 in
include hγ hγ1 in
/-- **Positive coefficient linearity of the appended Gamma-named integral.** -/
theorem presentation_left_product_appended_integral (U : GammaVolumeObjects 𝔅 𝔖 p) (F : Presentation C Ξ hΞ n k) :
    (F.leftProduct hc C Ξ hΞ U).appendedIntegral hc C Ξ hΞ hGenerated =
      gammaClassReindex hc 𝔇 (appended_positive_coefficient_degree_eq (n+1) p k)
        (gammaVolumeBlowupClass hc 𝔇 𝔅 (U.prod hc
          (F.appendedObject hc C Ξ hΞ (F.contraction hc C Ξ hΞ hGenerated) (F.contraction_gamma hc C Ξ hΞ hGenerated)))) := by
  have hBC := gamma_named_code_context_base C Ξ hΞ
  have hreal := small_gamma_named_real C Ξ hΞ
  have hNames := gamma_named_code_context_names C Ξ hΞ
  have hGeneric : ∀ {p : ℕ} (x : Fin p → SpecialTransformations.Section5.VF (M := M)),
      AlgebraicIndependent (vfParameterField (𝔅).real) x → AlgebraicIndependent (vfParameterField 𝔖) x :=
    fun x hx => gamma_named_code_context_generic C Ξ hΞ hc x hx
  let h := appended_positive_coefficient_degree_eq (n+1) p k
  let S := F.leftProduct hc C Ξ hΞ U
  let TS := S.contraction hc C Ξ hΞ hGenerated
  have hTS := S.contraction_gamma hc C Ξ hΞ hGenerated
  let TF := F.contraction hc C Ξ hΞ hGenerated
  have hTF := F.contraction_gamma hc C Ξ hΞ hGenerated
  let LS := S.family.appendedFullLift
  have hLS := presentation_appended_full_lift_gamma hc C Ξ hΞ S
  let LF := F.family.appendedFullLift
  have hLF := presentation_appended_full_lift_gamma hc C Ξ hΞ F
  have hLU := rv_volume_lift_gamma hc 𝔇 hBC U.property
  let P := (rvVolumeLift U.val).prod LF
  have hP : VFVolumeObjectGamma P 𝔅 := hLU.prod hc hLF
  have hPh : VFVolumeObjectGamma (P.reindexDegree h) 𝔅 := hP.reindexDegree h
  obtain ⟨ES,hES,_,_,_⟩ := generated_base_standard_contraction_exists (B := 𝔅) (𝔇).saturated (𝔇).model00
    hreal hGenerated hBC (nativeMixedVolumeDomain hc LS.densityGraph.domain) hLS.densityGraph (Equiv.refl _)
  obtain ⟨EF,hEF,_,_,_⟩ := generated_base_standard_contraction_exists (B := 𝔅) (𝔇).saturated (𝔇).model00
    hreal hGenerated hBC (nativeMixedVolumeDomain hc LF.densityGraph.domain) hLF.densityGraph (Equiv.refl _)
  obtain ⟨EU,hEU,_,_,_⟩ := generated_base_standard_contraction_exists (B := 𝔅) (𝔇).saturated (𝔇).model00
    hreal hGenerated hBC (nativeMixedVolumeDomain hc (rvVolumeLift U.val).densityGraph.domain) hLU.densityGraph
    (Equiv.refl _)
  obtain ⟨EP,hEP,_,_,_⟩ := generated_base_standard_contraction_exists (B := 𝔅) (𝔇).saturated (𝔇).model00
    hreal hGenerated hBC (nativeMixedVolumeDomain hc P.densityGraph.domain) hP.densityGraph (Equiv.refl _)
  obtain ⟨EPh,hEPh,_,_,_⟩ := generated_base_standard_contraction_exists (B := 𝔅) (𝔇).saturated (𝔇).model00
    hreal hGenerated hBC (nativeMixedVolumeDomain hc (P.reindexDegree h).densityGraph.domain) hPh.densityGraph
    (Equiv.refl _)
  have c1 := presentation_appended_full_lift hc C Ξ hΞ hGenerated γ hγ hγ1 S TS hTS ES hES
  have c2 := GammaNamed.gamma_vf_iso_contraction_comparison hc 𝔇 𝔅 hBC hΞ hGenerated hNames hGeneric γ hγ hγ1
    LS (P.reindexDegree h) hLS hPh _ (selected_positive_coefficient_appended_lift_gamma hc 𝔇 hBC U.property F.gamma)
    ES EPh hES hEPh
  have c3 := GammaNamed.gamma_heq_contraction hc 𝔇 𝔅 hBC hΞ hGenerated hNames hGeneric γ hγ hγ1 h
    (vf_reindex_degree_heq P h) hPh hP EPh EP hEPh hEP
  have c4 := GammaNamed.gamma_prod_contraction hc 𝔇 𝔅 hBC hΞ hGenerated hNames hGeneric γ hγ hγ1
    (rvVolumeLift U.val) LF hLU hLF hP EU EF EP hEU hEF hEP
  have c5 := GammaNamed.gamma_lift_standard_contraction hc 𝔇 𝔅 hBC hΞ hGenerated hNames hGeneric γ hγ hγ1 U EU hEU
  have c6 := presentation_appended_full_lift hc C Ξ hΞ hGenerated γ hγ hγ1 F TF hTF EF hEF
  have d := (c4.trans hc (CommonContextVolumeEquivalent.prod hc c5 (c6.symm hc))).reindexDegree hc h
  have hAll := ((c1.trans hc c2).trans hc c3).trans hc d
  exact (gammaVolumeBlowupClass_eq_iff hc 𝔇 𝔅).mpr (hAll.descend hc 𝔇 hNames)

end IntegrationInACVF.Section7.GammaFun
