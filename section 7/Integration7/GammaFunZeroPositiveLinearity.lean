import Integration7.GammaFunGradedModule
import Integration7.HKZeroPositiveCoefficientLiftBijections

/-! **Positive coefficients on Gamma-named degree-zero functions: integral linearity.** The
appended Gamma-named integral of the positive-coefficient product `U • F` of a Gamma degree-zero
presentation `F` is the class of the product of `U` with the integral of `F`, up to the degree
identification; in the Gamma-named RV semiring this is `∫(U • F) = [U] * ∫F`. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section9
open SpecialTransformations.Section5 (Point GammaSetDefinable GammaGraphDefinable gammaLogicInput carrier VF RV)
open IntegrationInACVF.Section5 IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {G : Base (M := M)}

set_option maxHeartbeats 1600000 in
/-- **The zero-family coefficient lift isomorphism is Gamma.** -/
theorem zero_positive_coefficient_lift_gamma (hc : CanonicalStructure.IsCanonical (M := M))
    (C : BaseContext M) (hGC : G.real ⊆ (C.base : Set M)) {n a p : ℕ}
    {F : HK.ZeroVFVolumeFamily C (n+1) a} (hF : F.Gamma G)
    {U : PositiveRVVolumeObject (M := M) (C.base : Set M) p} (hU : VolumeObjectGamma U G) :
    (VFVolumeIso.of_bijection ((definableVolumeFamilyAppendedSelectionBijection hc (F.mulConstant U)).trans hc C
      ((HK.zeroPositiveCoefficientLiftBijection hc F U).symm hc C))).GammaDefinable G := by
  let h := HK.zero_positive_coefficient_lift_degree n p
  have hS : VFVolumeObjectGamma (HK.selectedZeroFamilyPositiveProduct U F).appendedFullLift G :=
    (hF.positiveProduct hc hU).appendedFullLift hc
  have hLU := rv_volume_lift_gamma hc C hGC hU
  have hP : VFVolumeObjectGamma (((rvVolumeLift U).prod F.fullVFObject).reindexDegree h) G :=
    (hLU.prod hc hF.fullVFObject).reindexDegree h
  have hB : VFBijGamma (definableVolumeFamilyAppendedSelectionBijection hc (F.mulConstant U)) G :=
    vf_rv_coordinate_map_gamma _ (Fin.castAdd (p+1)) (fun _ => rfl) hS.domain
  have hA : VFBijGamma (HK.zeroPositiveCoefficientLiftBijection hc F U) G :=
    vf_rv_coordinate_map_gamma _ (finAddFlip : Fin (a+U.underlying.obj.arity) ≃ Fin (U.underlying.obj.arity+a))
      (fun _ => rfl) hP.domain
  exact ⟨hS.domain,hP.domain,hB.trans hc C (hA.symm hc C)⟩

end IntegrationInACVF.Section7

namespace IntegrationInACVF.Section7.GammaFun
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n p : ℕ}
variable (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
variable (Ξ : Set (Values.Gamma (M := M))) (hΞ : Cardinal.mk Ξ < C.κ)
variable (hGenerated : VFGammaGeneratedBase (gammaNamedBase C Ξ))

set_option quotPrecheck false
local notation "𝔅" => gammaNamedBase C Ξ
local notation "𝔇" => gammaNamedCodeContext C Ξ hΞ
local notation "𝔖" => ((gammaNamedCodeContext C Ξ hΞ).base : Set M)

variable (γ : Values.Gamma (M := M)) (hγ : γ ∈ Ξ) (hγ1 : 1 < γ)

set_option maxHeartbeats 3200000 in
include hγ hγ1 in
/-- The Gamma-named integration equivalence sends a Gamma VF class to the class of any Gamma
standard contraction of a representative. -/
theorem gamma_named_integration_equiv_contraction {k : ℕ} (X : GammaVFVolumeObjects 𝔅 𝔖 k)
    {σ : Equiv.Perm (Fin (k+1))} (E : StandardContraction (nativeMixedVolumeDomain hc X.val.densityGraph.domain) σ)
    (hE : GammaProgramDefinable 𝔅 E.program) :
    gammaNamedIntegrationEquiv hc C Ξ hΞ hGenerated γ hγ hγ1 k (gammaVFVolumeClass hc 𝔇 𝔅 X) =
      gammaVolumeBlowupClass hc 𝔇 𝔅 ⟨X.val.standardContractionObject hc 𝔇 (𝔅).gamma E,
        GammaNamed.standard_contraction_object_gamma hc 𝔇 𝔅 (gamma_named_code_context_base C Ξ hΞ) _ X.property E hE⟩ := by
  have hBC := gamma_named_code_context_base C Ξ hΞ
  have hNames := gamma_named_code_context_names C Ξ hΞ
  have hGeneric : ∀ {p : ℕ} (x : Fin p → SpecialTransformations.Section5.VF (M := M)),
      AlgebraicIndependent (vfParameterField (𝔅).real) x → AlgebraicIndependent (vfParameterField 𝔖) x :=
    fun x hx => gamma_named_code_context_generic C Ξ hΞ hc x hx
  obtain ⟨P,⟨e,he⟩,hP⟩ := GammaNamed.gamma_lift_contraction_comparison hc 𝔇 𝔅 hBC hΞ hGenerated hNames hGeneric
    γ hγ hγ1 X.val X.property E hE
  apply (Equiv.symm_apply_eq _).mpr
  rw [Equiv.ofBijective_apply]
  change gammaVFVolumeClass hc 𝔇 𝔅 X = gammaVFVolumeClass hc 𝔇 𝔅 (gammaVolumeLift hc 𝔇 (fun _ h => hBC h) _)
  refine ((gammaVFVolumeClass_eq_iff hc 𝔇 𝔅 (U := X) (V := gammaVolumeLift hc 𝔇 (fun _ h => hBC h) P)).mpr
    ⟨e,he⟩).trans ?_
  exact gamma_named_lift_class_eq_of_blowup_class_eq hc C Ξ hΞ hGenerated P _
    ((gammaVolumeBlowupClass_eq_iff hc 𝔇 𝔅).mpr (hP.descend hc 𝔇 hNames))

set_option maxHeartbeats 6400000 in
include hγ hγ1 in
/-- **Positive coefficient linearity of the appended integral on degree-zero presentations.** -/
theorem zero_presentation_pos_coef_appended_integral (U : GammaVolumeObjects 𝔅 𝔖 p) (F : ZeroPresentation C Ξ hΞ n)
    {σ : Equiv.Perm (Fin (n+1))}
    (E0 : StandardContraction (nativeMixedVolumeDomain hc F.family.fullVFObject.densityGraph.domain) σ)
    (hE0 : GammaProgramDefinable 𝔅 E0.program) :
    (F.posCoef hc C Ξ hΞ U).appendedIntegral hc C Ξ hΞ hGenerated =
      gammaClassReindex hc 𝔇 (HK.zero_positive_coefficient_lift_degree n p)
        (gammaVolumeBlowupClass hc 𝔇 𝔅 (U.prod hc ⟨F.family.fullVFObject.standardContractionObject hc 𝔇 (𝔅).gamma E0,
          GammaNamed.standard_contraction_object_gamma hc 𝔇 𝔅 (gamma_named_code_context_base C Ξ hΞ) _
            F.gamma.fullVFObject E0 hE0⟩)) := by
  have hBC := gamma_named_code_context_base C Ξ hΞ
  have hreal := small_gamma_named_real C Ξ hΞ
  have hNames := gamma_named_code_context_names C Ξ hΞ
  have hGeneric : ∀ {p : ℕ} (x : Fin p → SpecialTransformations.Section5.VF (M := M)),
      AlgebraicIndependent (vfParameterField (𝔅).real) x → AlgebraicIndependent (vfParameterField 𝔖) x :=
    fun x hx => gamma_named_code_context_generic C Ξ hΞ hc x hx
  let h := HK.zero_positive_coefficient_lift_degree n p
  let S := F.posCoef hc C Ξ hΞ U
  let TS := S.contraction hc C Ξ hΞ hGenerated
  have hTS := S.contraction_gamma hc C Ξ hΞ hGenerated
  let LS := S.family.appendedFullLift
  have hLS := presentation_appended_full_lift_gamma hc C Ξ hΞ S
  have hLU := rv_volume_lift_gamma hc 𝔇 hBC U.property
  have hW := F.gamma.fullVFObject
  let P := (rvVolumeLift U.val).prod F.family.fullVFObject
  have hP : VFVolumeObjectGamma P 𝔅 := hLU.prod hc hW
  have hPh : VFVolumeObjectGamma (P.reindexDegree h) 𝔅 := hP.reindexDegree h
  obtain ⟨ES,hES,_,_,_⟩ := generated_base_standard_contraction_exists (B := 𝔅) (𝔇).saturated (𝔇).model00
    hreal hGenerated hBC (nativeMixedVolumeDomain hc LS.densityGraph.domain) hLS.densityGraph (Equiv.refl _)
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
    LS (P.reindexDegree h) hLS hPh _ (zero_positive_coefficient_lift_gamma hc 𝔇 hBC F.gamma U.property) ES EPh hES hEPh
  have c3 := GammaNamed.gamma_heq_contraction hc 𝔇 𝔅 hBC hΞ hGenerated hNames hGeneric γ hγ hγ1 h
    (vf_reindex_degree_heq P h) hPh hP EPh EP hEPh hEP
  have c4 := GammaNamed.gamma_prod_contraction hc 𝔇 𝔅 hBC hΞ hGenerated hNames hGeneric γ hγ hγ1
    (rvVolumeLift U.val) F.family.fullVFObject hLU hW hP EU E0 EP hEU hE0 hEP
  have c5 := GammaNamed.gamma_lift_standard_contraction hc 𝔇 𝔅 hBC hΞ hGenerated hNames hGeneric γ hγ hγ1 U EU hEU
  have d := (c4.trans hc (CommonContextVolumeEquivalent.prod hc c5
    (CommonContextVolumeEquivalent.refl hc _))).reindexDegree hc h
  have hAll := ((c1.trans hc c2).trans hc c3).trans hc d
  exact (gammaVolumeBlowupClass_eq_iff hc 𝔇 𝔅).mpr (hAll.descend hc 𝔇 hNames)

end IntegrationInACVF.Section7.GammaFun
