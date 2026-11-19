import Integration7.GammaFunZeroCoefLinearity
import Integration7.HKZeroScalarRealizations

/-! **The graded Gamma-named integral is linear.** On every graded component the Gamma-named
integral satisfies `∫(a • f) = a * ∫f` in `HK.GammaNamedRVSemiring`, for coefficients and
functions of every degree (positive or weighted degree zero). Hence the graded integral is an
`HK.GammaNamedRVSemiring`-linear map on the graded Gamma-named function module. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section9
open SpecialTransformations.Section5 (Point GammaSetDefinable GammaGraphDefinable gammaLogicInput carrier VF RV)
open IntegrationInACVF.Section5 IntegrationInACVF.Section6
open scoped DirectSum

namespace IntegrationInACVF.Section7.GammaFun
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n k p : ℕ}
variable (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
variable (Ξ : Set (Values.Gamma (M := M))) (hΞ : Cardinal.mk Ξ < C.κ)
variable (hGenerated : VFGammaGeneratedBase (gammaNamedBase C Ξ))

set_option quotPrecheck false
local notation "𝔅" => gammaNamedBase C Ξ
local notation "𝔇" => gammaNamedCodeContext C Ξ hΞ
local notation "𝔖" => ((gammaNamedCodeContext C Ξ hΞ).base : Set M)

/-- The product of a degree-zero and a positive Gamma-named class is the positive-zero product. -/
theorem named_zero_pos_product_heq {d : ℕ} (Z : HK.GammaZeroRVObjects 𝔅 𝔖) (V : GammaVolumeObjects 𝔅 𝔖 d) :
    HEq (HK.gammaNamedRVClass hc C Ξ hΞ (n := 0+(d+1))
        (HK.GammaRVObjects.product hc (⟨Z.val,(HK.RVVolumeObject.Gamma.zero_iff _).mpr Z.property⟩ : HK.GammaRVObjects 𝔅 𝔖 0)
          (⟨V.val,(HK.RVVolumeObject.Gamma.positive_iff _).mpr V.property⟩ : HK.GammaRVObjects 𝔅 𝔖 (d+1))))
      (gammaVolumeBlowupClass hc 𝔇 𝔅 (V.posZeroProd hc Z)) := by
  have hZP := HK.RVVolumeObject.Gamma.product (n := 0) (m := d+1) hc ((HK.RVVolumeObject.Gamma.zero_iff _).mpr Z.property)
    ((HK.RVVolumeObject.Gamma.positive_iff _).mpr V.property)
  have e3 : gammaVolumeBlowupClass hc 𝔇 𝔅 ((V.zeroProd hc Z).reindexDegree (Nat.zero_add d)) =
      gammaVolumeBlowupClass hc 𝔇 𝔅 ⟨HK.product 𝔖 0 (d+1) Z.val V.val,(HK.RVVolumeObject.Gamma.positive_iff _).mp hZP⟩ :=
    (gammaVolumeBlowupClass_eq_iff hc 𝔇 𝔅).mpr (GammaVolumeBlowupEquivalent.of_iso 𝔇 𝔅
      ((HK.productZeroPositiveIso hc 𝔇 Z.val V.val).symm hc 𝔇)
      ((gamma_volume_iso_of_label_identity hc (HK.productZeroPositiveIso hc 𝔇 Z.val V.val)
        ((HK.RVVolumeObject.Gamma.positive_iff _).mp hZP) rfl (fun _ => rfl)).symm hc 𝔇 𝔅))
  have e2 : gammaVolumeBlowupClass hc 𝔇 𝔅 (V.posZeroProd hc Z) = gammaVolumeBlowupClass hc 𝔇 𝔅 (V.zeroProd hc Z) :=
    (gammaVolumeBlowupClass_eq_iff hc 𝔇 𝔅).mpr (GammaVolumeBlowupEquivalent.of_iso 𝔇 𝔅
      (U := V.posZeroProd hc Z) (V := V.zeroProd hc Z)
      (HK.mixedProductSwapIso hc 𝔇 V.val Z.val) (gamma_mixed_product_swap_iso hc 𝔇 V.property Z.property))
  refine (heq_of_eq e3.symm).trans ?_
  exact (gamma_class_reindex_heq hc 𝔇 𝔅 (Nat.zero_add d) _).trans (heq_of_eq e2.symm)

variable (γ : Values.Gamma (M := M)) (hγ : γ ∈ Ξ) (hγ1 : 1 < γ)

include hγ hγ1 in
theorem zero_presentation_integral_contraction (F : ZeroPresentation C Ξ hΞ n) {σ : Equiv.Perm (Fin (n+1))}
    (E0 : StandardContraction (nativeMixedVolumeDomain hc F.family.fullVFObject.densityGraph.domain) σ)
    (hE0 : GammaProgramDefinable 𝔅 E0.program) :
    F.integral hc C Ξ hΞ hGenerated γ hγ hγ1 =
      gammaVolumeBlowupClass hc 𝔇 𝔅 ⟨F.family.fullVFObject.standardContractionObject hc 𝔇 (𝔅).gamma E0,
        GammaNamed.standard_contraction_object_gamma hc 𝔇 𝔅 (gamma_named_code_context_base C Ξ hΞ) _
          F.gamma.fullVFObject E0 hE0⟩ :=
  gamma_named_integration_equiv_contraction hc C Ξ hΞ hGenerated γ hγ hγ1 ⟨_,F.gamma.fullVFObject⟩ E0 hE0

set_option maxHeartbeats 3200000 in
include hγ hγ1 in
/-- **Weighted degree-zero coefficient linearity on degree-zero presentations.** -/
theorem zero_presentation_zero_coef_integral (Z : HK.GammaZeroRVObjects 𝔅 𝔖) (F : ZeroPresentation C Ξ hΞ n)
    {σ : Equiv.Perm (Fin (n+1))}
    (E0 : StandardContraction (nativeMixedVolumeDomain hc F.family.fullVFObject.densityGraph.domain) σ)
    (hE0 : GammaProgramDefinable 𝔅 E0.program) :
    (F.zeroCoef hc C Ξ hΞ Z).integral hc C Ξ hΞ hGenerated γ hγ hγ1 =
      gammaVolumeBlowupClass hc 𝔇 𝔅 (GammaVolumeObjects.posZeroProd hc (⟨F.family.fullVFObject.standardContractionObject
        hc 𝔇 (𝔅).gamma E0,GammaNamed.standard_contraction_object_gamma hc 𝔇 𝔅 (gamma_named_code_context_base C Ξ hΞ) _
          F.gamma.fullVFObject E0 hE0⟩ : GammaVolumeObjects 𝔅 𝔖 n) Z) := by
  have hBC := gamma_named_code_context_base C Ξ hΞ
  have hreal := small_gamma_named_real C Ξ hΞ
  have hNames := gamma_named_code_context_names C Ξ hΞ
  have hGeneric : ∀ {p : ℕ} (x : Fin p → SpecialTransformations.Section5.VF (M := M)),
      AlgebraicIndependent (vfParameterField (𝔅).real) x → AlgebraicIndependent (vfParameterField 𝔖) x :=
    fun x hx => gamma_named_code_context_generic C Ξ hΞ hc x hx
  let S := F.zeroCoef hc C Ξ hΞ Z
  let XS := S.family.fullVFObject
  let XF := F.family.fullVFObject
  have hXS := S.gamma.fullVFObject
  have hXF := F.gamma.fullVFObject
  have hXZ : VFVolumeObjectGamma (HK.positiveVFZeroProduct XF Z.val) 𝔅 := hXF.weightedZero hc Z.property
  obtain ⟨ES,hES,_,_,_⟩ := generated_base_standard_contraction_exists (B := 𝔅) (𝔇).saturated (𝔇).model00
    hreal hGenerated hBC (nativeMixedVolumeDomain hc XS.densityGraph.domain) hXS.densityGraph (Equiv.refl _)
  obtain ⟨EZ,hEZ,_,_,_⟩ := generated_base_standard_contraction_exists (B := 𝔅) (𝔇).saturated (𝔇).model00
    hreal hGenerated hBC (nativeMixedVolumeDomain hc (HK.positiveVFZeroProduct XF Z.val).densityGraph.domain)
    hXZ.densityGraph (Equiv.refl _)
  have hIso : (VFVolumeIso.of_bijection (HK.zeroVolumeScalarRealizationBijection hc F.family Z.val)).GammaDefinable 𝔅 :=
    ⟨hXS.domain,hXZ.domain,vf_identity_map_gamma _ (fun _ => rfl) hXS.domain⟩
  rw [zero_presentation_integral_contraction hc C Ξ hΞ hGenerated γ hγ hγ1 S ES hES]
  have a2 := GammaNamed.gamma_vf_iso_contraction_comparison hc 𝔇 𝔅 hBC hΞ hGenerated hNames hGeneric γ hγ hγ1
    XS _ hXS hXZ _ hIso ES EZ hES hEZ
  have a3 := GammaNamed.gamma_weighted_zero_contraction hc 𝔇 𝔅 hBC hΞ hGenerated hNames hGeneric γ hγ hγ1
    XF hXF Z hXZ E0 EZ hE0 hEZ
  exact (gammaVolumeBlowupClass_eq_iff hc 𝔇 𝔅).mpr ((a2.trans hc a3).descend hc 𝔇 hNames)

theorem presentation_reindex_appended_heq {k k' : ℕ} (h : k = k') (F : Presentation C Ξ hΞ n k) :
    HEq ((F.reindex C Ξ hΞ h).appendedIntegral hc C Ξ hΞ hGenerated) (F.appendedIntegral hc C Ξ hΞ hGenerated) := by
  subst h
  rfl

/-! ### The component integrals and their coefficient linearity -/

/-- The Gamma-named integral of a graded component, in the Gamma-named RV semiring. -/
def compIntegral (n : ℕ) : (j : ℕ) → AEComp hc C Ξ hΞ n j →+ HK.GammaNamedRVSemiring hc C Ξ hΞ
  | 0 => gammaSemiringZeroIntegralAddHom hc C Ξ hΞ hGenerated γ hγ hγ1 n
  | k+1 => gammaSemiringIntegralAddHom hc C Ξ hΞ hGenerated γ hγ hγ1 n k

set_option maxHeartbeats 3200000 in
include hγ hγ1 in
/-- **Coefficient linearity of the component integrals.** -/
theorem comp_integral_act {i j : ℕ} (a : HK.GammaNamedRVClasses hc C Ξ hΞ i) (f : AEComp hc C Ξ hΞ n j) :
    compIntegral hc C Ξ hΞ hGenerated γ hγ hγ1 n (i+j) (aeAct hc C Ξ hΞ a f) =
      DirectSum.of (HK.GammaNamedRVClasses hc C Ξ hΞ) i a * compIntegral hc C Ξ hΞ hGenerated γ hγ hγ1 n j f := by
  obtain ⟨u,rfl⟩ := HK.gammaNamedRVClass_surjective hc C Ξ hΞ i a
  rw [← aeMk_rep hc C Ξ hΞ f,aeAct_mk]
  have hBC := gamma_named_code_context_base C Ξ hΞ
  have hreal := small_gamma_named_real C Ξ hΞ
  cases i with
  | zero =>
    let Z : HK.GammaZeroRVObjects 𝔅 𝔖 := ⟨u.val,(HK.RVVolumeObject.Gamma.zero_iff _).mp u.property⟩
    cases j with
    | zero =>
      let F : ZeroPresentation C Ξ hΞ n := aeRep hc C Ξ hΞ f
      obtain ⟨E0,hE0,_,_,_⟩ := generated_base_standard_contraction_exists (B := 𝔅) (𝔇).saturated (𝔇).model00
        hreal hGenerated hBC (nativeMixedVolumeDomain hc F.family.fullVFObject.densityGraph.domain)
        F.gamma.fullVFObject.densityGraph (Equiv.refl _)
      change DirectSum.of (HK.GammaNamedRVClasses hc C Ξ hΞ) (n+1) ((F.zeroCoef hc C Ξ hΞ Z).integral hc C Ξ hΞ hGenerated γ hγ hγ1) =
        DirectSum.of (HK.GammaNamedRVClasses hc C Ξ hΞ) 0 (HK.gammaNamedRVClass hc C Ξ hΞ u) *
          DirectSum.of (HK.GammaNamedRVClasses hc C Ξ hΞ) (n+1) (F.integral hc C Ξ hΞ hGenerated γ hγ hγ1)
      rw [DirectSum.of_mul_of,zero_presentation_zero_coef_integral hc C Ξ hΞ hGenerated γ hγ hγ1 Z F E0 hE0,
        zero_presentation_integral_contraction hc C Ξ hΞ hGenerated γ hγ hγ1 F E0 hE0]
      apply gamma_semiring_of_heq hc C Ξ hΞ (Nat.zero_add n).symm
      change _ ≍ HK.gammaNamedRVMul hc C Ξ hΞ (HK.gammaNamedRVClass hc C Ξ hΞ u)
        (HK.gammaNamedRVClass hc C Ξ hΞ (n := n+1) ⟨_,(HK.RVVolumeObject.Gamma.positive_iff _).mpr
          (GammaNamed.standard_contraction_object_gamma hc 𝔇 𝔅 hBC _ F.gamma.fullVFObject E0 hE0)⟩)
      rw [HK.gammaNamedRVMul_class]
      exact (named_zero_pos_product_heq hc C Ξ hΞ Z _).symm
    | succ k =>
      let F : Presentation C Ξ hΞ n k := aeRep hc C Ξ hΞ f
      change DirectSum.of (HK.GammaNamedRVClasses hc C Ξ hΞ) (appendVolumeDegree (n+1) (0+k) + 1)
          (((F.zeroCoef hc C Ξ hΞ Z).reindex C Ξ hΞ (Nat.zero_add k).symm).appendedIntegral hc C Ξ hΞ hGenerated) =
        DirectSum.of (HK.GammaNamedRVClasses hc C Ξ hΞ) 0 (HK.gammaNamedRVClass hc C Ξ hΞ u) *
          DirectSum.of (HK.GammaNamedRVClasses hc C Ξ hΞ) (appendVolumeDegree (n+1) k + 1)
            (F.appendedIntegral hc C Ξ hΞ hGenerated)
      rw [DirectSum.of_mul_of]
      have hd : appendVolumeDegree (n+1) (0+k) = 0 + appendVolumeDegree (n+1) k := by
        rw [Nat.zero_add,Nat.zero_add]
      apply gamma_semiring_of_heq hc C Ξ hΞ hd
      refine (presentation_reindex_appended_heq hc C Ξ hΞ hGenerated (Nat.zero_add k).symm _).trans ?_
      rw [presentation_zero_coef_appended_integral hc C Ξ hΞ hGenerated γ hγ hγ1 Z F]
      let V := F.appendedObject hc C Ξ hΞ (F.contraction hc C Ξ hΞ hGenerated) (F.contraction_gamma hc C Ξ hΞ hGenerated)
      change _ ≍ HK.gammaNamedRVMul hc C Ξ hΞ (HK.gammaNamedRVClass hc C Ξ hΞ u)
        (HK.gammaNamedRVClass hc C Ξ hΞ (n := appendVolumeDegree (n+1) k + 1)
          ⟨V.val,(HK.RVVolumeObject.Gamma.positive_iff _).mpr V.property⟩)
      rw [HK.gammaNamedRVMul_class]
      exact (named_zero_pos_product_heq hc C Ξ hΞ Z V).symm
  | succ p =>
    let U : GammaVolumeObjects 𝔅 𝔖 p := ⟨u.val,(HK.RVVolumeObject.Gamma.positive_iff _).mp u.property⟩
    cases j with
    | zero =>
      let F : ZeroPresentation C Ξ hΞ n := aeRep hc C Ξ hΞ f
      obtain ⟨E0,hE0,_,_,_⟩ := generated_base_standard_contraction_exists (B := 𝔅) (𝔇).saturated (𝔇).model00
        hreal hGenerated hBC (nativeMixedVolumeDomain hc F.family.fullVFObject.densityGraph.domain)
        F.gamma.fullVFObject.densityGraph (Equiv.refl _)
      change DirectSum.of (HK.GammaNamedRVClasses hc C Ξ hΞ) (appendVolumeDegree (n+1) p + 1)
          ((F.posCoef hc C Ξ hΞ U).appendedIntegral hc C Ξ hΞ hGenerated) =
        DirectSum.of (HK.GammaNamedRVClasses hc C Ξ hΞ) (p+1) (HK.gammaNamedRVClass hc C Ξ hΞ u) *
          DirectSum.of (HK.GammaNamedRVClasses hc C Ξ hΞ) (n+1) (F.integral hc C Ξ hΞ hGenerated γ hγ hγ1)
      rw [DirectSum.of_mul_of,zero_presentation_pos_coef_appended_integral hc C Ξ hΞ hGenerated γ hγ hγ1 U F E0 hE0,
        zero_presentation_integral_contraction hc C Ξ hΞ hGenerated γ hγ hγ1 F E0 hE0]
      apply gamma_semiring_of_heq hc C Ξ hΞ (HK.zero_positive_coefficient_lift_degree n p)
      refine (gamma_class_reindex_heq hc 𝔇 𝔅 _ _).trans (heq_of_eq ?_)
      change _ = HK.gammaNamedRVMul hc C Ξ hΞ (HK.gammaNamedRVClass hc C Ξ hΞ (n := p+1) u)
        (HK.gammaNamedRVClass hc C Ξ hΞ (n := n+1) ⟨_,(HK.RVVolumeObject.Gamma.positive_iff _).mpr
          (GammaNamed.standard_contraction_object_gamma hc 𝔇 𝔅 hBC _ F.gamma.fullVFObject E0 hE0)⟩)
      rw [HK.gammaNamedRVMul_class]
      rfl
    | succ k =>
      exact gamma_semiring_integral_positive_coefficient hc C Ξ hΞ hGenerated γ hγ hγ1
        (gammaVolumeBlowupClass hc 𝔇 𝔅 U) (Quotient.mk _ (aeRep hc C Ξ hΞ f))

/-! ### The graded integral -/

/-- **The graded Gamma-named integral.** -/
def gradedIntegralAddHom (n : ℕ) : GradedAEFunction hc C Ξ hΞ n →+ HK.GammaNamedRVSemiring hc C Ξ hΞ :=
  DirectSum.toAddMonoid (compIntegral hc C Ξ hΞ hGenerated γ hγ hγ1 n)

theorem graded_integral_of {j : ℕ} (f : AEComp hc C Ξ hΞ n j) :
    gradedIntegralAddHom hc C Ξ hΞ hGenerated γ hγ hγ1 n (DirectSum.of (AEComp hc C Ξ hΞ n) j f) =
      compIntegral hc C Ξ hΞ hGenerated γ hγ hγ1 n j f :=
  DirectSum.toAddMonoid_of _ j f

include hγ hγ1 in
theorem graded_integral_smul (r : HK.GammaNamedRVSemiring hc C Ξ hΞ) (f : GradedAEFunction hc C Ξ hΞ n) :
    gradedIntegralAddHom hc C Ξ hΞ hGenerated γ hγ hγ1 n (r • f) =
      r * gradedIntegralAddHom hc C Ξ hΞ hGenerated γ hγ hγ1 n f := by
  let I := gradedIntegralAddHom hc C Ξ hΞ hGenerated γ hγ hγ1 n
  induction r using DirectSum.induction_on with
  | zero => simp only [zero_smul,map_zero,zero_mul]
  | of i a =>
    induction f using DirectSum.induction_on with
    | zero => simp only [smul_zero,map_zero,mul_zero]
    | of j f =>
      rw [graded_ae_action_of,graded_integral_of,graded_integral_of]
      exact comp_integral_act hc C Ξ hΞ hGenerated γ hγ hγ1 a f
    | add f g hf hg =>
      change I (DirectSum.of (HK.GammaNamedRVClasses hc C Ξ hΞ) i a • (f+g)) =
        DirectSum.of (HK.GammaNamedRVClasses hc C Ξ hΞ) i a * I (f+g)
      rw [smul_add,map_add,map_add,mul_add]
      exact congrArg₂ (·+·) hf hg
  | add r s hr hs =>
    change I ((r+s) • f) = (r+s) * I f
    rw [add_smul,map_add,add_mul]
    exact congrArg₂ (·+·) hr hs

/-- **The graded Gamma-named integral as a linear map over `HK.GammaNamedRVSemiring`.** -/
def gradedIntegralLinearMap (n : ℕ) :
    GradedAEFunction hc C Ξ hΞ n →ₗ[HK.GammaNamedRVSemiring hc C Ξ hΞ] HK.GammaNamedRVSemiring hc C Ξ hΞ where
  toAddHom := (gradedIntegralAddHom hc C Ξ hΞ hGenerated γ hγ hγ1 n).toAddHom
  map_smul' r f := graded_integral_smul hc C Ξ hΞ hGenerated γ hγ hγ1 r f

end IntegrationInACVF.Section7.GammaFun
