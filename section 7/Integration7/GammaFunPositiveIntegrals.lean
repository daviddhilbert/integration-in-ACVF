import Integration7.GammaFunIntegrationFormula

/-! Gamma-named positive homogeneous function presentations over `⟨C.base, Ξ⟩`
and their integrals in the Gamma-named RV classes. A presentation is a
selected VF volume family coded over the named code context with a Gamma
certificate; its integral is the Gamma-named class of its canonical
contraction object. The value does not depend on the Gamma contraction, and
families whose rows are Gamma blowup equivalent at every VF point have equal
integrals (Gamma Lemma 7.5). -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section9
open SpecialTransformations.Section5 (Point GammaSetDefinable GammaGraphDefinable gammaLogicInput carrier)
open IntegrationInACVF.Section5 IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7.GammaFun
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n a b k : ℕ}

theorem GammaVolumeBlowupEquivalent.of_reindexDegree' (hc : CanonicalStructure.IsCanonical (M := M))
    (C : BaseContext M) (G : Base (M := M)) {p q : ℕ} (h : p = q)
    {U V : GammaVolumeObjects G (C.base : Set M) q}
    (hUV : GammaVolumeBlowupEquivalent G (C.base : Set M) p (U.reindexDegree h) (V.reindexDegree h)) :
    GammaVolumeBlowupEquivalent G (C.base : Set M) q U V := by
  cases h
  have hU := gamma_volume_iso_of_label_identity hc (volumeCastReindexIso hc C U.val rfl)
    (U.property.reindexDegree rfl) rfl (fun _ => rfl)
  have hV := gamma_volume_iso_of_label_identity hc (volumeCastReindexIso hc C V.val rfl)
    (V.property.reindexDegree rfl) rfl (fun _ => rfl)
  exact ((GammaVolumeBlowupEquivalent.of_iso C G _ (hU.symm hc C G)).trans hc C G hUV).trans hc C G
    (GammaVolumeBlowupEquivalent.of_iso C G _ hV)

variable (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
variable (Ξ : Set (Values.Gamma (M := M))) (hΞ : Cardinal.mk Ξ < C.κ)
variable (hGenerated : VFGammaGeneratedBase (gammaNamedBase C Ξ))

set_option quotPrecheck false
local notation "𝔅" => gammaNamedBase C Ξ
local notation "𝔇" => gammaNamedCodeContext C Ξ hΞ
local notation "𝔖" => ((gammaNamedCodeContext C Ξ hΞ).base : Set M)

/-- A Gamma-named presentation of a positive homogeneous function on `VF^(n+1)`
with coefficient degree `k+1`. -/
structure Presentation (n k : ℕ) where
  arity : ℕ
  family : SelectedVFVolumeFamily (gammaNamedCodeContext C Ξ hΞ) (n+1) arity k
  gamma : family.Gamma (gammaNamedBase C Ξ)

include hGenerated in
theorem presentation_contraction_exists (F : Presentation C Ξ hΞ n k) :
    ∃ T : StandardContraction (nativeMixedVolumeDomain hc F.family.densityGraph.domain) (Equiv.refl _),
      GammaProgramDefinable 𝔅 T.program := by
  obtain ⟨T,hT,_⟩ := generated_base_standard_contraction_exists (B := 𝔅) (𝔇).saturated (𝔇).model00
    ((Cardinal.mk_le_mk_of_subset (gamma_named_code_context_base C Ξ hΞ)).trans_lt (𝔇).small) hGenerated
    (gamma_named_code_context_base C Ξ hΞ) _ (F.gamma.native_domain hc) (Equiv.refl _)
  exact ⟨T,hT⟩

/-- The chosen Gamma contraction of a presentation. -/
def Presentation.contraction (F : Presentation C Ξ hΞ n k) :
    StandardContraction (nativeMixedVolumeDomain hc F.family.densityGraph.domain) (Equiv.refl _) :=
  Classical.choose (presentation_contraction_exists hc C Ξ hΞ hGenerated F)

theorem Presentation.contraction_gamma (F : Presentation C Ξ hΞ n k) :
    GammaProgramDefinable 𝔅 (F.contraction hc C Ξ hΞ hGenerated).program :=
  Classical.choose_spec (presentation_contraction_exists hc C Ξ hΞ hGenerated F)

/-- The Gamma canonical contraction object of a presentation for a Gamma contraction. -/
def Presentation.integralObject (F : Presentation C Ξ hΞ n k)
    (T : StandardContraction (nativeMixedVolumeDomain hc F.family.densityGraph.domain) (Equiv.refl _))
    (hT : GammaProgramDefinable 𝔅 T.program) : GammaVolumeObjects 𝔅 𝔖 ((k+1)+n) :=
  ⟨F.family.canonicalIntegralObject hc Ξ T,
    GammaNamed.selected_standard_volume_object_gamma hc 𝔇 Ξ 𝔅 _ _ _ _ _ T hT⟩

/-- **The Gamma-named integral of a presentation.** -/
def Presentation.integral (F : Presentation C Ξ hΞ n k) : HK.GammaNamedRVClasses hc C Ξ hΞ (((k+1)+n)+1) :=
  gammaVolumeBlowupClass hc 𝔇 𝔅
    (F.integralObject hc C Ξ hΞ (F.contraction hc C Ξ hΞ hGenerated) (F.contraction_gamma hc C Ξ hΞ hGenerated))

variable (γ : Values.Gamma (M := M)) (hγ : γ ∈ Ξ) (hγ1 : 1 < γ)

include hγ hγ1 in
/-- The integral object does not depend on the Gamma contraction. -/
theorem presentation_integral_object_independent (F : Presentation C Ξ hΞ n k)
    (T E : StandardContraction (nativeMixedVolumeDomain hc F.family.densityGraph.domain) (Equiv.refl _))
    (hT : GammaProgramDefinable 𝔅 T.program) (hE : GammaProgramDefinable 𝔅 E.program) :
    gammaVolumeBlowupClass hc 𝔇 𝔅 (F.integralObject hc C Ξ hΞ T hT) =
      gammaVolumeBlowupClass hc 𝔇 𝔅 (F.integralObject hc C Ξ hΞ E hE) := by
  apply (gammaVolumeBlowupClass_eq_iff hc 𝔇 𝔅).mpr
  exact (GammaNamed.selected_same_order_standard_volume_comparison hc 𝔇 𝔅 (gamma_named_code_context_base C Ξ hΞ)
    hΞ (fun x hx => gamma_named_code_context_generic C Ξ hΞ hc x hx) γ hγ hγ1 _ (F.gamma.native_domain hc)
    _ _ _ _ T E hT hE).descend hc 𝔇 (gamma_named_code_context_names C Ξ hΞ)

include hγ hγ1 in
theorem presentation_integral_eq (F : Presentation C Ξ hΞ n k)
    (T : StandardContraction (nativeMixedVolumeDomain hc F.family.densityGraph.domain) (Equiv.refl _))
    (hT : GammaProgramDefinable 𝔅 T.program) :
    F.integral hc C Ξ hΞ hGenerated = gammaVolumeBlowupClass hc 𝔇 𝔅 (F.integralObject hc C Ξ hΞ T hT) :=
  presentation_integral_object_independent hc C Ξ hΞ γ hγ hγ1 F _ _ _ _

/-- Gamma row equivalence of two presentations at a VF point. -/
def RowsEquivalent (F H : Presentation C Ξ hΞ n k) (x : Fin (n+1) → VFType (M := M)) : Prop :=
  GammaRowsEquivalent hc 𝔇 𝔅 F.gamma H.gamma x

set_option maxHeartbeats 2400000 in
include hγ hγ1 in
/-- **Gamma Lemma 7.5 on integrals.** -/
theorem presentation_integral_eq_of_rows (F H : Presentation C Ξ hΞ n k)
    (hRows : ∀ x, RowsEquivalent hc C Ξ hΞ F H x) :
    F.integral hc C Ξ hΞ hGenerated = H.integral hc C Ξ hΞ hGenerated := by
  let T := F.contraction hc C Ξ hΞ hGenerated
  let E := H.contraction hc C Ξ hΞ hGenerated
  have hT := F.contraction_gamma hc C Ξ hΞ hGenerated
  have hE := H.contraction_gamma hc C Ξ hΞ hGenerated
  have hCommon := gamma_family_lemma_7_5 hc 𝔇 𝔅 (gamma_named_code_context_base C Ξ hΞ) hΞ γ hγ hγ1
    F.gamma H.gamma hRows T E hT hE
  have hOld := hCommon.descend hc 𝔇 (gamma_named_code_context_names C Ξ hΞ)
  let A := nativeMixedVolumeDomain hc F.family.densityGraph.domain
  let B := nativeMixedVolumeDomain hc H.family.densityGraph.domain
  have hA : GammaSetDefinable 𝔅 (carrier A) := F.gamma.native_domain hc
  have hB : GammaSetDefinable 𝔅 (carrier B) := H.gamma.native_domain hc
  let U' : GammaVolumeObjects 𝔅 𝔖 ((k+1)+n) := F.integralObject hc C Ξ hΞ T hT
  let V' : GammaVolumeObjects 𝔅 𝔖 ((k+1)+n) := H.integralObject hc C Ξ hΞ E hE
  have hU0 := standard_append_volume_object_gamma_of hc 𝔇 Ξ 𝔅 A F.family.densityGraph.selected (Fin.last F.arity)
    (fun p hp => F.family.densityGraph_label_nonzero p hp) F.family.densityGraph.finite_selected T hT
  have hNew := hOld.of_permuted_coordinate_charts hc 𝔇 (U' := U'.reindexDegree (selected_append_degree_eq n k))
    (V' := V'.reindexDegree (selected_append_degree_eq n k)) (appendedToOriginalVolumePermutation (n+1) k)
    (selectedIntegralCoordinateChart hc 𝔇 Ξ A F.family.densityGraph.selected (Fin.last F.arity)
      F.family.densityGraph_label_nonzero F.family.densityGraph.finite_selected T)
    (selectedIntegralCoordinateChart hc 𝔇 Ξ B H.family.densityGraph.selected (Fin.last H.arity)
      H.family.densityGraph_label_nonzero H.family.densityGraph.finite_selected E)
    (gamma_rv_coordinate_map hc _ id hU0.domain_graph (fun _ => rfl))
    (gamma_rv_coordinate_map hc _ id (standard_append_volume_object_gamma_of hc 𝔇 Ξ 𝔅 B
      H.family.densityGraph.selected (Fin.last H.arity)
      (fun p hp => H.family.densityGraph_label_nonzero p hp) H.family.densityGraph.finite_selected E hE).domain_graph
      (fun _ => rfl))
    (selected_integral_coordinate_chart_coordinates hc 𝔇 Ξ A F.family.densityGraph.selected (Fin.last F.arity)
      F.family.densityGraph_label_nonzero F.family.densityGraph.finite_selected T)
    (selected_integral_coordinate_chart_coordinates hc 𝔇 Ξ B H.family.densityGraph.selected (Fin.last H.arity)
      H.family.densityGraph_label_nonzero H.family.densityGraph.finite_selected E)
    (selected_integral_coordinate_chart_density hc 𝔇 Ξ A F.family.densityGraph.selected (Fin.last F.arity)
      F.family.densityGraph_label_nonzero F.family.densityGraph.finite_selected T)
    (selected_integral_coordinate_chart_density hc 𝔇 Ξ B H.family.densityGraph.selected (Fin.last H.arity)
      H.family.densityGraph_label_nonzero H.family.densityGraph.finite_selected E)
  exact (gammaVolumeBlowupClass_eq_iff hc 𝔇 𝔅).mpr
    (GammaVolumeBlowupEquivalent.of_reindexDegree' hc 𝔇 𝔅 (selected_append_degree_eq n k) hNew)

end IntegrationInACVF.Section7.GammaFun
