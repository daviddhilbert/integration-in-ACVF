import Integration7.GammaVFPermutationCovariance
import Integration7.AppendedFamilyFullLifts
import Integration7.VFVolumeDegreeReindexing

/-! **Gamma appended full-lift formula.** The appended-convention Gamma object of a Gamma-named
presentation is common-context equivalent to every Gamma standard contraction of the appended
full VF lift of its family. The proof composes the Gamma permutation covariance with the Gamma
realization comparison; degree casts are handled by explicit transport lemmas. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section9
open SpecialTransformations.Section5 (Point GammaSetDefinable GammaGraphDefinable gammaLogicInput carrier VF RV)
open IntegrationInACVF.Section5 IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {G : Base (M := M)} {S : Set M}

theorem VFVolumeObjectGamma.reindexDegree {a b : ℕ} {U : PositiveVFVolumeObject (M := M) S b}
    (hU : VFVolumeObjectGamma U G) (h : a = b) : VFVolumeObjectGamma (U.reindexDegree h) G := by
  cases h
  exact hU

theorem VFVolumeObjectGamma.of_heq {p q : ℕ} (h : p = q) {X : PositiveVFVolumeObject (M := M) S p}
    {Y : PositiveVFVolumeObject (M := M) S q} (hXY : HEq X Y) (hY : VFVolumeObjectGamma Y G) :
    VFVolumeObjectGamma X G := by
  subst h
  obtain rfl := eq_of_heq hXY
  exact hY

theorem vf_reindex_degree_heq {a b : ℕ} (U : PositiveVFVolumeObject (M := M) S b) (h : a = b) :
    HEq (U.reindexDegree h) U := by
  cases h
  rfl

variable (hc : CanonicalStructure.IsCanonical (M := M)) {C : BaseContext M}

include hc in
theorem CommonContextVolumeEquivalent.reindex_rfl {b : ℕ} (P : GammaVolumeObjects G (C.base : Set M) b) :
    CommonContextVolumeEquivalent G C (P.reindexDegree rfl) P :=
  CommonContextVolumeEquivalent.of_iso (volumeCastReindexIso hc C P.val rfl)
    (gamma_volume_iso_of_label_identity hc (volumeCastReindexIso hc C P.val rfl) (P.property.reindexDegree rfl) rfl
      (fun _ => rfl))

include hc in
theorem CommonContextVolumeEquivalent.reindex_trans {a b c : ℕ} (P : GammaVolumeObjects G (C.base : Set M) c)
    (h₁ : a = b) (h₂ : b = c) :
    CommonContextVolumeEquivalent G C ((P.reindexDegree h₂).reindexDegree h₁) (P.reindexDegree (h₁.trans h₂)) := by
  subst h₁ h₂
  exact ((CommonContextVolumeEquivalent.reindex_rfl hc _).trans hc (CommonContextVolumeEquivalent.reindex_rfl hc _)).trans hc
    ((CommonContextVolumeEquivalent.reindex_rfl hc P).symm hc)

theorem GammaVolumeBlowupEquivalent.toCommon {b : ℕ} {U V : GammaVolumeObjects G (C.base : Set M) b}
    (h : GammaVolumeBlowupEquivalent G (C.base : Set M) b U V) : CommonContextVolumeEquivalent G C U V :=
  ⟨C,Set.Subset.refl _,h.extend (Set.Subset.refl _)⟩

end IntegrationInACVF.Section7

namespace IntegrationInACVF.Section7.GammaNamed
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

set_option maxHeartbeats 3200000 in
/-- Gamma standard contractions of heterogeneously equal VF objects agree up to the degree cast. -/
theorem gamma_heq_contraction (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (G : Base (M := M)) (hGC : G.real ⊆ (C.base : Set M)) (hΞ : Cardinal.mk G.gamma < C.κ)
    (hGenerated : VFGammaGeneratedBase G) (hNames : commonRealNames G ⊆ (C.base : Set M))
    (hGeneric : ∀ {p : ℕ} (x : Fin p → VF (M := M)), AlgebraicIndependent (vfParameterField G.real) x →
      AlgebraicIndependent (vfParameterField (C.base : Set M)) x)
    (γ : Values.Gamma (M := M)) (hγ : γ ∈ G.gamma) (hγ1 : 1 < γ)
    {p q : ℕ} (h : p = q) {X : PositiveVFVolumeObject (M := M) (C.base : Set M) p}
    {Y : PositiveVFVolumeObject (M := M) (C.base : Set M) q} (hXY : HEq X Y)
    (hX : VFVolumeObjectGamma X G) (hY : VFVolumeObjectGamma Y G) {σ : Equiv.Perm (Fin (p+1))}
    {υ : Equiv.Perm (Fin (q+1))}
    (E : StandardContraction (nativeMixedVolumeDomain hc X.densityGraph.domain) σ)
    (E' : StandardContraction (nativeMixedVolumeDomain hc Y.densityGraph.domain) υ)
    (hE : GammaProgramDefinable G E.program) (hE' : GammaProgramDefinable G E'.program) :
    CommonContextVolumeEquivalent G C
      ⟨X.standardContractionObject hc C G.gamma E,standard_contraction_object_gamma hc C G hGC _ hX E hE⟩
      (GammaVolumeObjects.reindexDegree
        ⟨Y.standardContractionObject hc C G.gamma E',standard_contraction_object_gamma hc C G hGC _ hY E' hE'⟩ h) := by
  subst h
  obtain rfl := eq_of_heq hXY
  exact (gamma_vf_iso_contraction_comparison hc C G hGC hΞ hGenerated hNames hGeneric γ hγ hγ1 X X hX hY
    (VFVolumeIso.refl hc C X) (hX.refl_iso hc C) E E' hE hE').trans hc
      ((CommonContextVolumeEquivalent.reindex_rfl hc _).symm hc)

end IntegrationInACVF.Section7.GammaNamed

namespace IntegrationInACVF.Section7.GammaFun
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n k : ℕ}
variable (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
variable (Ξ : Set (Values.Gamma (M := M))) (hΞ : Cardinal.mk Ξ < C.κ)
variable (hGenerated : VFGammaGeneratedBase (gammaNamedBase C Ξ))

set_option quotPrecheck false
local notation "𝔅" => gammaNamedBase C Ξ
local notation "𝔇" => gammaNamedCodeContext C Ξ hΞ
local notation "𝔖" => ((gammaNamedCodeContext C Ξ hΞ).base : Set M)

include hc in
theorem presentation_appended_full_lift_gamma (F : Presentation C Ξ hΞ n k) :
    VFVolumeObjectGamma F.family.appendedFullLift 𝔅 :=
  ((F.gamma.fullLift hc).reindexDegree (appended_family_lift_degree_eq (n+1) k)).permuteVF hc 𝔇
    (appendedToOriginalVolumePermutation (n+1) k).symm

variable (γ : Values.Gamma (M := M)) (hγ : γ ∈ Ξ) (hγ1 : 1 < γ)

set_option maxHeartbeats 6400000 in
include hGenerated hγ hγ1 in
/-- **Gamma appended full-lift formula.** -/
theorem presentation_appended_full_lift (F : Presentation C Ξ hΞ n k)
    (T : StandardContraction (nativeMixedVolumeDomain hc F.family.densityGraph.domain) (Equiv.refl _))
    (hT : GammaProgramDefinable 𝔅 T.program) {υ : Equiv.Perm (Fin (appendVolumeDegree (n+1) k + 1))}
    (E : StandardContraction (nativeMixedVolumeDomain hc F.family.appendedFullLift.densityGraph.domain) υ)
    (hE : GammaProgramDefinable 𝔅 E.program) :
    CommonContextVolumeEquivalent 𝔅 𝔇 (F.appendedObject hc C Ξ hΞ T hT)
      ⟨F.family.appendedFullLift.standardContractionObject hc 𝔇 (𝔅).gamma E,
        GammaNamed.standard_contraction_object_gamma hc 𝔇 𝔅 (gamma_named_code_context_base C Ξ hΞ) _
          (presentation_appended_full_lift_gamma hc C Ξ hΞ F) E hE⟩ := by
  have hBC := gamma_named_code_context_base C Ξ hΞ
  have hreal := small_gamma_named_real C Ξ hΞ
  have hNames := gamma_named_code_context_names C Ξ hΞ
  have hGeneric : ∀ {p : ℕ} (x : Fin p → SpecialTransformations.Section5.VF (M := M)),
      AlgebraicIndependent (vfParameterField (𝔅).real) x → AlgebraicIndependent (vfParameterField 𝔖) x :=
    fun x hx => gamma_named_code_context_generic C Ξ hΞ hc x hx
  let e := appendedToOriginalVolumePermutation (n+1) k
  let hA := appended_family_lift_degree_eq (n+1) k
  let h0 := family_realization_degree_eq n k
  let hS := selected_append_degree_eq n k
  let X := F.family.fullLift
  have hX : VFVolumeObjectGamma X 𝔅 := F.gamma.fullLift hc
  let Y := X.reindexDegree hA
  have hY : VFVolumeObjectGamma Y 𝔅 := hX.reindexDegree hA
  have hL := presentation_appended_full_lift_gamma hc C Ξ hΞ F
  obtain ⟨eX,heX⟩ := gamma_full_lift_density_graph_iso hc 𝔇 F.gamma
  let A := nativeMixedVolumeDomain hc F.family.densityGraph.domain
  have hAg : GammaSetDefinable 𝔅 (carrier A) := F.gamma.native_domain hc
  have hW := realization_gamma hc C Ξ hΞ A hAg F.family.densityGraph.selected F.family.densityGraph.finite_selected
    (Fin.last F.arity) F.family.densityGraph_label_nonzero
  let X' := F.family.densityGraph.fullLift
  have hX' : VFVolumeObjectGamma X' 𝔅 :=
    VFVolumeObjectGamma.of_heq h0 (family_density_graph_full_lift_realization_heq hc F.family) hW
  let W := selectedCoordinateVolumeRealization hc A F.family.densityGraph.selected
    F.family.densityGraph.finite_selected (Fin.last F.arity) F.family.densityGraph_label_nonzero
  obtain ⟨EY,hEY,_,_,_⟩ := generated_base_standard_contraction_exists (B := 𝔅) (𝔇).saturated (𝔇).model00
    hreal hGenerated hBC (nativeMixedVolumeDomain hc Y.densityGraph.domain) hY.densityGraph (Equiv.refl _)
  obtain ⟨EX,hEX,_,_,_⟩ := generated_base_standard_contraction_exists (B := 𝔅) (𝔇).saturated (𝔇).model00
    hreal hGenerated hBC (nativeMixedVolumeDomain hc X.densityGraph.domain) hX.densityGraph (Equiv.refl _)
  obtain ⟨EX',hEX',_,_,_⟩ := generated_base_standard_contraction_exists (B := 𝔅) (𝔇).saturated (𝔇).model00
    hreal hGenerated hBC (nativeMixedVolumeDomain hc X'.densityGraph.domain) hX'.densityGraph (Equiv.refl _)
  obtain ⟨EW,hEW,_,_,_⟩ := generated_base_standard_contraction_exists (B := 𝔅) (𝔇).saturated (𝔇).model00
    hreal hGenerated hBC (nativeMixedVolumeDomain hc W.densityGraph.domain) hW.densityGraph (Equiv.refl _)
  have c1 := GammaNamed.gamma_vf_permutation_covariance hc 𝔇 𝔅 hBC hΞ hGenerated hNames hGeneric γ hγ hγ1
    Y hY e.symm EY E hEY hE
  have c2 := GammaNamed.gamma_heq_contraction hc 𝔇 𝔅 hBC hΞ hGenerated hNames hGeneric γ hγ hγ1 hA
    (vf_reindex_degree_heq X hA) hY hX EY EX hEY hEX
  have c3 := GammaNamed.gamma_vf_iso_contraction_comparison hc 𝔇 𝔅 hBC hΞ hGenerated hNames hGeneric γ hγ hγ1
    X X' hX hX' eX heX EX EX' hEX hEX'
  have c4 := GammaNamed.gamma_heq_contraction hc 𝔇 𝔅 hBC hΞ hGenerated hNames hGeneric γ hγ hγ1 h0
    (family_density_graph_full_lift_realization_heq hc F.family) hX' hW EX' EW hEX' hEW
  have c5 := GammaNamed.gamma_selected_realization_contraction hc 𝔇 𝔅 hBC hΞ hGenerated hNames hGeneric γ hγ hγ1
    A hAg F.family.densityGraph.selected F.family.densityGraph.finite_selected (Fin.last F.arity)
    F.family.densityGraph_label_nonzero T hT hW EW hEW
  have c6 := gamma_selected_appended_permuted hc 𝔇 𝔅 A F.family.densityGraph.selected (Fin.last F.arity)
    F.family.densityGraph_label_nonzero F.family.densityGraph.finite_selected T hT
  -- assemble
  have d1 := (((c3.trans hc c4).trans hc ((c5.symm hc).reindexDegree hc h0)).reindexDegree hc hA)
  have d2 := (c2.trans hc d1).trans hc (CommonContextVolumeEquivalent.reindex_trans hc _ hA h0)
  have d3 := c1.trans hc (d2.permuteVolume hc e.symm)
  exact (GammaVolumeBlowupEquivalent.toCommon (c6.symm hc 𝔇 𝔅)).trans hc (d3.symm hc)

end IntegrationInACVF.Section7.GammaFun
