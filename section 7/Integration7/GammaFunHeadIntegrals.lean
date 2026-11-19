import Integration7.GammaFunAEIntegrals
import Integration7.AERVVolumeHeadIntegralComparison
import Integration7.HKPureVFGammaLoci
import IntegrationSection5.GammaHeadPreparation

/-! Gamma-named head integrals: integrating out the first VF coordinate of a
Gamma-named presentation with a Gamma head preparation. Generic Gamma formula
witnesses give almost-everywhere equivalence outside a Gamma VF-small set, and
the head integral descends to almost-everywhere functions. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section9
open SpecialTransformations.Section4 (vfValues)
open SpecialTransformations.Section5 (Point GammaSetDefinable GammaGraphDefinable gammaLogicInput carrier VF RV pointMapGraph headImage)
open IntegrationInACVF.Section5 IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {C : BaseContext M} {G : Base (M := M)} {n a b k : ℕ}

/-- Gamma row equivalence gives the geometric schema comparison of density graphs. -/
theorem gamma_rows_schema_common (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (G : Base (M := M)) {F : SelectedVFVolumeFamily C n a k} {H : SelectedVFVolumeFamily C n b k}
    (hF : F.Gamma G) (hH : H.Gamma G) (x : Fin n → VF (M := M)) (h : GammaRowsEquivalent hc C G hF hH x) :
    (gammaSelectedVolumeSchema (nativeMixedVolumeDomain hc F.densityGraph.domain) (hF.native_domain hc)
        F.densityGraph.selected (Fin.last a)).commonByGammaGeometry
      (gammaSelectedVolumeSchema (nativeMixedVolumeDomain hc H.densityGraph.domain) (hH.native_domain hc)
        H.densityGraph.selected (Fin.last b)) (fun j => (x j).val) := by
  let Cx := vfParameterVolumeContext C x
  have h1 := GammaVolumeBlowupEquivalent.of_iso Cx (rowGammaBase G x)
    (U := ⟨F.densityGraph.rowInContext x,hF.densityGraph_row hc x⟩) (V := ⟨F.rowInContext x,hF.row hc x⟩)
    ((F.densityGraphRowIso hc x).symm hc Cx) ((hF.densityGraphRowIso hc x).symm hc Cx _)
  have h2 := GammaVolumeBlowupEquivalent.of_iso Cx (rowGammaBase G x)
    (U := ⟨H.rowInContext x,hH.row hc x⟩) (V := ⟨H.densityGraph.rowInContext x,hH.densityGraph_row hc x⟩)
    (H.densityGraphRowIso hc x) (hH.densityGraphRowIso hc x)
  exact ⟨Cx,⟨F.densityGraph.rowInContext x,hF.densityGraph_row hc x⟩,
    ⟨H.densityGraph.rowInContext x,hH.densityGraph_row hc x⟩,rfl,rfl,
    F.densityGraph_schema_rows_of hc (hF.native_domain hc) x,H.densityGraph_schema_rows_of hc (hH.native_domain hc) x,
    (h1.trans hc Cx _ h).trans hc Cx _ h2⟩

/-- Names of a row Gamma base lie in a row context of a names-containing code context. -/
theorem row_context_names (C : BaseContext M) (G : Base (M := M)) (hNames : commonRealNames G ⊆ (C.base : Set M))
    (x : Fin n → VF (M := M)) :
    commonRealNames (rowGammaBase G x) ⊆ ((vfParameterVolumeContext C x).base : Set M) := by
  rintro y ((hy | hy) | hy)
  · exact vfParameterVolumeContext_contains C x (Or.inl (hNames (Or.inl hy)))
  · exact vfParameterVolumeContext_contains C x (Or.inr hy)
  · exact vfParameterVolumeContext_contains C x (Or.inl (hNames (Or.inr hy)))

theorem algebraicIndependent_subfield_restrict {K : Type} [Field K] {ι : Type} {E F : Subfield K} {z : ι → K}
    (h : E ≤ F) (hz : AlgebraicIndependent F z) : AlgebraicIndependent E z := by
  letI := (Subfield.inclusion h).toAlgebra
  letI : IsScalarTower E F K := .of_algebraMap_eq (fun _ => rfl)
  exact hz.restrictScalars
    (show Function.Injective (algebraMap E F) from fun _ _ he => Subtype.ext (congrArg (fun y : F => y.val) he))

theorem algebraicIndependent_of_larger_base {S T : Set M} (hST : S ⊆ T) {p : ℕ} (x : Fin p → VFType (M := M))
    (hx : AlgebraicIndependent (vfParameterField T) x) : AlgebraicIndependent (vfParameterField S) x :=
  algebraicIndependent_subfield_restrict (Subfield.closure_mono (fun y hy => hST hy)) hx

end IntegrationInACVF.Section7

namespace IntegrationInACVF.Section7.GammaFun
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n a b k : ℕ}
variable (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
variable (Ξ : Set (Values.Gamma (M := M))) (hΞ : Cardinal.mk Ξ < C.κ)
variable (hGenerated : VFGammaGeneratedBase (gammaNamedBase C Ξ))

set_option quotPrecheck false
local notation "𝔅" => gammaNamedBase C Ξ
local notation "𝔇" => gammaNamedCodeContext C Ξ hΞ
local notation "𝔖" => ((gammaNamedCodeContext C Ξ hΞ).base : Set M)

include hGenerated in
theorem presentation_head_preparation_exists (F : Presentation C Ξ hΞ (n+1) k) :
    ∃ T : HeadPreparation (nativeMixedVolumeDomain hc F.family.densityGraph.domain),
      GammaSetDefinable 𝔅 (carrier T.target) ∧ GammaGraphDefinable 𝔅 (pointMapGraph T.map) := by
  obtain ⟨T,_,_,hT,hg⟩ := gamma_head_preparation (𝔇).saturated (𝔇).model00 𝔅
    ((Cardinal.mk_le_mk_of_subset (gamma_named_code_context_base C Ξ hΞ)).trans_lt (𝔇).small)
    (generatedBaseVFField hGenerated) (gamma_named_code_context_base C Ξ hΞ) _ (F.gamma.native_domain hc)
  exact ⟨T,hT,hg⟩

/-- The chosen Gamma head preparation of a presentation. -/
def Presentation.headPrep (F : Presentation C Ξ hΞ (n+1) k) :
    HeadPreparation (nativeMixedVolumeDomain hc F.family.densityGraph.domain) :=
  Classical.choose (presentation_head_preparation_exists hc C Ξ hΞ hGenerated F)

theorem Presentation.headPrep_target (F : Presentation C Ξ hΞ (n+1) k) :
    GammaSetDefinable 𝔅 (carrier (F.headPrep hc C Ξ hΞ hGenerated).target) :=
  (Classical.choose_spec (presentation_head_preparation_exists hc C Ξ hΞ hGenerated F)).1

theorem Presentation.headPrep_map (F : Presentation C Ξ hΞ (n+1) k) :
    GammaGraphDefinable 𝔅 (pointMapGraph (F.headPrep hc C Ξ hΞ hGenerated).map) :=
  (Classical.choose_spec (presentation_head_preparation_exists hc C Ξ hΞ hGenerated F)).2

/-- The head integral of a family along a Gamma head preparation is Gamma. -/
theorem head_integral_family_gamma (F : SelectedVFVolumeFamily 𝔇 (n+1) a k)
    (T : HeadPreparation (nativeMixedVolumeDomain hc F.densityGraph.domain))
    (hT : GammaSetDefinable 𝔅 (carrier T.target)) :
    (F.headIntegral hc Ξ T).Gamma 𝔅 := by
  have hA : GammaSetDefinable 𝔅 (carrier T.contractedSet) := gamma_headImage T.target hT
  exact ⟨hA,gamma_coordinate_volume_density_graph hc hA _ _ (fun _ => rfl)⟩

/-- **The Gamma head integral of a presentation**: integrate out the first VF coordinate. -/
def Presentation.headIntegral (F : Presentation C Ξ hΞ (n+1) k) : Presentation C Ξ hΞ n (k+1) where
  arity := 1+(F.headPrep hc C Ξ hΞ hGenerated).arity
  family := F.family.headIntegral hc Ξ (F.headPrep hc C Ξ hΞ hGenerated)
  gamma := head_integral_family_gamma hc C Ξ hΞ F.family _ (F.headPrep_target hc C Ξ hΞ hGenerated)

theorem small_gamma_named_real : Cardinal.mk (gammaNamedBase C Ξ).real < (gammaNamedCodeContext C Ξ hΞ).κ :=
  (Cardinal.mk_le_mk_of_subset (gamma_named_code_context_base C Ξ hΞ)).trans_lt (gammaNamedCodeContext C Ξ hΞ).small

/-- **Gamma generic-witness descent.** Generic Gamma common-comparison witnesses for the rows of
two presentations give almost-everywhere equivalence outside a Gamma VF-small set. -/
theorem presentation_ae_of_generic_witnesses (F H : Presentation C Ξ hΞ n k)
    (L : GammaRVVolumeSchema 𝔅 (n+1) F.arity k (fun _ => .vf))
    (R : GammaRVVolumeSchema 𝔅 (n+1) H.arity k (fun _ => .vf))
    (PL : ∀ x, RVVolumeSchemaRow (F.family.rowInContext x) L (vfValues x))
    (PR : ∀ x, RVVolumeSchemaRow (H.family.rowInContext x) R (vfValues x))
    (hWitness : ∀ x, AlgebraicIndependent (vfParameterField (gammaNamedBase C Ξ).real) x →
      ∃ W : GammaVolumeCommonSchema L R, W.valid (vfValues x)) :
    AEEquivalent hc C Ξ hΞ F H := by
  classical
  obtain ⟨J,hJ⟩ := gamma_finite_witnesses_at_generic_points 𝔅 (𝔇).uncountable.le (𝔇).saturated
    (small_gamma_named_real C Ξ hΞ) hΞ
    (fun W : GammaVolumeCommonSchema L R => {z | W.valid z}) (fun W => W.valid_definable hc) hWitness
  let R0 := ⋃ W ∈ J, {z | W.valid z}
  have hR0 : DefinableOverBase 𝔅 (fun _ => .vf) R0 :=
    DefinableOverBase.finite_iUnion J (fun W : GammaVolumeCommonSchema L R => {z | W.valid z})
      (fun W _ => W.valid_definable hc)
  let Good := pureVFFormulaLocus R0 (hR0.common_names.mono (gamma_named_code_context_names C Ξ hΞ))
  let Eset := (SpecialTransformations.DefinableGeometry.DefSet.univ
    (SpecialTransformations.Section4.rawVFSpace (M := M) (n+1)) 𝔖).sdiff Good
  have hAll : GammaSetDefinable 𝔅 (Set.univ : Set (Point (M := M) (n+1) 0)) :=
    (gammaLogicInput 𝔅).real_set _
      (SpecialTransformations.Section5.setDefinable
        (SpecialTransformations.Section5.PresentedSet.univ (SpecialTransformations.Section5.pointSpace (M := M) (n+1) 0)
          (gammaNamedBase C Ξ).real))
  let E : GammaVFSet C Ξ hΞ n := ⟨Eset,by
    have h := (gammaLogicInput 𝔅).sdiff hAll (HK.gamma_pure_vf_locus hR0)
    convert h using 1
    ext q
    exact ⟨fun hq => ⟨Set.mem_univ _,hq.2⟩,fun hq => ⟨Set.mem_univ _,hq.2⟩⟩⟩
  have hGood : ∀ x, AlgebraicIndependent (vfParameterField (gammaNamedBase C Ξ).real) x → x ∈ Good.carrier := by
    intro x hx
    obtain ⟨W,hWJ,hW⟩ := hJ x hx
    exact Set.mem_iUnion.mpr ⟨W,Set.mem_iUnion.mpr ⟨hWJ,hW⟩⟩
  refine ⟨E,pure_vf_dimension_lt_of_no_independent hc 𝔇 (Nat.zero_lt_succ _) Eset ?_,?_⟩
  · intro p hp
    exact p.property.2 (hGood p.val
      (algebraicIndependent_of_larger_base (gamma_named_code_context_base C Ξ hΞ) _ hp))
  · intro x hx
    have hg : x ∈ Good.carrier := by
      by_contra h
      exact hx ⟨Set.mem_univ _,h⟩
    change vfValues x ∈ R0 at hg
    obtain ⟨W,hW⟩ := Set.mem_iUnion.mp hg
    obtain ⟨_,hW⟩ := Set.mem_iUnion.mp hW
    let Cx := vfParameterVolumeContext 𝔇 x
    apply (gammaVolumeBlowupClass_eq_iff hc Cx _).mpr
    have hW' : W.valid (vfValues x) := hW
    obtain ⟨D,hDE,hCommon⟩ := GammaVolumeCommonSchema.realizeOnGamma hc Cx W (vfValues x) hW' (PL x) (PR x)
      (F.gamma.row hc x) (H.gamma.row hc x)
      ((gamma_named_code_context_base C Ξ hΞ).trans (fun y hy => vfParameterVolumeContext_contains 𝔇 x (Or.inl hy)))
      (fun y hy => vfParameterVolumeContext_contains 𝔇 x (Or.inr hy))
    exact (show CommonContextVolumeEquivalent (rowGammaBase 𝔅 x) Cx ⟨_,F.gamma.row hc x⟩ ⟨_,H.gamma.row hc x⟩
      from ⟨D,hDE,hCommon⟩).descend hc Cx (row_context_names 𝔇 𝔅 (gamma_named_code_context_names C Ξ hΞ) x)

/-- Almost-everywhere equivalent presentations have Gamma-equivalent rows at generic points. -/
theorem presentation_rows_at_generic (F H : Presentation C Ξ hΞ n k) (h : AEEquivalent hc C Ξ hΞ F H)
    (x : Fin (n+1) → VFType (M := M)) (hx : AlgebraicIndependent (vfParameterField (gammaNamedBase C Ξ).real) x) :
    RowsEquivalent hc C Ξ hΞ F H x := by
  obtain ⟨E,hE,hRows⟩ := h
  exact (gammaVolumeBlowupClass_eq_iff hc _ _).mp (hRows x (fun hm =>
    pure_vf_small_has_no_independent hc E.set hE ⟨x,hm⟩ (gamma_named_code_context_generic C Ξ hΞ hc x hx)))

variable (γ : Values.Gamma (M := M)) (hγ : γ ∈ Ξ) (hγ1 : 1 < γ)

set_option maxHeartbeats 2400000 in
include hγ hγ1 in
/-- **Head integration respects almost-everywhere equivalence.** -/
theorem presentation_head_integral_ae (F H : Presentation C Ξ hΞ (n+1) k) (h : AEEquivalent hc C Ξ hΞ F H) :
    AEEquivalent hc C Ξ hΞ (F.headIntegral hc C Ξ hΞ hGenerated) (H.headIntegral hc C Ξ hΞ hGenerated) := by
  let T := F.headPrep hc C Ξ hΞ hGenerated
  let E := H.headPrep hc C Ξ hΞ hGenerated
  have hU := F.gamma.native_domain hc
  have hV := H.gamma.native_domain hc
  have hT := F.headPrep_map hc C Ξ hΞ hGenerated
  have hE := H.headPrep_map hc C Ξ hΞ hGenerated
  have hTarget := F.headPrep_target hc C Ξ hΞ hGenerated
  have hETarget := H.headPrep_target hc C Ξ hΞ hGenerated
  have hreal := small_gamma_named_real C Ξ hΞ
  let δ := Fin.natAdd 1 (suffixIndex (specialRelative_rvArity_le T.special) (Fin.last F.arity))
  let ε := Fin.natAdd 1 (suffixIndex (specialRelative_rvArity_le E.special) (Fin.last H.arity))
  let LF := gammaSelectedVolumeSchema T.contractedSet (gamma_headImage T.target hTarget)
    (headAppendVolumeIndex T F.family.densityGraph.selected) δ
  let RG := gammaSelectedVolumeSchema E.contractedSet (gamma_headImage E.target hETarget)
    (headAppendVolumeIndex E H.family.densityGraph.selected) ε
  obtain ⟨NF,hNF⟩ := selected_volume_schema_uniform_bound (𝔇).uncountable.le (𝔇).saturated hreal hΞ
    T.contractedSet (gamma_headImage T.target hTarget) (headAppendVolumeIndex T F.family.densityGraph.selected) δ
    (head_retained_density_nonzero T (Fin.last F.arity) F.family.densityGraph_label_nonzero)
    (F.family.headIntegral hc Ξ T).finite_selected
  obtain ⟨NG,hNG⟩ := selected_volume_schema_uniform_bound (𝔇).uncountable.le (𝔇).saturated hreal hΞ
    E.contractedSet (gamma_headImage E.target hETarget) (headAppendVolumeIndex E H.family.densityGraph.selected) ε
    (head_retained_density_nonzero E (Fin.last H.arity) H.family.densityGraph_label_nonzero)
    (H.family.headIntegral hc Ξ E).finite_selected
  apply presentation_ae_of_generic_witnesses hc C Ξ hΞ _ _ (LF.withBound NF) (RG.withBound NG)
  · intro x
    exact (native_coordinate_volume_family_schema_row hc T.contractedSet (gamma_headImage T.target hTarget)
      (headAppendVolumeIndex T F.family.densityGraph.selected) (F.family.headIntegral hc Ξ T).finite_selected δ
      (head_retained_density_nonzero T (Fin.last F.arity) F.family.densityGraph_label_nonzero) x).congr
      (GammaRVVolumeSchema.sameRow_symm (LF.withBound_sameRow NF _ (fun j => (x j).property)))
  · intro x
    exact (native_coordinate_volume_family_schema_row hc E.contractedSet (gamma_headImage E.target hETarget)
      (headAppendVolumeIndex E H.family.densityGraph.selected) (H.family.headIntegral hc Ξ E).finite_selected ε
      (head_retained_density_nonzero E (Fin.last H.arity) H.family.densityGraph_label_nonzero) x).congr
      (GammaRVVolumeSchema.sameRow_symm (RG.withBound_sameRow NG _ (fun j => (x j).property)))
  · intro x hx
    apply gamma_volume_formula_witness_from_geometry hc (𝔇).uncountable.le (𝔇).saturated (𝔇).model00
      hreal hΞ _ _ _ (hNF x) (hNG x)
    apply GammaRVVolumeSchema.commonByGammaGeometry_transport_rows
      (F := LF) (G := RG) (F' := LF.withBound NF) (G' := RG.withBound NG)
      (z := fun j => (x j).val) (t := fun j => (x j).val) rfl
      (fun _ _ => Iff.rfl) (fun _ _ => Iff.rfl) (fun _ _ => Iff.rfl) (fun _ _ => Iff.rfl)
    exact gamma_head_volume_common_comparison_at_generic hc 𝔇 (𝔇).uncountable.le (𝔇).saturated (𝔇).model00
      hreal hΞ γ hγ hγ1 (gamma_named_code_context_base C Ξ hΞ) _ _ hU hV
      F.family.densityGraph.selected H.family.densityGraph.selected (Fin.last F.arity) (Fin.last H.arity)
      F.family.densityGraph_label_nonzero H.family.densityGraph_label_nonzero
      F.family.densityGraph.finite_selected H.family.densityGraph.finite_selected
      (fun y hy => gamma_rows_schema_common hc 𝔇 𝔅 F.gamma H.gamma y
        (presentation_rows_at_generic hc C Ξ hΞ F H h y hy)) T E hT hE hTarget hETarget x hx

/-- **The Gamma-named head integral of almost-everywhere functions.** -/
def aeHeadIntegral : AEFunction hc C Ξ hΞ (n+1) k → AEFunction hc C Ξ hΞ n (k+1) :=
  Quotient.lift (fun F => Quotient.mk _ (F.headIntegral hc C Ξ hΞ hGenerated))
    (fun F H h => Quotient.sound (presentation_head_integral_ae hc C Ξ hΞ hGenerated γ hγ hγ1 F H h))

end IntegrationInACVF.Section7.GammaFun
