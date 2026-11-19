import Integration7.GammaFunHeadIntegrals
import Integration7.AppendedHeadIntegralPrograms
import Integration7.SelectedIntegralCoordinateEquivalence

/-! Gamma-named head Fubini. Lemma 7.5 for standard appended objects of arbitrary Gamma
sets, the appended-convention integral of a Gamma-named presentation, its comparison with
the canonical integral, and successive integration of one VF head. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section9
open SpecialTransformations.Section4 (vfValues)
open SpecialTransformations.Section5 (Point GammaSetDefinable GammaGraphDefinable gammaLogicInput carrier VF RV pointMapGraph headImage)
open IntegrationInACVF.Section5 IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n a b k : ℕ}

set_option maxHeartbeats 2400000 in
/-- **Gamma Lemma 7.5 for standard appended objects of Gamma sets.** -/
theorem gamma_standard_append_lemma_7_5 (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (G : Base (M := M)) (hGC : G.real ⊆ (C.base : Set M)) (hgamma : Cardinal.mk G.gamma < C.κ)
    (γ : Values.Gamma (M := M)) (hγ : γ ∈ G.gamma) (hγ1 : 1 < γ)
    (U : SpecialTransformations.Section5.DefSet (M := M) (C.base : Set M) n a)
    (V : SpecialTransformations.Section5.DefSet (M := M) (C.base : Set M) n b)
    (hU : GammaSetDefinable G (carrier U)) (hV : GammaSetDefinable G (carrier V))
    (ρ : Fin (k+1) → Fin a) (τ : Fin (k+1) → Fin b) (δ : Fin a) (ε : Fin b)
    (hδ : ∀ p ∈ carrier U, (p.2 δ).val ≠ iRVZero) (hε : ∀ p ∈ carrier V, (p.2 ε).val ≠ iRVZero)
    (hfinU : ∀ (x : Fin n → VF (M := M)) (t : Fin (k+1) → RV (M := M)),
      {v : Fin a → RV (M := M) | (x,v) ∈ carrier U ∧ v ∘ ρ = t}.Finite)
    (hfinV : ∀ (x : Fin n → VF (M := M)) (t : Fin (k+1) → RV (M := M)),
      {v : Fin b → RV (M := M) | (x,v) ∈ carrier V ∧ v ∘ τ = t}.Finite)
    (hCommon : ∀ x : Fin n → VF (M := M),
      (gammaSelectedVolumeSchema U hU ρ δ).commonByGammaGeometry
        (gammaSelectedVolumeSchema V hV τ ε) (fun j => (x j).val))
    {σ : Equiv.Perm (Fin n)} (T : StandardContraction U σ) (E : StandardContraction V σ)
    (hT : GammaProgramDefinable G T.program) (hE : GammaProgramDefinable G E.program) :
    CommonContextVolumeEquivalent G C
      ⟨standardAppendVolumeObject hc C G.gamma U ρ δ hδ hfinU T,
        standard_append_volume_object_gamma_of hc C G.gamma G U ρ δ hδ hfinU T hT⟩
      ⟨standardAppendVolumeObject hc C G.gamma V τ ε hε hfinV E,
        standard_append_volume_object_gamma_of hc C G.gamma G V τ ε hε hfinV E hE⟩ := by
  have hreal : Cardinal.mk G.real < C.κ := (Cardinal.mk_le_mk_of_subset hGC).trans_lt C.small
  have hTotal := lemma_7_5_standard_geometric hc C C.uncountable.le C.saturated C.model00 hreal hgamma γ hγ hγ1
    hGC U V hU hV ρ τ δ ε hδ hε hfinU hfinV hCommon T E hT hE
  let z : Fin 0 → M := fun i => (Fin.elim0 i : VF (M := M)).val
  have hBase : (⟨G.real ∪ Set.range z,G.gamma⟩ : Base (M := M)) = G := by
    change (⟨G.real ∪ Set.range z,G.gamma⟩ : Base (M := M)) = ⟨G.real,G.gamma⟩
    rw [Set.range_eq_empty,Set.union_empty]
  have hUo := standard_append_volume_object_gamma_of hc C G.gamma G U ρ δ hδ hfinU T hT
  have hVo := standard_append_volume_object_gamma_of hc C G.gamma G V τ ε hε hfinV E hE
  have hU' : VolumeObjectGamma (standardAppendVolumeObject hc C G.gamma U ρ δ hδ hfinU T)
      ⟨G.real ∪ Set.range z,G.gamma⟩ := hBase.symm ▸ hUo
  have hV' : VolumeObjectGamma (standardAppendVolumeObject hc C G.gamma V τ ε hε hfinV E)
      ⟨G.real ∪ Set.range z,G.gamma⟩ := hBase.symm ▸ hVo
  have hBC : G.real ∪ Set.range z ⊆ (C.base : Set M) := by
    simpa only [Set.range_eq_empty,Set.union_empty] using hGC
  obtain ⟨D,hCD,h⟩ := GammaRVVolumeSchema.commonByGammaGeometry_on_objects hc C _ _ _ _ z
    (standard_append_volume_object_schema_row_of hc C G.gamma G U ρ δ hδ hfinU T hT)
    (standard_append_volume_object_schema_row_of hc C G.gamma G V τ ε hε hfinV E hE)
    hU' hV' hBC (hTotal Fin.elim0)
  exact ⟨D,hCD,h.rebase hBase⟩

/-- A native coordinate family of a Gamma set is Gamma. -/
theorem native_coordinate_volume_family_gamma (hc : CanonicalStructure.IsCanonical (M := M)) {C : BaseContext M}
    {G : Base (M := M)} (A : SpecialTransformations.Section5.DefSet (M := M) (C.base : Set M) n a)
    (hA : GammaSetDefinable G (carrier A)) (ρ : Fin (k+1) → Fin a)
    (hfin : ∀ (x : Fin n → VF (M := M)) (t : Fin (k+1) → RV (M := M)),
      {r : Fin a → RV (M := M) | (x,r) ∈ carrier A ∧ r ∘ ρ = t}.Finite)
    (δ : Fin a) (hδ : ∀ p ∈ carrier A, (p.2 δ).val ≠ iRVZero) :
    (nativeCoordinateVolumeFamily hc A ρ hfin δ hδ).Gamma G :=
  ⟨hA,gamma_coordinate_volume_density_graph hc hA _ _ (fun _ => rfl)⟩

set_option maxHeartbeats 2400000 in
/-- The standard appended object of a native coordinate family is common-context equivalent
to the standard appended object of its Gamma set. -/
theorem gamma_native_family_append_comparison (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (G : Base (M := M)) (hGC : G.real ⊆ (C.base : Set M)) (hgamma : Cardinal.mk G.gamma < C.κ)
    (γ : Values.Gamma (M := M)) (hγ : γ ∈ G.gamma) (hγ1 : 1 < γ)
    (A : SpecialTransformations.Section5.DefSet (M := M) (C.base : Set M) n a)
    (hA : GammaSetDefinable G (carrier A)) (ρ : Fin (k+1) → Fin a)
    (hfin : ∀ (x : Fin n → VF (M := M)) (t : Fin (k+1) → RV (M := M)),
      {r : Fin a → RV (M := M) | (x,r) ∈ carrier A ∧ r ∘ ρ = t}.Finite)
    (δ : Fin a) (hδ : ∀ p ∈ carrier A, (p.2 δ).val ≠ iRVZero) {σ : Equiv.Perm (Fin n)}
    (T : StandardContraction (nativeMixedVolumeDomain hc
      (nativeCoordinateVolumeFamily hc A ρ hfin δ hδ).densityGraph.domain) σ)
    (D : StandardContraction A σ)
    (hT : GammaProgramDefinable G T.program) (hD : GammaProgramDefinable G D.program) :
    CommonContextVolumeEquivalent G C
      ⟨(nativeCoordinateVolumeFamily hc A ρ hfin δ hδ).standardAppendObject hc G.gamma T,
        standard_append_volume_object_gamma_of hc C G.gamma G _ _ _ _ _ T hT⟩
      ⟨standardAppendVolumeObject hc C G.gamma A ρ δ hδ hfin D,
        standard_append_volume_object_gamma_of hc C G.gamma G A ρ δ hδ hfin D hD⟩ := by
  let H := nativeCoordinateVolumeFamily hc A ρ hfin δ hδ
  have hH : H.Gamma G := native_coordinate_volume_family_gamma hc A hA ρ hfin δ hδ
  refine gamma_standard_append_lemma_7_5 hc C G hGC hgamma γ hγ hγ1 _ A (hH.native_domain hc) hA
    H.densityGraph.selected ρ (Fin.last a) δ (fun p hp => H.densityGraph_label_nonzero p hp) hδ
    H.densityGraph.finite_selected hfin ?_ T D hT hD
  intro x
  let Cx := vfParameterVolumeContext C x
  have h1 := GammaVolumeBlowupEquivalent.of_iso Cx (rowGammaBase G x)
    (U := ⟨H.densityGraph.rowInContext x,hH.densityGraph_row hc x⟩) (V := ⟨H.rowInContext x,hH.row hc x⟩)
    ((H.densityGraphRowIso hc x).symm hc Cx) ((hH.densityGraphRowIso hc x).symm hc Cx _)
  exact ⟨Cx,⟨H.densityGraph.rowInContext x,hH.densityGraph_row hc x⟩,⟨H.rowInContext x,hH.row hc x⟩,rfl,rfl,
    H.densityGraph_schema_rows_of hc (hH.native_domain hc) x,
    native_coordinate_volume_family_schema_row hc A hA ρ hfin δ hδ x,h1⟩

set_option maxHeartbeats 2400000 in
/-- Appended Gamma equivalence gives canonical Gamma equivalence. -/
theorem gamma_selected_canonical_of_appended (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (G : Base (M := M))
    (A : SpecialTransformations.Section5.DefSet (M := M) (C.base : Set M) (n+1) a)
    (B : SpecialTransformations.Section5.DefSet (M := M) (C.base : Set M) (n+1) b)
    (ρ : Fin (k+1) → Fin a) (τ : Fin (k+1) → Fin b) (δ : Fin a) (ε : Fin b)
    (hδ : ∀ p ∈ carrier A, (p.2 δ).val ≠ iRVZero) (hε : ∀ p ∈ carrier B, (p.2 ε).val ≠ iRVZero)
    (hfinA : ∀ (x : Fin (n+1) → VF (M := M)) (t : Fin (k+1) → RV (M := M)),
      {r : Fin a → RV (M := M) | (x,r) ∈ carrier A ∧ r ∘ ρ = t}.Finite)
    (hfinB : ∀ (x : Fin (n+1) → VF (M := M)) (t : Fin (k+1) → RV (M := M)),
      {r : Fin b → RV (M := M) | (x,r) ∈ carrier B ∧ r ∘ τ = t}.Finite)
    (T : StandardContraction A (Equiv.refl _)) (E : StandardContraction B (Equiv.refl _))
    (hT : GammaProgramDefinable G T.program) (hE : GammaProgramDefinable G E.program)
    (h : GammaVolumeBlowupEquivalent G (C.base : Set M) (appendVolumeDegree (n+1) k)
      ⟨standardAppendVolumeObject hc C G.gamma A ρ δ hδ hfinA T,
        standard_append_volume_object_gamma_of hc C G.gamma G A ρ δ hδ hfinA T hT⟩
      ⟨standardAppendVolumeObject hc C G.gamma B τ ε hε hfinB E,
        standard_append_volume_object_gamma_of hc C G.gamma G B τ ε hε hfinB E hE⟩) :
    GammaVolumeBlowupEquivalent G (C.base : Set M) ((k+1)+n)
      ⟨selectedStandardVolumeObject hc C G.gamma A ρ δ hδ hfinA T,
        GammaNamed.selected_standard_volume_object_gamma hc C G.gamma G A ρ δ hδ hfinA T hT⟩
      ⟨selectedStandardVolumeObject hc C G.gamma B τ ε hε hfinB E,
        GammaNamed.selected_standard_volume_object_gamma hc C G.gamma G B τ ε hε hfinB E hE⟩ := by
  let U' : GammaVolumeObjects G (C.base : Set M) ((k+1)+n) :=
    ⟨selectedStandardVolumeObject hc C G.gamma A ρ δ hδ hfinA T,
      GammaNamed.selected_standard_volume_object_gamma hc C G.gamma G A ρ δ hδ hfinA T hT⟩
  let V' : GammaVolumeObjects G (C.base : Set M) ((k+1)+n) :=
    ⟨selectedStandardVolumeObject hc C G.gamma B τ ε hε hfinB E,
      GammaNamed.selected_standard_volume_object_gamma hc C G.gamma G B τ ε hε hfinB E hE⟩
  have hU0 := standard_append_volume_object_gamma_of hc C G.gamma G A ρ δ hδ hfinA T hT
  have hV0 := standard_append_volume_object_gamma_of hc C G.gamma G B τ ε hε hfinB E hE
  have hNew := h.of_permuted_coordinate_charts hc C (U' := U'.reindexDegree (selected_append_degree_eq n k))
    (V' := V'.reindexDegree (selected_append_degree_eq n k)) (appendedToOriginalVolumePermutation (n+1) k)
    (selectedIntegralCoordinateChart hc C G.gamma A ρ δ hδ hfinA T)
    (selectedIntegralCoordinateChart hc C G.gamma B τ ε hε hfinB E)
    (gamma_rv_coordinate_map hc _ id hU0.domain_graph (fun _ => rfl))
    (gamma_rv_coordinate_map hc _ id hV0.domain_graph (fun _ => rfl))
    (selected_integral_coordinate_chart_coordinates hc C G.gamma A ρ δ hδ hfinA T)
    (selected_integral_coordinate_chart_coordinates hc C G.gamma B τ ε hε hfinB E)
    (selected_integral_coordinate_chart_density hc C G.gamma A ρ δ hδ hfinA T)
    (selected_integral_coordinate_chart_density hc C G.gamma B τ ε hε hfinB E)
  exact IntegrationInACVF.Section7.GammaFun.GammaVolumeBlowupEquivalent.of_reindexDegree' hc C G (selected_append_degree_eq n k) hNew

set_option maxHeartbeats 2400000 in
/-- Canonical Gamma equivalence gives appended Gamma equivalence. -/
theorem gamma_selected_appended_of_canonical (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (G : Base (M := M))
    (A : SpecialTransformations.Section5.DefSet (M := M) (C.base : Set M) (n+1) a)
    (B : SpecialTransformations.Section5.DefSet (M := M) (C.base : Set M) (n+1) b)
    (ρ : Fin (k+1) → Fin a) (τ : Fin (k+1) → Fin b) (δ : Fin a) (ε : Fin b)
    (hδ : ∀ p ∈ carrier A, (p.2 δ).val ≠ iRVZero) (hε : ∀ p ∈ carrier B, (p.2 ε).val ≠ iRVZero)
    (hfinA : ∀ (x : Fin (n+1) → VF (M := M)) (t : Fin (k+1) → RV (M := M)),
      {r : Fin a → RV (M := M) | (x,r) ∈ carrier A ∧ r ∘ ρ = t}.Finite)
    (hfinB : ∀ (x : Fin (n+1) → VF (M := M)) (t : Fin (k+1) → RV (M := M)),
      {r : Fin b → RV (M := M) | (x,r) ∈ carrier B ∧ r ∘ τ = t}.Finite)
    (T : StandardContraction A (Equiv.refl _)) (E : StandardContraction B (Equiv.refl _))
    (hT : GammaProgramDefinable G T.program) (hE : GammaProgramDefinable G E.program)
    (h : GammaVolumeBlowupEquivalent G (C.base : Set M) ((k+1)+n)
      ⟨selectedStandardVolumeObject hc C G.gamma A ρ δ hδ hfinA T,
        GammaNamed.selected_standard_volume_object_gamma hc C G.gamma G A ρ δ hδ hfinA T hT⟩
      ⟨selectedStandardVolumeObject hc C G.gamma B τ ε hε hfinB E,
        GammaNamed.selected_standard_volume_object_gamma hc C G.gamma G B τ ε hε hfinB E hE⟩) :
    GammaVolumeBlowupEquivalent G (C.base : Set M) (appendVolumeDegree (n+1) k)
      ⟨standardAppendVolumeObject hc C G.gamma A ρ δ hδ hfinA T,
        standard_append_volume_object_gamma_of hc C G.gamma G A ρ δ hδ hfinA T hT⟩
      ⟨standardAppendVolumeObject hc C G.gamma B τ ε hε hfinB E,
        standard_append_volume_object_gamma_of hc C G.gamma G B τ ε hε hfinB E hE⟩ := by
  let fA := selectedIntegralCoordinateChart hc C G.gamma A ρ δ hδ hfinA T
  let fB := selectedIntegralCoordinateChart hc C G.gamma B τ ε hε hfinB E
  have hU1 := (GammaNamed.selected_standard_volume_object_gamma hc C G.gamma G A ρ δ hδ hfinA T hT).reindexDegree
    (selected_append_degree_eq n k)
  have hV1 := (GammaNamed.selected_standard_volume_object_gamma hc C G.gamma G B τ ε hε hfinB E hE).reindexDegree
    (selected_append_degree_eq n k)
  have hdA := selected_integral_coordinate_chart_density hc C G.gamma A ρ δ hδ hfinA T
  have hdB := selected_integral_coordinate_chart_density hc C G.gamma B τ ε hε hfinB E
  exact (h.reindexDegree hc C (selected_append_degree_eq n k)).of_permuted_coordinate_charts hc C
    (appendedToOriginalVolumePermutation (n+1) k).symm fA.symm fB.symm
    (gamma_rv_coordinate_map hc _ id hU1.domain_graph (fun x => by
      have h1 : (finiteIsoMap fA (finiteIsoMap fA.symm x)).val = (finiteIsoMap fA.symm x).val ∘ id := rfl
      rw [finiteIsoMap_apply_symm] at h1
      exact h1.symm))
    (gamma_rv_coordinate_map hc _ id hV1.domain_graph (fun x => by
      have h1 : (finiteIsoMap fB (finiteIsoMap fB.symm x)).val = (finiteIsoMap fB.symm x).val ∘ id := rfl
      rw [finiteIsoMap_apply_symm] at h1
      exact h1.symm))
    (finite_volume_coordinate_chart_inverse fA _
      (selected_integral_coordinate_chart_coordinates hc C G.gamma A ρ δ hδ hfinA T))
    (finite_volume_coordinate_chart_inverse fB _
      (selected_integral_coordinate_chart_coordinates hc C G.gamma B τ ε hε hfinB E))
    (fun v => by
      have h1 := hdA (finiteIsoMap fA.symm v)
      rw [finiteIsoMap_apply_symm] at h1
      exact h1.symm)
    (fun v => by
      have h1 := hdB (finiteIsoMap fB.symm v)
      rw [finiteIsoMap_apply_symm] at h1
      exact h1.symm)

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

/-- The Gamma standard appended object of a presentation for a Gamma contraction. -/
def Presentation.appendedObject (F : Presentation C Ξ hΞ n k)
    (T : StandardContraction (nativeMixedVolumeDomain hc F.family.densityGraph.domain) (Equiv.refl _))
    (hT : GammaProgramDefinable 𝔅 T.program) : GammaVolumeObjects 𝔅 𝔖 (appendVolumeDegree (n+1) k) :=
  ⟨F.family.standardAppendObject hc Ξ T, standard_append_volume_object_gamma_of hc 𝔇 Ξ 𝔅 _ _ _ _ _ T hT⟩

/-- **The appended-convention Gamma-named integral of a presentation.** -/
def Presentation.appendedIntegral (F : Presentation C Ξ hΞ n k) :
    GammaVolumeBlowupClasses hc 𝔇 𝔅 (appendVolumeDegree (n+1) k) :=
  gammaVolumeBlowupClass hc 𝔇 𝔅
    (F.appendedObject hc C Ξ hΞ (F.contraction hc C Ξ hΞ hGenerated) (F.contraction_gamma hc C Ξ hΞ hGenerated))

variable (γ : Values.Gamma (M := M)) (hγ : γ ∈ Ξ) (hγ1 : 1 < γ)

include hγ hγ1 in
/-- **Gamma Lemma 7.5 on appended integrals.** -/
theorem presentation_appended_eq_of_rows (F H : Presentation C Ξ hΞ n k)
    (hRows : ∀ x, RowsEquivalent hc C Ξ hΞ F H x)
    (T : StandardContraction (nativeMixedVolumeDomain hc F.family.densityGraph.domain) (Equiv.refl _))
    (E : StandardContraction (nativeMixedVolumeDomain hc H.family.densityGraph.domain) (Equiv.refl _))
    (hT : GammaProgramDefinable 𝔅 T.program) (hE : GammaProgramDefinable 𝔅 E.program) :
    gammaVolumeBlowupClass hc 𝔇 𝔅 (F.appendedObject hc C Ξ hΞ T hT) =
      gammaVolumeBlowupClass hc 𝔇 𝔅 (H.appendedObject hc C Ξ hΞ E hE) :=
  (gammaVolumeBlowupClass_eq_iff hc 𝔇 𝔅).mpr
    ((gamma_family_lemma_7_5 hc 𝔇 𝔅 (gamma_named_code_context_base C Ξ hΞ) hΞ γ hγ hγ1
      F.gamma H.gamma hRows T E hT hE).descend hc 𝔇 (gamma_named_code_context_names C Ξ hΞ))

theorem presentation_rows_refl (F : Presentation C Ξ hΞ n k) (x : Fin (n+1) → VFType (M := M)) :
    RowsEquivalent hc C Ξ hΞ F F x :=
  GammaVolumeBlowupEquivalent.refl hc (vfParameterVolumeContext 𝔇 x) (rowGammaBase 𝔅 x) _

include hγ hγ1 in
theorem presentation_appended_integral_eq (F : Presentation C Ξ hΞ n k)
    (T : StandardContraction (nativeMixedVolumeDomain hc F.family.densityGraph.domain) (Equiv.refl _))
    (hT : GammaProgramDefinable 𝔅 T.program) :
    F.appendedIntegral hc C Ξ hΞ hGenerated = gammaVolumeBlowupClass hc 𝔇 𝔅 (F.appendedObject hc C Ξ hΞ T hT) :=
  presentation_appended_eq_of_rows hc C Ξ hΞ γ hγ hγ1 F F (presentation_rows_refl hc C Ξ hΞ F) _ _ _ _

include hγ hγ1 in
/-- Equal appended integrals give equal canonical integrals. -/
theorem presentation_integral_eq_of_appended (F H : Presentation C Ξ hΞ n k)
    (h : F.appendedIntegral hc C Ξ hΞ hGenerated = H.appendedIntegral hc C Ξ hΞ hGenerated) :
    F.integral hc C Ξ hΞ hGenerated = H.integral hc C Ξ hΞ hGenerated :=
  (gammaVolumeBlowupClass_eq_iff hc 𝔇 𝔅).mpr
    (gamma_selected_canonical_of_appended hc 𝔇 𝔅 _ _ _ _ _ _ _ _ _ _ _ _
      (F.contraction_gamma hc C Ξ hΞ hGenerated) (H.contraction_gamma hc C Ξ hΞ hGenerated)
      ((gammaVolumeBlowupClass_eq_iff hc 𝔇 𝔅).mp h))

include hγ hγ1 in
/-- Equal canonical integrals give equal appended integrals. -/
theorem presentation_appended_eq_of_integral (F H : Presentation C Ξ hΞ n k)
    (h : F.integral hc C Ξ hΞ hGenerated = H.integral hc C Ξ hΞ hGenerated) :
    F.appendedIntegral hc C Ξ hΞ hGenerated = H.appendedIntegral hc C Ξ hΞ hGenerated :=
  (gammaVolumeBlowupClass_eq_iff hc 𝔇 𝔅).mpr
    (gamma_selected_appended_of_canonical hc 𝔇 𝔅 _ _ _ _ _ _ _ _ _ _ _ _
      (F.contraction_gamma hc C Ξ hΞ hGenerated) (H.contraction_gamma hc C Ξ hΞ hGenerated)
      ((gammaVolumeBlowupClass_eq_iff hc 𝔇 𝔅).mp h))

include hγ hγ1 in
/-- **The appended Gamma-named integral of almost-everywhere functions.** -/
def aeAppendedIntegral : AEFunction hc C Ξ hΞ n k → GammaVolumeBlowupClasses hc 𝔇 𝔅 (appendVolumeDegree (n+1) k) :=
  Quotient.lift (fun F => F.appendedIntegral hc C Ξ hΞ hGenerated)
    (fun F H h => presentation_appended_eq_of_integral hc C Ξ hΞ hGenerated γ hγ hγ1 F H
      (presentation_integral_ae hc C Ξ hΞ hGenerated γ hγ hγ1 F H h))

set_option maxHeartbeats 2400000 in
include hγ hγ1 in
/-- **Gamma head Fubini**: integrating out one VF head and then the rest equals total
integration. -/
theorem presentation_head_fubini (F : Presentation C Ξ hΞ (n+1) k) :
    (F.headIntegral hc C Ξ hΞ hGenerated).appendedIntegral hc C Ξ hΞ hGenerated =
      F.appendedIntegral hc C Ξ hΞ hGenerated := by
  let T := F.headPrep hc C Ξ hΞ hGenerated
  have hT := F.headPrep_map hc C Ξ hΞ hGenerated
  have hTarget := F.headPrep_target hc C Ξ hΞ hGenerated
  have hA : GammaSetDefinable 𝔅 (carrier T.contractedSet) := gamma_headImage T.target hTarget
  have hBC := gamma_named_code_context_base C Ξ hΞ
  have hNames := gamma_named_code_context_names C Ξ hΞ
  obtain ⟨D,hD,_⟩ := generated_base_standard_contraction_exists (B := 𝔅) (𝔇).saturated (𝔇).model00
    (small_gamma_named_real C Ξ hΞ) hGenerated hBC T.contractedSet hA (Equiv.refl _)
  let P := identityHeadTailStandardContraction T D
  have hP : GammaProgramDefinable 𝔅 P.program :=
    gamma_orderedCastSource _ _ ⟨hT,hTarget,gamma_orderedCastSource _ _ hD⟩
  let H := F.headIntegral hc C Ξ hΞ hGenerated
  have hHead := (gamma_native_family_append_comparison hc 𝔇 𝔅 hBC hΞ γ hγ hγ1 T.contractedSet hA
    (headAppendVolumeIndex T F.family.densityGraph.selected) (F.family.headIntegral hc Ξ T).finite_selected
    (Fin.natAdd 1 (suffixIndex (specialRelative_rvArity_le T.special) (Fin.last F.arity)))
    (head_retained_density_nonzero T (Fin.last F.arity) F.family.densityGraph_label_nonzero)
    (H.contraction hc C Ξ hΞ hGenerated) D (H.contraction_gamma hc C Ξ hΞ hGenerated) hD).descend hc 𝔇 hNames
  have hIso := gamma_volume_iso_of_label_identity hc
    (appendedHeadIntegralVolumeIso hc 𝔇 Ξ (nativeMixedVolumeDomain hc F.family.densityGraph.domain) T
      F.family.densityGraph.selected (Fin.last F.arity) F.family.densityGraph_label_nonzero
      F.family.densityGraph.finite_selected (F.family.headIntegral hc Ξ T).finite_selected D)
    (standard_append_volume_object_gamma_of hc 𝔇 Ξ 𝔅 _ _ _ _ _ D hD) rfl (fun _ => rfl)
  rw [presentation_appended_integral_eq hc C Ξ hΞ hGenerated γ hγ hγ1 F P hP]
  apply (gammaVolumeBlowupClass_eq_iff hc 𝔇 𝔅).mpr
  exact hHead.trans hc 𝔇 𝔅 (GammaVolumeBlowupEquivalent.of_iso 𝔇 𝔅 _ hIso)

include hγ hγ1 in
/-- **Gamma head Fubini for almost-everywhere functions.** -/
theorem ae_head_fubini (f : AEFunction hc C Ξ hΞ (n+1) k) :
    aeAppendedIntegral hc C Ξ hΞ hGenerated γ hγ hγ1 (aeHeadIntegral hc C Ξ hΞ hGenerated γ hγ hγ1 f) =
      aeAppendedIntegral hc C Ξ hΞ hGenerated γ hγ hγ1 f := by
  induction f using Quotient.inductionOn with
  | h F => exact presentation_head_fubini hc C Ξ hΞ hGenerated γ hγ hγ1 F

end IntegrationInACVF.Section7.GammaFun
