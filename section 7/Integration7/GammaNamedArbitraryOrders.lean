import Integration7.GammaNamedCommonHeadComparisons
import Integration7.SelectedArbitraryContractionOrders
import Integration7.RetainedDensityArbitraryOrderComparisons

/-! Gamma-named independence of the contraction order: all standard
contraction orders of a Gamma finite-label VF domain give Gamma-named
common-context equivalent selected and normalized contraction objects. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section5
open IntegrationInACVF.Section5 IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7.GammaNamed
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n a : ℕ}

set_option maxHeartbeats 2400000 in
theorem selected_volume_contraction_order_independent
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (G : Base (M := M)) (hGC : G.real ⊆ (C.base : Set M)) (hΞ : Cardinal.mk G.gamma < C.κ)
    (hGenerated : VFGammaGeneratedBase G) (hNames : commonRealNames G ⊆ (C.base : Set M))
    (hGeneric : ∀ {p : ℕ} (x : Fin p → VF (M := M)), AlgebraicIndependent (vfParameterField G.real) x →
      AlgebraicIndependent (vfParameterField (C.base : Set M)) x)
    (γ : Values.Gamma (M := M)) (hγ : γ ∈ G.gamma) (hγ1 : 1 < γ) (n : ℕ) :
    SelectedVolumeOrderIndependent hc C G n := by
  have hreal : Cardinal.mk G.real < C.κ := (Cardinal.mk_le_mk_of_subset hGC).trans_lt C.small
  induction n with
  | zero =>
    intro a d A hA ρ δ hδ hfin σ υ T E hT hE
    have hOrder : υ = σ := by
      apply Equiv.ext
      intro j
      apply Fin.ext
      have hυ := (υ j).isLt
      have hσ := (σ j).isLt
      omega
    subst υ
    exact selected_same_order_standard_volume_comparison hc C G hGC hΞ hGeneric γ hγ hγ1
      A hA ρ hfin δ hδ T E hT hE
  | succ n ih =>
    intro a d A hA ρ δ hδ hfin σ υ T E hT hE
    by_cases h0 : σ 0 = υ 0
    · exact selected_common_head_order_comparison hc C G hGC hΞ hGenerated hGeneric γ hγ hγ1 ih
        A hA ρ δ hδ hfin σ υ h0 T E hT hE
    · obtain ⟨π,hπ0,hπ1⟩ := exists_contraction_bridge_order σ υ h0
      obtain ⟨D,hD,_,_,_⟩ := generated_base_standard_contraction_exists (B := G) C.saturated C.model00
        hreal hGenerated hGC A hA π
      obtain ⟨F,hF,_,_,_⟩ := generated_base_standard_contraction_exists (B := G) C.saturated C.model00
        hreal hGenerated hGC A hA ((swapFirstTwo n).trans π)
      have hLeft := selected_common_head_order_comparison hc C G hGC hΞ hGenerated hGeneric γ hγ hγ1 ih
        A hA ρ δ hδ hfin σ π hπ0.symm T D hT hD
      have hFirst : ((swapFirstTwo n).trans π) 0 = υ 0 := by
        change π (swapFirstTwo n 0) = υ 0
        rw [swapFirstTwo_zero]
        exact hπ1
      have hRight := selected_common_head_order_comparison hc C G hGC hΞ hGenerated hGeneric γ hγ hγ1 ih
        A hA ρ δ hδ hfin ((swapFirstTwo n).trans π) υ hFirst F E hF hE
      have hMiddle := selected_first_two_standard_volume_exchange hc C G hGC hΞ hGenerated hNames hGeneric
        γ hγ hγ1 A hA ρ hfin δ hδ
        (by change π (swapFirstTwo n 0) = π (0 : Fin (n+1)).succ; rw [swapFirstTwo_zero])
        (by change π (swapFirstTwo n (0 : Fin (n+1)).succ) = π 0; rw [swapFirstTwo_one])
        (fun j => by change π (swapFirstTwo n j.succ.succ) = π j.succ.succ; rw [swapFirstTwo_tail])
        D F hD hF
      exact hLeft.trans hc (hMiddle.trans hc hRight)

theorem empty_selected_raw_volume_iso_gamma
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M) (G : Base (M := M))
    (A : SpecialTransformations.Section5.DefSet (M := M) (C.base : Set M) (n+1) a)
    (hfin : ∀ x : Fin (n+1) → VF (M := M), {r : Fin a → RV (M := M) | (x,r) ∈ carrier A}.Finite)
    (δ : Fin a) (hδ : ∀ p ∈ carrier A, (p.2 δ).val ≠ iRVZero)
    {σ : Equiv.Perm (Fin (n+1))} (T : StandardContraction A σ) (hT : GammaProgramDefinable G T.program) :
    (emptySelectedRawVolumeIso hc C G.gamma A hfin δ hδ T).GammaDefinable G := by
  have hU := (selected_standard_volume_object_gamma hc C G.gamma G A (Fin.elim0 : Fin 0 → Fin a) δ hδ
    (empty_selected_volume_finite A hfin) T hT).reindexDegree ((Nat.zero_add n).symm)
  exact gamma_volume_iso_of_full_map _ _ (gamma_essential_volume_domain _ hU.coordinates)
    ((RVMapGamma.identity hc hU.domain_graph).congr (fun _ => rfl)) (fun _ => rfl)

set_option maxHeartbeats 1600000 in
theorem retained_density_arbitrary_order_contractions_compare
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (G : Base (M := M)) (hGC : G.real ⊆ (C.base : Set M)) (hΞ : Cardinal.mk G.gamma < C.κ)
    (hGenerated : VFGammaGeneratedBase G) (hNames : commonRealNames G ⊆ (C.base : Set M))
    (hGeneric : ∀ {p : ℕ} (x : Fin p → VF (M := M)), AlgebraicIndependent (vfParameterField G.real) x →
      AlgebraicIndependent (vfParameterField (C.base : Set M)) x)
    (γ : Values.Gamma (M := M)) (hγ : γ ∈ G.gamma) (hγ1 : 1 < γ)
    (A : SpecialTransformations.Section5.DefSet (M := M) (C.base : Set M) (n+1) a)
    (hA : GammaSetDefinable G (carrier A))
    (hfin : ∀ x : Fin (n+1) → VF (M := M), {r : Fin a → RV (M := M) | (x,r) ∈ carrier A}.Finite)
    (δ : Fin a) (hδ : ∀ p ∈ carrier A, (p.2 δ).val ≠ iRVZero)
    (σ υ : Equiv.Perm (Fin (n+1))) (T : StandardContraction A σ) (E : StandardContraction A υ)
    (hT : GammaProgramDefinable G T.program) (hE : GammaProgramDefinable G E.program) :
    CommonContextVolumeEquivalent G C
      (retainedDensityContractionGammaObject C.uncountable.le C.saturated
        ((Cardinal.mk_le_mk_of_subset hGC).trans_lt C.small) hc C hGC A hA hfin δ
        (fun p => hδ p.val p.property) T hT)
      (retainedDensityContractionGammaObject C.uncountable.le C.saturated
        ((Cardinal.mk_le_mk_of_subset hGC).trans_lt C.small) hc C hGC A hA hfin δ
        (fun p => hδ p.val p.property) E hE) := by
  let ρ : Fin 0 → Fin a := Fin.elim0
  let hfin₀ := empty_selected_volume_finite A hfin
  let PT : GammaVolumeObjects G (C.base : Set M) n :=
    GammaVolumeObjects.reindexDegree (⟨selectedStandardVolumeObject hc C G.gamma A ρ δ hδ hfin₀ T,
      selected_standard_volume_object_gamma hc C G.gamma G A ρ δ hδ hfin₀ T hT⟩ :
      GammaVolumeObjects G (C.base : Set M) (0+n)) ((Nat.zero_add n).symm)
  let PE : GammaVolumeObjects G (C.base : Set M) n :=
    GammaVolumeObjects.reindexDegree (⟨selectedStandardVolumeObject hc C G.gamma A ρ δ hδ hfin₀ E,
      selected_standard_volume_object_gamma hc C G.gamma G A ρ δ hδ hfin₀ E hE⟩ :
      GammaVolumeObjects G (C.base : Set M) (0+n)) ((Nat.zero_add n).symm)
  let RT : GammaVolumeObjects G (C.base : Set M) n :=
    ⟨rawStandardVolumeObject hc C G.gamma A hfin δ hδ T,
      raw_standard_volume_object_gamma hc C G hGC A hA hfin δ hδ T hT⟩
  let RE : GammaVolumeObjects G (C.base : Set M) n :=
    ⟨rawStandardVolumeObject hc C G.gamma A hfin δ hδ E,
      raw_standard_volume_object_gamma hc C G hGC A hA hfin δ hδ E hE⟩
  have hOrders : CommonContextVolumeEquivalent G C PT PE :=
    (selected_volume_contraction_order_independent hc C G hGC hΞ hGenerated hNames hGeneric γ hγ hγ1 n
      A hA ρ δ hδ hfin₀ σ υ T E hT hE).reindexDegree hc ((Nat.zero_add n).symm)
  have hT' : CommonContextVolumeEquivalent G C PT RT :=
    .of_iso (emptySelectedRawVolumeIso hc C G.gamma A hfin δ hδ T)
      (empty_selected_raw_volume_iso_gamma hc C G A hfin δ hδ T hT)
  have hE' : CommonContextVolumeEquivalent G C PE RE :=
    .of_iso (emptySelectedRawVolumeIso hc C G.gamma A hfin δ hδ E)
      (empty_selected_raw_volume_iso_gamma hc C G A hfin δ hδ E hE)
  have hRaw : CommonContextVolumeEquivalent G C RT RE := ((hT'.symm hc).trans hc hOrders).trans hc hE'
  have hNT := raw_standard_volume_normalization hc C G hGC A hA hfin δ hδ T hT
  have hNE := raw_standard_volume_normalization hc C G hGC A hA hfin δ hδ E hE
  exact ((hNT.symm hc).trans hc hRaw).trans hc hNE

end IntegrationInACVF.Section7.GammaNamed
