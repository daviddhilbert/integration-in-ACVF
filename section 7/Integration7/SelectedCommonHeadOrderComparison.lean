module

public import Integration7.SelectedVolumeOrderIndependence
public import Integration7.AppendedHeadVolumeCharts
public import Integration7.StandardContractionOrderTransport
public import Integration7.GeneratedBaseStandardContractions

@[expose] public section

/-! The all-order induction step for two orders sharing their first
coordinate. The selected head is retained and the smaller VF induction
is transported through actual volume charts. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section5
open IntegrationInACVF.Section5 IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n a d : ℕ}

def standardFirstHead {S : Set M} {A : DefSet (M := M) S (n+1) a}
    {σ : Equiv.Perm (Fin (n+1))} (T : StandardContraction A σ) :
    HeadPreparation (vfPermutationImage A σ) :=
  match T.program with | .step H _ => H

set_option maxHeartbeats 2400000 in
theorem selected_common_head_order_comparison
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (Ξ : Set (Values.Gamma (M := M))) (hΞ : Cardinal.mk Ξ < C.κ)
    (hGenerated : VFGammaGeneratedBase (⟨(C.base : Set M),Ξ⟩ : Base (M := M)))
    (γ : Values.Gamma (M := M)) (hγ : γ ∈ Ξ) (hγ1 : 1 < γ)
    (ih : SelectedVolumeOrderIndependent hc C Ξ n)
    (A : DefSet (M := M) (C.base : Set M) (n+2) a) (ρ : Fin d → Fin a) (δ : Fin a)
    (hδ : ∀ p ∈ carrier A, (p.2 δ).val ≠ iRVZero)
    (hfin : ∀ (x : Fin (n+2) → VF (M := M)) (t : Fin d → RV (M := M)),
      {r : Fin a → RV (M := M) | (x,r) ∈ carrier A ∧ r ∘ ρ = t}.Finite)
    (σ υ : Equiv.Perm (Fin (n+2))) (h0 : σ 0 = υ 0)
    (T : StandardContraction A σ) (E : StandardContraction A υ) :
    let G : Base (M := M) := ⟨(C.base : Set M),Ξ⟩
    CommonContextVolumeEquivalent G C
      ⟨selectedStandardVolumeObject hc C Ξ A ρ δ hδ hfin T,
        selected_standard_volume_object_gamma hc C Ξ A ρ δ hδ hfin T⟩
      ⟨selectedStandardVolumeObject hc C Ξ A ρ δ hδ hfin E,
        selected_standard_volume_object_gamma hc C Ξ A ρ δ hδ hfin E⟩ := by
  intro G
  have hBase : (C.base : Set M) = (Substructure.closure LRV G.real : Set M) := by
    change (C.base : Set M) = (Substructure.closure LRV (C.base : Set M) : Set M)
    rw [Substructure.closure_eq]
  obtain ⟨τ,hOrder⟩ := contractionOrders_common_head σ υ h0
  let H := standardFirstHead T
  let A' := H.contractedSet
  let ρ' := headVolumeIndex H ρ
  let δ' := Fin.natAdd 1 (suffixIndex (specialRelative_rvArity_le H.special) δ)
  have hA' : GammaSetDefinable G (carrier A') := (gammaLogicInput G).real_set _ (setDefinable A')
  have hδ' : ∀ p ∈ carrier A', (p.2 δ').val ≠ iRVZero :=
    head_retained_density_nonzero H δ (vf_permuted_retained_density_nonzero A σ δ hδ)
  have hfin' : ∀ (x : Fin (n+1) → VF (M := M)) (t : Fin (1+d) → RV (M := M)),
      {r : Fin (1+H.arity) → RV (M := M) | (x,r) ∈ carrier A' ∧ r ∘ ρ' = t}.Finite :=
    head_selected_fibres_finite (B := G) C.uncountable.le C.saturated C.small H
      ((gammaLogicInput G).real_map_graph H.map) ((gammaLogicInput G).real_set _ (setDefinable H.target))
      ρ (vfPermutation_selected_finite A σ ρ hfin)
  obtain ⟨D₀,hD₀,_,_,_⟩ := generated_base_standard_contraction_exists (B := G) C.saturated C.model00
    C.small hGenerated (Set.Subset.refl _) A' hA' (Equiv.refl _)
  obtain ⟨Dτ,hDτ,_,_,_⟩ := generated_base_standard_contraction_exists (B := G) C.saturated C.model00
    C.small hGenerated (Set.Subset.refl _) A' hA' τ
  let R₀ : GammaVolumeObjects G (C.base : Set M) ((1+d)+n) :=
    ⟨selectedStandardVolumeObject hc C Ξ A' ρ' δ' hδ' hfin' D₀,
      selected_standard_volume_object_gamma hc C Ξ A' ρ' δ' hδ' hfin' D₀⟩
  let Rτ : GammaVolumeObjects G (C.base : Set M) ((1+d)+n) :=
    ⟨selectedStandardVolumeObject hc C Ξ A' ρ' δ' hδ' hfin' Dτ,
      selected_standard_volume_object_gamma hc C Ξ A' ρ' δ' hδ' hfin' Dτ⟩
  have hRest : CommonContextVolumeEquivalent G C R₀ Rτ :=
    ih A' ρ' δ' hδ' hfin' (Equiv.refl _) τ D₀ Dτ
  let P₀ : GammaVolumeObjects G (C.base : Set M) (d+(n+1)) :=
    ⟨(R₀.val.reindexDegree (appended_head_volume_object_degree n d)).permuteVolume (headVolumeOrderPermutation d σ),
      (R₀.property.reindexDegree (appended_head_volume_object_degree n d)).permuteVolume hc _⟩
  let Pτ : GammaVolumeObjects G (C.base : Set M) (d+(n+1)) :=
    ⟨(Rτ.val.reindexDegree (appended_head_volume_object_degree n d)).permuteVolume (headVolumeOrderPermutation d σ),
      (Rτ.property.reindexDegree (appended_head_volume_object_degree n d)).permuteVolume hc _⟩
  have hP : CommonContextVolumeEquivalent G C P₀ Pτ :=
    (hRest.reindexDegree hc (appended_head_volume_object_degree n d)).permuteVolume hc (headVolumeOrderPermutation d σ)
  let F₀ := headTailAppendedStandardProgram σ H (Equiv.refl _) D₀
  let Fτ := headTailAppendedStandardProgram σ H τ Dτ
  let F₀' := standardChangeOrder F₀ (head_tail_identity_order σ)
  let E' := standardChangeOrder E hOrder
  let B₀ : GammaVolumeObjects G (C.base : Set M) (d+(n+1)) :=
    ⟨selectedStandardVolumeObject hc C Ξ A ρ δ hδ hfin F₀,selected_standard_volume_object_gamma hc C Ξ A ρ δ hδ hfin F₀⟩
  let Bτ : GammaVolumeObjects G (C.base : Set M) (d+(n+1)) :=
    ⟨selectedStandardVolumeObject hc C Ξ A ρ δ hδ hfin Fτ,selected_standard_volume_object_gamma hc C Ξ A ρ δ hδ hfin Fτ⟩
  let i₀ := appendedHeadVolumeIso hc C Ξ A σ H ρ δ hδ hfin hδ' hfin' (Equiv.refl _) D₀
  let iτ := appendedHeadVolumeIso hc C Ξ A σ H ρ δ hδ hfin hδ' hfin' τ Dτ
  have hC₀ : CommonContextVolumeEquivalent G C P₀ B₀ := .of_iso i₀ (i₀.gamma_of_term_context hc C hBase)
  have hCτ : CommonContextVolumeEquivalent G C Pτ Bτ := .of_iso iτ (iτ.gamma_of_term_context hc C hBase)
  have hMid : CommonContextVolumeEquivalent G C B₀ Bτ := ((hC₀.symm hc).trans hc hP).trans hc hCτ
  have hLeft := selected_same_order_standard_volume_comparison hc C Ξ hΞ γ hγ hγ1 A ρ hfin δ hδ T F₀'
  have hRight := selected_same_order_standard_volume_comparison hc C Ξ hΞ γ hγ hγ1 A ρ hfin δ hδ Fτ E'
  have hF₀ : (⟨selectedStandardVolumeObject hc C Ξ A ρ δ hδ hfin F₀',
      selected_standard_volume_object_gamma hc C Ξ A ρ δ hδ hfin F₀'⟩ : GammaVolumeObjects G (C.base : Set M) (d+(n+1))) = B₀ :=
    Subtype.ext (selected_standard_volume_object_change_order hc C Ξ A ρ δ hδ hfin F₀ (head_tail_identity_order σ))
  have hE : (⟨selectedStandardVolumeObject hc C Ξ A ρ δ hδ hfin E',
      selected_standard_volume_object_gamma hc C Ξ A ρ δ hδ hfin E'⟩ : GammaVolumeObjects G (C.base : Set M) (d+(n+1))) =
      ⟨selectedStandardVolumeObject hc C Ξ A ρ δ hδ hfin E,selected_standard_volume_object_gamma hc C Ξ A ρ δ hδ hfin E⟩ :=
    Subtype.ext (selected_standard_volume_object_change_order hc C Ξ A ρ δ hδ hfin E hOrder)
  dsimp only at hLeft hRight
  rw [hF₀] at hLeft
  rw [hE] at hRight
  exact hLeft.trans hc (hMid.trans hc hRight)

end IntegrationInACVF.Section7
