import Integration7.GammaNamedSelectedComparisons
import Integration7.SelectedCommonHeadOrderComparison
import Integration7.GammaRVMapRestrictions

/-! Gamma-named common-head induction step for selected standard contraction
volume objects. The first head of a Gamma contraction program, its contracted
set, the appended head–tail programs and the appended head volume chart all
receive Gamma certificates over the arbitrary Gamma base `G`. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section5
open IntegrationInACVF.Section5 IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7.GammaNamed
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n a d : ℕ}

theorem gamma_standard_first_head {G : Base (M := M)} {S : Set M}
    {A : SpecialTransformations.Section5.DefSet (M := M) S (n+1) a}
    {σ : Equiv.Perm (Fin (n+1))} (T : StandardContraction A σ)
    (hT : GammaProgramDefinable G T.program) :
    GammaGraphDefinable G (pointMapGraph (standardFirstHead T).map) ∧
      GammaSetDefinable G (carrier (standardFirstHead T).target) ∧
      GammaSetDefinable G (carrier (standardFirstHead T).contractedSet) := by
  obtain ⟨r,B,P⟩ := T
  cases P with
  | step H tail =>
    exact ⟨hT.1,hT.2.1,gamma_headImage _ hT.2.1⟩

theorem gamma_standard_change_order {G : Base (M := M)} {S : Set M}
    {A : SpecialTransformations.Section5.DefSet (M := M) S n a} {σ υ : Equiv.Perm (Fin n)}
    (T : StandardContraction A σ) (h : σ = υ) (hT : GammaProgramDefinable G T.program) :
    GammaProgramDefinable G (standardChangeOrder T h).program :=
  gamma_orderedCastSource _ _ hT

theorem gamma_head_tail_appended_standard_program {G : Base (M := M)} {S : Set M}
    {A : SpecialTransformations.Section5.DefSet (M := M) S (n+1) a}
    (σ : Equiv.Perm (Fin (n+1))) (hA : GammaSetDefinable G (carrier A))
    (T : HeadPreparation (vfPermutationImage A σ))
    (hTmap : GammaGraphDefinable G (pointMapGraph T.map))
    (hTtarget : GammaSetDefinable G (carrier T.target))
    (τ : Equiv.Perm (Fin n)) (D : StandardContraction T.contractedSet τ)
    (hD : GammaProgramDefinable G D.program) :
    GammaProgramDefinable G (headTailAppendedStandardProgram σ T τ D).program :=
  gamma_standardFromProgram _ _ _ _
    ⟨HeadPreparation.gamma_permute_tail_map T τ (gamma_vfPermutationImage A hA σ) hTtarget hTmap,
      HeadPreparation.gamma_permute_tail_target T τ hTtarget,gamma_orderedCastSource _ _ hD⟩

theorem appended_head_volume_iso_gamma
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M) (G : Base (M := M))
    (A : SpecialTransformations.Section5.DefSet (M := M) (C.base : Set M) (n+2) a)
    (σ : Equiv.Perm (Fin (n+2))) (T : HeadPreparation (vfPermutationImage A σ))
    (ρ : Fin d → Fin a) (δ : Fin a)
    (hδ : ∀ p ∈ carrier A, (p.2 δ).val ≠ iRVZero)
    (hfin : ∀ (x : Fin (n+2) → VF (M := M)) (t : Fin d → RV (M := M)),
      {r : Fin a → RV (M := M) | (x,r) ∈ carrier A ∧ r ∘ ρ = t}.Finite)
    (hδT : ∀ p ∈ carrier T.contractedSet,
      (p.2 (Fin.natAdd 1 (suffixIndex (specialRelative_rvArity_le T.special) δ))).val ≠ iRVZero)
    (hfinT : ∀ (x : Fin (n+1) → VF (M := M)) (t : Fin (1+d) → RV (M := M)),
      {r : Fin (1+T.arity) → RV (M := M) | (x,r) ∈ carrier T.contractedSet ∧ r ∘ headVolumeIndex T ρ = t}.Finite)
    (τ : Equiv.Perm (Fin (n+1))) (D : StandardContraction T.contractedSet τ)
    (hR : VolumeObjectGamma (selectedStandardVolumeObject hc C G.gamma T.contractedSet (headVolumeIndex T ρ)
      (Fin.natAdd 1 (suffixIndex (specialRelative_rvArity_le T.special) δ)) hδT hfinT D) G) :
    (appendedHeadVolumeIso hc C G.gamma A σ T ρ δ hδ hfin hδT hfinT τ D).GammaDefinable G := by
  have hU := (hR.reindexDegree (appended_head_volume_object_degree n d)).permuteVolume hc
    (headVolumeOrderPermutation d σ)
  exact gamma_volume_iso_of_full_map _ _ (gamma_essential_volume_domain _ hU.coordinates)
    ((RVMapGamma.identity hc hU.domain_graph).congr (fun _ => rfl)) (fun _ => rfl)

set_option maxHeartbeats 2400000 in
theorem selected_common_head_order_comparison
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (G : Base (M := M)) (hGC : G.real ⊆ (C.base : Set M)) (hΞ : Cardinal.mk G.gamma < C.κ)
    (hGenerated : VFGammaGeneratedBase G)
    (hGeneric : ∀ {p : ℕ} (x : Fin p → VF (M := M)), AlgebraicIndependent (vfParameterField G.real) x →
      AlgebraicIndependent (vfParameterField (C.base : Set M)) x)
    (γ : Values.Gamma (M := M)) (hγ : γ ∈ G.gamma) (hγ1 : 1 < γ)
    (ih : SelectedVolumeOrderIndependent hc C G n)
    (A : SpecialTransformations.Section5.DefSet (M := M) (C.base : Set M) (n+2) a)
    (hA : GammaSetDefinable G (carrier A)) (ρ : Fin d → Fin a) (δ : Fin a)
    (hδ : ∀ p ∈ carrier A, (p.2 δ).val ≠ iRVZero)
    (hfin : ∀ (x : Fin (n+2) → VF (M := M)) (t : Fin d → RV (M := M)),
      {r : Fin a → RV (M := M) | (x,r) ∈ carrier A ∧ r ∘ ρ = t}.Finite)
    (σ υ : Equiv.Perm (Fin (n+2))) (h0 : σ 0 = υ 0)
    (T : StandardContraction A σ) (E : StandardContraction A υ)
    (hT : GammaProgramDefinable G T.program) (hE : GammaProgramDefinable G E.program) :
    CommonContextVolumeEquivalent G C
      ⟨selectedStandardVolumeObject hc C G.gamma A ρ δ hδ hfin T,
        selected_standard_volume_object_gamma hc C G.gamma G A ρ δ hδ hfin T hT⟩
      ⟨selectedStandardVolumeObject hc C G.gamma A ρ δ hδ hfin E,
        selected_standard_volume_object_gamma hc C G.gamma G A ρ δ hδ hfin E hE⟩ := by
  have hreal : Cardinal.mk G.real < C.κ := (Cardinal.mk_le_mk_of_subset hGC).trans_lt C.small
  obtain ⟨τ,hOrder⟩ := contractionOrders_common_head σ υ h0
  let H := standardFirstHead T
  obtain ⟨hHmap,hHtarget,hA'⟩ := gamma_standard_first_head T hT
  let A' := H.contractedSet
  let ρ' := headVolumeIndex H ρ
  let δ' := Fin.natAdd 1 (suffixIndex (specialRelative_rvArity_le H.special) δ)
  have hδ' : ∀ p ∈ carrier A', (p.2 δ').val ≠ iRVZero :=
    head_retained_density_nonzero H δ (vf_permuted_retained_density_nonzero A σ δ hδ)
  have hfin' : ∀ (x : Fin (n+1) → VF (M := M)) (t : Fin (1+d) → RV (M := M)),
      {r : Fin (1+H.arity) → RV (M := M) | (x,r) ∈ carrier A' ∧ r ∘ ρ' = t}.Finite :=
    head_selected_fibres_finite (B := G) C.uncountable.le C.saturated hreal H hHmap hHtarget
      ρ (vfPermutation_selected_finite A σ ρ hfin)
  obtain ⟨D₀,hD₀,_,_,_⟩ := generated_base_standard_contraction_exists (B := G) C.saturated C.model00
    hreal hGenerated hGC A' hA' (Equiv.refl _)
  obtain ⟨Dτ,hDτ,_,_,_⟩ := generated_base_standard_contraction_exists (B := G) C.saturated C.model00
    hreal hGenerated hGC A' hA' τ
  have hR₀ := selected_standard_volume_object_gamma hc C G.gamma G A' ρ' δ' hδ' hfin' D₀ hD₀
  have hRτ := selected_standard_volume_object_gamma hc C G.gamma G A' ρ' δ' hδ' hfin' Dτ hDτ
  let R₀ : GammaVolumeObjects G (C.base : Set M) ((1+d)+n) :=
    ⟨selectedStandardVolumeObject hc C G.gamma A' ρ' δ' hδ' hfin' D₀,hR₀⟩
  let Rτ : GammaVolumeObjects G (C.base : Set M) ((1+d)+n) :=
    ⟨selectedStandardVolumeObject hc C G.gamma A' ρ' δ' hδ' hfin' Dτ,hRτ⟩
  have hRest : CommonContextVolumeEquivalent G C R₀ Rτ :=
    ih A' hA' ρ' δ' hδ' hfin' (Equiv.refl _) τ D₀ Dτ hD₀ hDτ
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
  have hF₀ : GammaProgramDefinable G F₀.program :=
    gamma_head_tail_appended_standard_program σ hA H hHmap hHtarget _ D₀ hD₀
  have hFτ : GammaProgramDefinable G Fτ.program :=
    gamma_head_tail_appended_standard_program σ hA H hHmap hHtarget _ Dτ hDτ
  let F₀' := standardChangeOrder F₀ (head_tail_identity_order σ)
  let E' := standardChangeOrder E hOrder
  have hF₀' : GammaProgramDefinable G F₀'.program := gamma_standard_change_order F₀ _ hF₀
  have hE' : GammaProgramDefinable G E'.program := gamma_standard_change_order E _ hE
  let B₀ : GammaVolumeObjects G (C.base : Set M) (d+(n+1)) :=
    ⟨selectedStandardVolumeObject hc C G.gamma A ρ δ hδ hfin F₀,
      selected_standard_volume_object_gamma hc C G.gamma G A ρ δ hδ hfin F₀ hF₀⟩
  let Bτ : GammaVolumeObjects G (C.base : Set M) (d+(n+1)) :=
    ⟨selectedStandardVolumeObject hc C G.gamma A ρ δ hδ hfin Fτ,
      selected_standard_volume_object_gamma hc C G.gamma G A ρ δ hδ hfin Fτ hFτ⟩
  let i₀ := appendedHeadVolumeIso hc C G.gamma A σ H ρ δ hδ hfin hδ' hfin' (Equiv.refl _) D₀
  let iτ := appendedHeadVolumeIso hc C G.gamma A σ H ρ δ hδ hfin hδ' hfin' τ Dτ
  have hC₀ : CommonContextVolumeEquivalent G C P₀ B₀ :=
    .of_iso i₀ (appended_head_volume_iso_gamma hc C G A σ H ρ δ hδ hfin hδ' hfin' _ D₀ hR₀)
  have hCτ : CommonContextVolumeEquivalent G C Pτ Bτ :=
    .of_iso iτ (appended_head_volume_iso_gamma hc C G A σ H ρ δ hδ hfin hδ' hfin' τ Dτ hRτ)
  have hMid : CommonContextVolumeEquivalent G C B₀ Bτ := ((hC₀.symm hc).trans hc hP).trans hc hCτ
  have hLeft := selected_same_order_standard_volume_comparison hc C G hGC hΞ hGeneric γ hγ hγ1
    A hA ρ hfin δ hδ T F₀' hT hF₀'
  have hRight := selected_same_order_standard_volume_comparison hc C G hGC hΞ hGeneric γ hγ hγ1
    A hA ρ hfin δ hδ Fτ E' hFτ hE'
  have hF₀eq : (⟨selectedStandardVolumeObject hc C G.gamma A ρ δ hδ hfin F₀',
      selected_standard_volume_object_gamma hc C G.gamma G A ρ δ hδ hfin F₀' hF₀'⟩ :
        GammaVolumeObjects G (C.base : Set M) (d+(n+1))) = B₀ :=
    Subtype.ext (selected_standard_volume_object_change_order hc C G.gamma A ρ δ hδ hfin F₀
      (head_tail_identity_order σ))
  have hEeq : (⟨selectedStandardVolumeObject hc C G.gamma A ρ δ hδ hfin E',
      selected_standard_volume_object_gamma hc C G.gamma G A ρ δ hδ hfin E' hE'⟩ :
        GammaVolumeObjects G (C.base : Set M) (d+(n+1))) =
      ⟨selectedStandardVolumeObject hc C G.gamma A ρ δ hδ hfin E,
        selected_standard_volume_object_gamma hc C G.gamma G A ρ δ hδ hfin E hE⟩ :=
    Subtype.ext (selected_standard_volume_object_change_order hc C G.gamma A ρ δ hδ hfin E hOrder)
  rw [hF₀eq] at hLeft
  rw [hEeq] at hRight
  exact hLeft.trans hc (hMid.trans hc hRight)

end IntegrationInACVF.Section7.GammaNamed
