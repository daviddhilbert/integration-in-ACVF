module

public import Integration7.SelectedArbitraryContractionOrders
public import Integration7.EmptySelectedVolumeCharts
public import Integration7.RawStandardVolumeNormalization

@[expose] public section

/-! All standard contraction orders of a finite-label VF domain give
common forward volume blowups, with arbitrary retained nonzero density,
on the actual normalized contraction objects. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section5
open IntegrationInACVF.Section5 IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n a : ℕ}

set_option maxHeartbeats 1600000 in
theorem retained_density_arbitrary_order_contractions_compare
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (Ξ : Set (Values.Gamma (M := M))) (hΞ : Cardinal.mk Ξ < C.κ)
    (hGenerated : VFGammaGeneratedBase (⟨(C.base : Set M),Ξ⟩ : Base (M := M)))
    (hNames : commonRealNames (⟨(C.base : Set M),Ξ⟩ : Base (M := M)) ⊆ (C.base : Set M))
    (γ : Values.Gamma (M := M)) (hγ : γ ∈ Ξ) (hγ1 : 1 < γ)
    (A : DefSet (M := M) (C.base : Set M) (n+1) a)
    (hfin : ∀ x : Fin (n+1) → VF (M := M), {r : Fin a → RV (M := M) | (x,r) ∈ carrier A}.Finite)
    (δ : Fin a) (hδ : ∀ p ∈ carrier A, (p.2 δ).val ≠ iRVZero)
    (σ υ : Equiv.Perm (Fin (n+1))) (T : StandardContraction A σ) (E : StandardContraction A υ) :
    let G : Base (M := M) := ⟨(C.base : Set M),Ξ⟩
    let R := fun (π : Equiv.Perm (Fin (n+1))) (P : StandardContraction A π) =>
      retainedDensityContractionGammaObject C.uncountable.le C.saturated C.small hc C
        (Set.Subset.refl _) A ((gammaLogicInput G).real_set _ (setDefinable A)) hfin δ
        (fun p => hδ p.val p.property) P (gamma_program_over_real_base G P.program)
    CommonContextVolumeEquivalent G C (R σ T) (R υ E) := by
  intro G R
  have hBase : (C.base : Set M) = (Substructure.closure LRV G.real : Set M) := by
    change (C.base : Set M) = (Substructure.closure LRV (C.base : Set M) : Set M)
    rw [Substructure.closure_eq]
  let ρ : Fin 0 → Fin a := Fin.elim0
  let hfin₀ := empty_selected_volume_finite A hfin
  let PT : GammaVolumeObjects G (C.base : Set M) n :=
    GammaVolumeObjects.reindexDegree (⟨selectedStandardVolumeObject hc C Ξ A ρ δ hδ hfin₀ T,
      selected_standard_volume_object_gamma hc C Ξ A ρ δ hδ hfin₀ T⟩ :
      GammaVolumeObjects G (C.base : Set M) (0+n)) ((Nat.zero_add n).symm)
  let PE : GammaVolumeObjects G (C.base : Set M) n :=
    GammaVolumeObjects.reindexDegree (⟨selectedStandardVolumeObject hc C Ξ A ρ δ hδ hfin₀ E,
      selected_standard_volume_object_gamma hc C Ξ A ρ δ hδ hfin₀ E⟩ :
      GammaVolumeObjects G (C.base : Set M) (0+n)) ((Nat.zero_add n).symm)
  let RT : GammaVolumeObjects G (C.base : Set M) n :=
    ⟨rawStandardVolumeObject hc C Ξ A hfin δ hδ T,raw_standard_volume_object_gamma hc C Ξ A hfin δ hδ T⟩
  let RE : GammaVolumeObjects G (C.base : Set M) n :=
    ⟨rawStandardVolumeObject hc C Ξ A hfin δ hδ E,raw_standard_volume_object_gamma hc C Ξ A hfin δ hδ E⟩
  have hOrders : CommonContextVolumeEquivalent G C PT PE :=
    (selected_volume_contraction_order_independent hc C Ξ hΞ hGenerated hNames γ hγ hγ1 n
      A ρ δ hδ hfin₀ σ υ T E).reindexDegree hc ((Nat.zero_add n).symm)
  let iT := emptySelectedRawVolumeIso hc C Ξ A hfin δ hδ T
  let iE := emptySelectedRawVolumeIso hc C Ξ A hfin δ hδ E
  have hT : CommonContextVolumeEquivalent G C PT RT := .of_iso iT (iT.gamma_of_term_context hc C hBase)
  have hE : CommonContextVolumeEquivalent G C PE RE := .of_iso iE (iE.gamma_of_term_context hc C hBase)
  have hRaw : CommonContextVolumeEquivalent G C RT RE := ((hT.symm hc).trans hc hOrders).trans hc hE
  have hNT := raw_standard_volume_normalization hc C Ξ A hfin δ hδ T
  have hNE := raw_standard_volume_normalization hc C Ξ A hfin δ hδ E
  exact ((hNT.symm hc).trans hc hRaw).trans hc hNE

end IntegrationInACVF.Section7
