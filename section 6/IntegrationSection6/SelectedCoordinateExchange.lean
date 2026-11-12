import IntegrationSection6.SelectedSliceContractionComparison
import IntegrationSection6.CoordinateExchange
import IntegrationSection6.GammaVolumeSliceUniformity
import IntegrationSection6.GammaSwappedCommonBlowups

/-! Lemma6.16 with selected original RV volume coordinates. Only fixing
VF together with these selected labels must give finite fibres. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5 SpecialTransformations.Section7
open IntegrationInACVF.Section5
namespace IntegrationInACVF.Section6.FiniteRV
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {n a k : ℕ}

theorem lemma_6_16_selected_univ {κ : Cardinal} (hκ : Cardinal.aleph0 < κ)
    (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (hreal : Cardinal.mk B.real < κ) (hgamma : Cardinal.mk B.gamma < κ)
    (δ : Values.Gamma (M := M)) (hδ : δ ∈ B.gamma) (hδ1 : 1 < δ)
    (h58 : ∀ (t : Fin k → RV (M := M)) (x : Fin n → VF (M := M)),
      Section5TwoOrderInput
        ⟨(B.real ∪ Set.range (fun j => (t j).val)) ∪ Set.range (fun j => (x j).val),B.gamma⟩ hκ.le hs
        (small_union_range hκ.le _ (small_union_range hκ.le B.real hreal (fun j => (t j).val)) (fun j => (x j).val)))
    (U : DefSet (M := M) Set.univ (n+2) a) (hU : GammaSetDefinable B (carrier U))
    (ρ : Fin k → Fin a)
    (hfin : ∀ (x : Fin (n+2) → VF (M := M)) (t : Fin k → RV (M := M)),
      {r : Fin a → RV (M := M) | (x,r) ∈ carrier U ∧ r ∘ ρ = t}.Finite)
    {σ : Equiv.Perm (Fin (n+2))}
    (C : StandardContraction U σ) (E : StandardContraction U ((swapFirstTwo n).trans σ))
    (hC : GammaProgramDefinable B C.program) (hE : GammaProgramDefinable B E.program) :
    GammaIsp hκ.le hs h00 hreal
      (gammaFiniteSelectedContraction hκ.le hs hreal (Set.subset_univ _) hU ρ hfin C hC)
      (gammaFiniteSelectedContraction hκ.le hs hreal (Set.subset_univ _) hU ρ hfin E hE) := by
  have H : GammaIsp hκ.le hs h00 hreal
      (gammaPrependSelectedContraction hκ.le hs hreal (Set.subset_univ _) hU ρ hfin C hC)
      (gammaPrependSelectedContraction hκ.le hs hreal (Set.subset_univ _) hU ρ hfin E hE) := by
    apply gamma_volume_slice_common_uniformity hκ.le hs h00 hreal hgamma
    intro t P Q
    obtain ⟨D⟩ := restrictedStandardData_exists C hU hC ρ t
    obtain ⟨F⟩ := restrictedStandardData_exists E hU hE ρ t
    obtain ⟨f⟩ := selectedSliceContractionComparison hκ.le hs hreal hU ρ hfin C hC t D P
    obtain ⟨g⟩ := selectedSliceContractionComparison hκ.le hs hreal hU ρ hfin E hE t F Q
    have h := lemma_6_16_uncountable (B := ⟨B.real ∪ Set.range (fun j => (t j).val),B.gamma⟩)
      hκ hs h00 (small_union_range hκ.le B.real hreal (fun j => (t j).val)) hgamma
      δ hδ hδ1 (Set.subset_univ _) (h58 t) (rvLabelSlice U hU ρ t)
      (rvLabelSlice_gamma U hU ρ t) (rvLabelSlice_finite U hU ρ hfin t)
      D.contraction F.contraction D.gamma F.gamma
    exact h.corollary_6_6 f g
  exact GammaIsp.of_swapVolumeBlocks H

end IntegrationInACVF.Section6.FiniteRV
