import IntegrationSection6.OrderedFibrewiseContractions
import IntegrationSection6.GammaPermutedFibrePresentations
import IntegrationSection6.GammaContractionPresentationIsomorphisms
import IntegrationSection6.SmallVFFieldBases

/-! Lemma6.14 in RV[k], for arbitrary VF arity and any common coordinate
order. Finiteness is required only after fixing the VF tuple and the selected
old RV labels. Both arbitrary standard contractions are actual programs. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
open IntegrationInACVF.Section5
namespace IntegrationInACVF.Section6.FiniteRV
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {S : Set M} {n a b k : ℕ}

theorem lemma_6_14_uncountable {κ : Cardinal} (hκ : Cardinal.aleph0 < κ)
    (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (hreal : Cardinal.mk B.real < κ) (hgamma : Cardinal.mk B.gamma < κ)
    (δ : Values.Gamma (M := M)) (hδ : δ ∈ B.gamma) (hδ1 : 1 < δ)
    (hBS : B.real ⊆ S)
    (U : DefSet (M := M) S n a) (V : DefSet (M := M) S n b)
    (hU : GammaSetDefinable B (carrier U)) (hV : GammaSetDefinable B (carrier V))
    (ρ : Fin k → Fin a) (τ : Fin k → Fin b)
    (hfinU : ∀ (x : Fin n → VF (M := M)) (t : Fin k → RV (M := M)),
      {r : Fin a → RV (M := M) | (x,r) ∈ carrier U ∧ r ∘ ρ = t}.Finite)
    (hfinV : ∀ (x : Fin n → VF (M := M)) (t : Fin k → RV (M := M)),
      {r : Fin b → RV (M := M) | (x,r) ∈ carrier V ∧ r ∘ τ = t}.Finite)
    (hCommon : ∀ x : Fin n → VF (M := M),
      ∀ P : SelectedLabelFibrePresentation B U ρ x, ∀ Q : SelectedLabelFibrePresentation B V τ x,
      GammaIsp hκ.le hs h00 (small_union_range hκ.le B.real hreal (fun j => (x j).val)) P.toGamma Q.toGamma)
    {σ : Equiv.Perm (Fin n)} (T : StandardContraction U σ) (E : StandardContraction V σ)
    (hT : GammaProgramDefinable B T.program) (hE : GammaProgramDefinable B E.program) :
    GammaIsp hκ.le hs h00 hreal (gammaFiniteSelectedContraction hκ.le hs hreal hBS hU ρ hfinU T hT)
      (gammaFiniteSelectedContraction hκ.le hs hreal hBS hV τ hfinV E hE) := by
  have hFU := vfPermutation_selected_finite U σ ρ hfinU
  have hFV := vfPermutation_selected_finite V σ τ hfinV
  obtain ⟨P⟩ := gammaSelectedRVPresentation_exists T.target (gamma_program_final_set T.program hT)
    (orderedSelectedIndex T.program ρ) (ordered_selected_fibres_finite hκ.le hs hreal T.program hT ρ hFU)
  obtain ⟨Q⟩ := gammaSelectedRVPresentation_exists E.target (gamma_program_final_set E.program hE)
    (orderedSelectedIndex E.program τ) (ordered_selected_fibres_finite hκ.le hs hreal E.program hE τ hFV)
  have h := lemma_6_14_ordered hκ hs h00 hreal hgamma δ hδ hδ1
    (vfPermutationImage U σ) (vfPermutationImage V σ)
    (gamma_vfPermutationImage U hU σ) (gamma_vfPermutationImage V hV σ) ρ τ hFU hFV
    (fun x LP LQ => gamma_permuted_pointwise_comparison hκ.le hs h00 hreal U V σ ρ τ hCommon x LP LQ)
    T.program E.program hT hE P Q
  have h' := h.corollary_6_6
    (gammaIsoSymm (gammaContractionPresentationIso hκ.le hs hreal hBS hU ρ hfinU T hT P))
    (gammaIsoSymm (gammaContractionPresentationIso hκ.le hs hreal hBS hV τ hfinV E hE Q))
  have h'' := h'.castDegree (orderedVolumeDegree_eq n k)
  simpa only [gammaCastDegree_symm] using h''

theorem lemma_6_14 {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (hreal : Cardinal.mk B.real < κ) (hgamma : Cardinal.mk B.gamma < κ)
    (δ : Values.Gamma (M := M)) (hδ : δ ∈ B.gamma) (hδ1 : 1 < δ) (FBase : VFFieldBase B.real)
    (hBS : B.real ⊆ S)
    (U : DefSet (M := M) S n a) (V : DefSet (M := M) S n b)
    (hU : GammaSetDefinable B (carrier U)) (hV : GammaSetDefinable B (carrier V))
    (ρ : Fin k → Fin a) (τ : Fin k → Fin b)
    (hfinU : ∀ (x : Fin n → VF (M := M)) (t : Fin k → RV (M := M)),
      {r : Fin a → RV (M := M) | (x,r) ∈ carrier U ∧ r ∘ ρ = t}.Finite)
    (hfinV : ∀ (x : Fin n → VF (M := M)) (t : Fin k → RV (M := M)),
      {r : Fin b → RV (M := M) | (x,r) ∈ carrier V ∧ r ∘ τ = t}.Finite)
    (hCommon : ∀ x : Fin n → VF (M := M),
      ∀ P : SelectedLabelFibrePresentation B U ρ x, ∀ Q : SelectedLabelFibrePresentation B V τ x,
      GammaIsp hκ hs h00 (small_union_range hκ B.real hreal (fun j => (x j).val)) P.toGamma Q.toGamma)
    {σ : Equiv.Perm (Fin n)} (T : StandardContraction U σ) (E : StandardContraction V σ)
    (hT : GammaProgramDefinable B T.program) (hE : GammaProgramDefinable B E.program) :
    GammaIsp hκ hs h00 hreal (gammaFiniteSelectedContraction hκ hs hreal hBS hU ρ hfinU T hT)
      (gammaFiniteSelectedContraction hκ hs hreal hBS hV τ hfinV E hE) :=
  lemma_6_14_uncountable (aleph0_lt_of_small_vf_field_base h00 FBase hreal) hs h00
    hreal hgamma δ hδ hδ1 hBS U V hU hV ρ τ hfinU hfinV hCommon T E hT hE

end IntegrationInACVF.Section6.FiniteRV
