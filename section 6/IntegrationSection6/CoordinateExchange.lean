import IntegrationSection6.OrderedTwoCoordinateExchange
import IntegrationSection6.VFPrefixSwaps
import IntegrationSection6.PermutationFiniteFibres
import IntegrationSection6.SmallVFFieldBases

/-! Lemma6.16 in the finite RV categories for arbitrary VF arity. The
first two contraction coordinates are exchanged and every later coordinate
has the same order. Only the unfinished Section5.8 theorem is an input. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5 SpecialTransformations.Section7
open IntegrationInACVF.Section5
namespace IntegrationInACVF.Section6.FiniteRV
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {S : Set M} {n a : ℕ}

theorem lemma_6_16_uncountable {κ : Cardinal} (hκ : Cardinal.aleph0 < κ)
    (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (hreal : Cardinal.mk B.real < κ) (hgamma : Cardinal.mk B.gamma < κ)
    (δ : Values.Gamma (M := M)) (hδ : δ ∈ B.gamma) (hδ1 : 1 < δ) (hBS : B.real ⊆ S)
    (h58 : ∀ x : Fin n → VF (M := M),
      Section5TwoOrderInput ⟨B.real ∪ Set.range (fun j => (x j).val),B.gamma⟩ hκ.le hs
        (small_union_range hκ.le B.real hreal (fun j => (x j).val)))
    (U : DefSet (M := M) S (n+2) a) (hU : GammaSetDefinable B (carrier U))
    (hfinU : ∀ y : Fin (n+2) → VF (M := M), {s : Fin a → RV (M := M) | (y,s) ∈ carrier U}.Finite)
    {σ : Equiv.Perm (Fin (n+2))}
    (T : StandardContraction U σ) (E : StandardContraction U ((swapFirstTwo n).trans σ))
    (hT : GammaProgramDefinable B T.program) (hE : GammaProgramDefinable B E.program) :
    GammaIsp hκ.le hs h00 hreal (gammaFiniteContraction hκ.le hs hreal hBS hU hfinU T hT)
      (gammaFiniteContraction hκ.le hs hreal hBS hU hfinU E hE) := by
  have hFU := vfPermutation_finite_rv_fibres U σ hfinU
  have hFW := vfPermutation_finite_rv_fibres U ((swapFirstTwo n).trans σ) hfinU
  obtain ⟨P⟩ := gammaSelectedRVPresentation_exists T.target (gamma_program_final_set T.program hT)
    (orderedSelectedIndex T.program (Fin.elim0 : Fin 0 → Fin a))
    (ordered_selected_fibres_finite hκ.le hs hreal T.program hT Fin.elim0
      (empty_selected_fibres (vfPermutationImage U σ) hFU))
  obtain ⟨Q⟩ := gammaSelectedRVPresentation_exists E.target (gamma_program_final_set E.program hE)
    (orderedSelectedIndex E.program (Fin.elim0 : Fin 0 → Fin a))
    (ordered_selected_fibres_finite hκ.le hs hreal E.program hE Fin.elim0
      (empty_selected_fibres (vfPermutationImage U ((swapFirstTwo n).trans σ)) hFW))
  have h := gamma_ordered_two_exchange hκ hs h00 hreal hgamma δ hδ hδ1 hBS
    (gamma_vfPermutationImage U hU σ) hFU hFW h58 (vfPrefix_permuted_swap U σ)
    T.program E.program hT hE P Q
  have h' := h.corollary_6_6
    (gammaIsoSymm (gammaOrdinaryContractionPresentationIso hκ.le hs hreal hBS hU hfinU T hT P))
    (gammaIsoSymm (gammaOrdinaryContractionPresentationIso hκ.le hs hreal hBS hU hfinU E hE Q))
  have h'' := h'.castDegree (orderedVolumeDegree_eq (n+2) 0)
  simpa only [gammaCastDegree_symm] using h''

end IntegrationInACVF.Section6.FiniteRV
