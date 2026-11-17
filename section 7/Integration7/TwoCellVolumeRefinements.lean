module

public import Integration7.MixedCellGraphRefinements
public import Integration7.NativeRVGraphVolumeRefinements

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! The actual refinement step in Lemma7.7: a positive VF²-volume object
has a VF-preserving, relatively unary graph refinement into a definable
two-cell family. Every old label and its selected density are retained. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section5 SpecialTransformations.Section9
open IntegrationInACVF.Section4 IntegrationInACVF.Section5

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {G : Base (M := M)} {m : ℕ}

theorem two_cell_volume_refinement_exists
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (hsmall : Cardinal.mk G.real < C.κ) (hGenerated : VFGammaGeneratedBase G)
    (δ : Values.Gamma (M := M)) (hδ : δ ∈ G.gamma) (hδ1 : 1 < δ)
    (A : DefSet (M := M) (C.base : Set M) 2 m) (hA : GammaSetDefinable G (carrier A))
    (hfin : ∀ x : Fin 2 → VF (M := M), {r : Fin m → RV (M := M) | (x,r) ∈ carrier A}.Finite)
    (hNames : commonRealNames G ⊆ (C.base : Set M))
    (ω : VolumeForm (rawSpecialSet hc A)) (j : Fin m) (hω : ∀ p, ω.value p = p.val.2 j) :
    ∃ d : ℕ, ∃ P : GammaRVMap G (carrier A) d,
      ParameterizedCells.DefinableTwoCell G (carrier (gammaRVGraphRefinement A P hNames)) ∧
      Function.Bijective (Map.toImage (gammaRVGraphRefinementMap A P hNames)) ∧
      GammaGraphDefinable G (pointMapGraph (Map.toImage (gammaRVGraphRefinementMap A P hNames))) ∧
      (∀ i : Fin 2, UnaryRelative (Map.toImage (gammaRVGraphRefinementMap A P hNames)) i) ∧
      (∀ a : A, retainVFLabels (Fin.castAdd d) (Map.toImage (gammaRVGraphRefinementMap A P hNames) a).val = a.val) ∧
      Nonempty (VFVolumeBijection (nativeMixedVFVolumeObject hc A hfin ω)
        (nativeRVGraphVolumeRefinement hc A hfin P hNames ω)) ∧
      ∀ q : (nativeRVGraphVolumeRefinement hc A hfin P hNames ω).domain,
        (nativeRVGraphVolumeRefinement hc A hfin P hNames ω).form.value q = q.val.2 (Fin.castAdd d j) := by
  obtain ⟨d,P,hCell⟩ := gamma_two_cell_graph_refinement_exists C.uncountable.le C.saturated C.model00
    hsmall hGenerated δ hδ hδ1 A hA hNames
  exact ⟨d,P,hCell,gamma_rv_graph_refinement_bijective A P hNames,
    gamma_rv_graph_refinement_map_gamma A P hNames,gamma_rv_graph_refinement_unary_relative A P hNames,
    gamma_rv_graph_refinement_retains_labels A P hNames,
    ⟨nativeRVGraphVolumeBijection hc C A hfin P hNames ω⟩,
    native_rv_graph_refinement_retained_density hc A hfin P hNames ω j hω⟩

end IntegrationInACVF.Section7
