import Integration7.StandardTargetRestrictionPresentations
import Integration7.UniformCellPartitionLabelCuts

/-! Each actual specified contraction of the entire graph family has
constructed restrictions to all three actual partition pieces, with
its original target arity and all selected volume coordinates retained. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section5
open IntegrationInACVF.Section5

namespace IntegrationInACVF.Section7.UniformMixedCellPresentation
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {G : Base (M := M)} {S : Set M} {m : ℕ}
variable {A : DefSet (M := M) S 2 m} {σ : Equiv.Perm (Fin 2)}

theorem zero_part_contraction_presentation (F : UniformMixedCellPresentation G (carrier A))
    (hNames : commonRealNames G ⊆ S)
    (C : StandardContraction (gammaRVGraphRefinement A F.parameters hNames) σ)
    (hC : GammaProgramDefinable G C.program) :
    Nonempty (StandardTargetRestrictionPresentation (G := G) C (F.zeroNativePart hNames)
      (rvLabelCut C.target (gamma_program_final_set C.program hC) (suffixIndex C.program.rvArity_le)
        (F.zeroParadigmRVLabels hNames) (F.zero_paradigm_rv_labels_gamma hNames) hNames)) :=
  standard_label_cut_presentation_on_equal_source C (gamma_rv_graph_refinement_target_gamma A F.parameters hNames)
    hC id (F.zeroParadigmRVLabels hNames) (F.zero_paradigm_rv_labels_gamma hNames) hNames _
    (F.zero_native_part_eq_label_cut hNames)

theorem rectangular_part_contraction_presentation (F : UniformMixedCellPresentation G (carrier A))
    (hNames : commonRealNames G ⊆ S)
    (C : StandardContraction (gammaRVGraphRefinement A F.parameters hNames) σ)
    (hC : GammaProgramDefinable G C.program) :
    Nonempty (StandardTargetRestrictionPresentation (G := G) C (F.rectangularNativePart hNames)
      (rvLabelCut C.target (gamma_program_final_set C.program hC) (suffixIndex C.program.rvArity_le)
        (F.rectangularPartRVLabels hNames) (F.rectangular_part_rv_labels_gamma hNames) hNames)) :=
  standard_label_cut_presentation_on_equal_source C (gamma_rv_graph_refinement_target_gamma A F.parameters hNames)
    hC id (F.rectangularPartRVLabels hNames) (F.rectangular_part_rv_labels_gamma hNames) hNames _
    (F.rectangular_native_part_eq_label_cut hNames)

theorem balanced_part_contraction_presentation (F : UniformMixedCellPresentation G (carrier A))
    (hNames : commonRealNames G ⊆ S)
    (C : StandardContraction (gammaRVGraphRefinement A F.parameters hNames) σ)
    (hC : GammaProgramDefinable G C.program) :
    Nonempty (StandardTargetRestrictionPresentation (G := G) C (F.balancedNativeRefinement hNames)
      (rvLabelCut C.target (gamma_program_final_set C.program hC) (suffixIndex C.program.rvArity_le)
        (F.balancedPartRVLabels hNames) (F.balanced_part_rv_labels_gamma hNames) hNames)) :=
  standard_label_cut_presentation_on_equal_source C (gamma_rv_graph_refinement_target_gamma A F.parameters hNames)
    hC id (F.balancedPartRVLabels hNames) (F.balanced_part_rv_labels_gamma hNames) hNames _
    (F.balanced_native_refinement_eq_label_cut hNames)

end IntegrationInACVF.Section7.UniformMixedCellPresentation
