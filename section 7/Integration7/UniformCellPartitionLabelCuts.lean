module

public import Integration7.GammaRVLabelCuts
public import Integration7.NativeCellFamilyPartitionDomains

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! All three actual cell-family pieces are cuts by original RV
labels, so their specified contractions can be restricted without
adding parameters or altering their selected volume coordinates. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section5
open IntegrationInACVF.Section4 IntegrationInACVF.Section5

namespace IntegrationInACVF.Section7.UniformMixedCellPresentation
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {G : Base (M := M)} {S : Set M} {m : ℕ}
variable {A : DefSet (M := M) S 2 m}

def rectangularPartRVLabels (F : UniformMixedCellPresentation G (carrier A)) (hNames : commonRealNames G ⊆ S) :
    Set (Point (M := M) 0 (m+F.arity)) :=
  (Set.univ \ F.zeroParadigmRVLabels hNames) \
    nonrectangleRVLabels (carrier (gammaRVGraphRefinement A F.parameters hNames))

def balancedPartRVLabels (F : UniformMixedCellPresentation G (carrier A)) (hNames : commonRealNames G ⊆ S) :
    Set (Point (M := M) 0 (m+F.arity)) :=
  (Set.univ \ F.zeroParadigmRVLabels hNames) ∩
    nonrectangleRVLabels (carrier (gammaRVGraphRefinement A F.parameters hNames))

private theorem gamma_full_rv_domain (d : ℕ) : GammaSetDefinable G (Set.univ : Set (Point (M := M) 0 d)) :=
  (gammaLogicInput G).real_set _ (setDefinable (PresentedSet.univ (pointSpace (M := M) 0 d) G.real))

theorem rectangular_part_rv_labels_gamma (F : UniformMixedCellPresentation G (carrier A))
    (hNames : commonRealNames G ⊆ S) : GammaSetDefinable G (F.rectangularPartRVLabels hNames) :=
  (gammaLogicInput G).sdiff ((gammaLogicInput G).sdiff (gamma_full_rv_domain _) (F.zero_paradigm_rv_labels_gamma hNames))
    (gamma_nonrectangle_rv_labels (gamma_rv_graph_refinement_target_gamma A F.parameters hNames))

theorem balanced_part_rv_labels_gamma (F : UniformMixedCellPresentation G (carrier A))
    (hNames : commonRealNames G ⊆ S) : GammaSetDefinable G (F.balancedPartRVLabels hNames) :=
  (gammaLogicInput G).inter ((gammaLogicInput G).sdiff (gamma_full_rv_domain _) (F.zero_paradigm_rv_labels_gamma hNames))
    (gamma_nonrectangle_rv_labels (gamma_rv_graph_refinement_target_gamma A F.parameters hNames))

theorem zero_native_part_eq_label_cut (F : UniformMixedCellPresentation G (carrier A))
    (hNames : commonRealNames G ⊆ S) :
    rvLabelCut (gammaRVGraphRefinement A F.parameters hNames) (gamma_rv_graph_refinement_target_gamma A F.parameters hNames)
      id (F.zeroParadigmRVLabels hNames) (F.zero_paradigm_rv_labels_gamma hNames) hNames = F.zeroNativePart hNames := by
  apply defSet_eq_of_carrier_eq
  rfl

theorem rectangular_native_part_eq_label_cut (F : UniformMixedCellPresentation G (carrier A))
    (hNames : commonRealNames G ⊆ S) :
    rvLabelCut (gammaRVGraphRefinement A F.parameters hNames) (gamma_rv_graph_refinement_target_gamma A F.parameters hNames)
      id (F.rectangularPartRVLabels hNames) (F.rectangular_part_rv_labels_gamma hNames) hNames = F.rectangularNativePart hNames := by
  apply defSet_eq_of_carrier_eq
  ext p
  change (p ∈ carrier (gammaRVGraphRefinement A F.parameters hNames) ∧
      (((Fin.elim0,p.2) ∈ Set.univ ∧ (Fin.elim0,p.2) ∉ F.zeroParadigmRVLabels hNames) ∧
        (Fin.elim0,p.2) ∉ nonrectangleRVLabels (carrier (gammaRVGraphRefinement A F.parameters hNames)))) ↔
    ((p ∈ carrier (gammaRVGraphRefinement A F.parameters hNames) ∧ (Fin.elim0,p.2) ∉ F.zeroParadigmRVLabels hNames) ∧
      (p ∈ carrier (gammaRVGraphRefinement A F.parameters hNames) ∧
        (Fin.elim0,p.2) ∉ nonrectangleRVLabels (carrier (gammaRVGraphRefinement A F.parameters hNames))))
  simp only [Set.mem_univ,true_and]
  tauto

theorem balanced_native_refinement_eq_label_cut (F : UniformMixedCellPresentation G (carrier A))
    (hNames : commonRealNames G ⊆ S) :
    rvLabelCut (gammaRVGraphRefinement A F.parameters hNames) (gamma_rv_graph_refinement_target_gamma A F.parameters hNames)
      id (F.balancedPartRVLabels hNames) (F.balanced_part_rv_labels_gamma hNames) hNames = F.balancedNativeRefinement hNames := by
  apply defSet_eq_of_carrier_eq
  rw [F.balanced_native_refinement_carrier hNames]
  ext p
  change (p ∈ carrier (gammaRVGraphRefinement A F.parameters hNames) ∧
      (((Fin.elim0,p.2) ∈ Set.univ ∧ (Fin.elim0,p.2) ∉ F.zeroParadigmRVLabels hNames) ∧
        (Fin.elim0,p.2) ∈ nonrectangleRVLabels (carrier (gammaRVGraphRefinement A F.parameters hNames)))) ↔
    ((p ∈ carrier (gammaRVGraphRefinement A F.parameters hNames) ∧ (Fin.elim0,p.2) ∉ F.zeroParadigmRVLabels hNames) ∧
      (p ∈ carrier (gammaRVGraphRefinement A F.parameters hNames) ∧
        (Fin.elim0,p.2) ∈ nonrectangleRVLabels (carrier (gammaRVGraphRefinement A F.parameters hNames))))
  simp only [Set.mem_univ,true_and]
  tauto

end IntegrationInACVF.Section7.UniformMixedCellPresentation
