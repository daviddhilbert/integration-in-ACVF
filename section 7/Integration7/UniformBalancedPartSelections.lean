module

public import Integration7.UniformCellShapePartitions
public import Integration7.UniformSelectedCellPresentations
public import Integration7.GammaRVPartImages

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! The balanced geometric part is an actual whole-parameter selection
of the original uniform chart. Its selected presentation satisfies
BalancedRows by proof, rather than by an additional balanced-case premise. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section5
open IntegrationInACVF.Section4 IntegrationInACVF.Section5

namespace IntegrationInACVF.Section7.UniformMixedCellPresentation
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {G : Base (M := M)} {S : Set M} {m : ℕ}
variable {A : DefSet (M := M) S 2 m}

private theorem balanced_labels_transfer (F : UniformMixedCellPresentation G (carrier A))
    (hNames : commonRealNames G ⊆ S) (p q : gammaRVGraphRefinement A F.parameters hNames)
    (hRV : p.val.2 = q.val.2) (hp : p.val ∈ F.balancedPart hNames) : q.val ∈ F.balancedPart hNames := by
  have hLabels : ((Fin.elim0,p.val.2) : Point (M := M) 0 (m+F.arity)) = (Fin.elim0,q.val.2) := Prod.ext rfl hRV
  have hZero := congrArg (fun r => r ∈ F.zeroParadigmRVLabels hNames) hLabels
  have hBad := congrArg (fun r => r ∈ nonrectangleRVLabels (carrier (gammaRVGraphRefinement A F.parameters hNames))) hLabels
  exact ⟨⟨q.property,fun hq => hp.1.2 (Eq.mpr hZero hq)⟩,q.property,Eq.mp hBad hp.2.2⟩

def balancedSource (F : UniformMixedCellPresentation G (carrier A)) (hNames : commonRealNames G ⊆ S) :
    Set (Point (M := M) 2 m) :=
  {p | ∃ a : A, a.val=p ∧ (gammaRVGraphRefinementMap A F.parameters hNames a).val ∈ F.balancedPart hNames}

theorem balanced_source_gamma (F : UniformMixedCellPresentation G (carrier A))
    (hNames : commonRealNames G ⊆ S) : GammaSetDefinable G (F.balancedSource hNames) :=
  gamma_map_preimage (gammaRVGraphRefinementMap A F.parameters hNames)
    (gamma_rv_graph_refinement_map_gamma A F.parameters hNames) (F.balanced_part_gamma hNames)

theorem balanced_source_whole_parameters (F : UniformMixedCellPresentation G (carrier A))
    (hNames : commonRealNames G ⊆ S) (a b : A) (he : F.parameters.toFun a = F.parameters.toFun b)
    (ha : a.val ∈ F.balancedSource hNames) : b.val ∈ F.balancedSource hNames := by
  obtain ⟨c,hc,hcB⟩ := ha
  have hca : c=a := Subtype.ext hc
  subst c
  have hOld := ((sameRV_iff _ _).mp (F.parameters_reflect_same_rv a b he)).2
  exact ⟨b,rfl,F.balanced_labels_transfer hNames
    (Map.toImage (gammaRVGraphRefinementMap A F.parameters hNames) a)
    (Map.toImage (gammaRVGraphRefinementMap A F.parameters hNames) b) (congrArg₂ Fin.append hOld he) hcB⟩

def balancedParameterLabels (F : UniformMixedCellPresentation G (carrier A)) (hNames : commonRealNames G ⊆ S) :
    Set (Point (M := M) 0 F.arity) := F.parameters.partImage (F.balancedSource hNames)

theorem balanced_parameter_labels_gamma (F : UniformMixedCellPresentation G (carrier A))
    (hNames : commonRealNames G ⊆ S) : GammaSetDefinable G (F.balancedParameterLabels hNames) :=
  F.parameters.part_image_gamma (F.balanced_source_gamma hNames)

theorem balanced_parameter_selection_eq (F : UniformMixedCellPresentation G (carrier A))
    (hNames : commonRealNames G ⊆ S) :
    F.parameters.selectedDomain (F.balancedParameterLabels hNames) = F.balancedSource hNames :=
  F.parameters.selected_part_image_eq _
    (by rintro p ⟨a,ha,_⟩; exact ha ▸ a.property) (F.balanced_source_whole_parameters hNames)

theorem selected_balanced_source_mem (F : UniformMixedCellPresentation G (carrier A))
    (hNames : commonRealNames G ⊆ S) (a : F.parameters.selectedDomain (F.balancedParameterLabels hNames)) :
    (Map.toImage (gammaRVGraphRefinementMap A F.parameters hNames)
      (F.parameters.selectedInclusion (F.balancedParameterLabels hNames) a)).val ∈ F.balancedPart hNames := by
  have ha : a.val ∈ F.balancedSource hNames := (F.balanced_parameter_selection_eq hNames) ▸ a.property
  obtain ⟨b,hb,hB⟩ := ha
  have he : b = F.parameters.selectedInclusion (F.balancedParameterLabels hNames) a := Subtype.ext hb
  exact (congrArg (fun b => (gammaRVGraphRefinementMap A F.parameters hNames b).val ∈ F.balancedPart hNames) he).mp hB

set_option maxHeartbeats 1600000 in
theorem balanced_parameter_selection_rows (F : UniformMixedCellPresentation G (carrier A))
    (hNames : commonRealNames G ⊆ S) (γ : Values.Gamma (M := M)) (hγ : 1 < γ) :
    (F.select (F.balancedParameterLabels hNames) (F.balanced_parameter_labels_gamma hNames)).BalancedRows := by
  apply F.selected_nonrectangle_nonzero_balanced_rows _ _ γ hγ
  · intro a
    let a₀ := F.parameters.selectedInclusion (F.balancedParameterLabels hNames) a
    have hB := F.selected_balanced_source_mem hNames a
    have hNot := (nonrectangle_labels_iff_fibre_not_product _ _).mp hB.2.2
    have hFibre := gamma_rv_graph_refinement_two_fibre A F.parameters hNames
      (fun a b he => F.parameters_reflect_same_rv a b he) a₀
    exact Eq.mp (congrArg (fun R => R ≠ Cells.first R ×ˢ Cells.second R) hFibre) hNot
  · intro a ht
    have hB := F.selected_balanced_source_mem hNames a
    apply hB.1.2
    apply (F.mem_zero_paradigm_rv_labels hNames _).mpr
    exact (F.refinement_paradigm_on_graph hNames _).trans ht

end IntegrationInACVF.Section7.UniformMixedCellPresentation
