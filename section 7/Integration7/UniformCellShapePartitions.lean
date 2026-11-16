module

public import Integration7.UniformCellRVParadigmPartitions
public import Integration7.UniformNonrectangleCellAlternatives

@[expose] public section

/-! The actual uniform cell family splits over its retained RV labels
into zero-paradigm, nonzero rectangular, and nonzero balanced parts.
Each part is original-Gamma definable. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section5
open IntegrationInACVF.Section4

namespace IntegrationInACVF.Section7.UniformMixedCellPresentation
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {G : Base (M := M)} {S : Set M} {m : ℕ}
variable {A : DefSet (M := M) S 2 m}

def rectangularPart (F : UniformMixedCellPresentation G (carrier A)) (hNames : commonRealNames G ⊆ S) :
    Set (Point (M := M) 2 (m+F.arity)) :=
  F.nonzeroParadigmPart hNames ∩ rectangularRVPart (carrier (gammaRVGraphRefinement A F.parameters hNames))

def balancedPart (F : UniformMixedCellPresentation G (carrier A)) (hNames : commonRealNames G ⊆ S) :
    Set (Point (M := M) 2 (m+F.arity)) :=
  F.nonzeroParadigmPart hNames ∩ nonrectangularRVPart (carrier (gammaRVGraphRefinement A F.parameters hNames))

theorem rectangular_part_gamma (F : UniformMixedCellPresentation G (carrier A))
    (hNames : commonRealNames G ⊆ S) : GammaSetDefinable G (F.rectangularPart hNames) :=
  (gammaLogicInput G).inter (F.nonzero_paradigm_part_gamma hNames)
    (gamma_rectangular_rv_part (gamma_rv_graph_refinement_target_gamma A F.parameters hNames))

theorem balanced_part_gamma (F : UniformMixedCellPresentation G (carrier A))
    (hNames : commonRealNames G ⊆ S) : GammaSetDefinable G (F.balancedPart hNames) :=
  (gammaLogicInput G).inter (F.nonzero_paradigm_part_gamma hNames)
    (gamma_nonrectangular_rv_part (gamma_rv_graph_refinement_target_gamma A F.parameters hNames))

theorem shape_partition (F : UniformMixedCellPresentation G (carrier A)) (hNames : commonRealNames G ⊆ S) :
    Disjoint (F.zeroParadigmPart hNames) (F.rectangularPart hNames) ∧
    Disjoint (F.zeroParadigmPart hNames) (F.balancedPart hNames) ∧
    Disjoint (F.rectangularPart hNames) (F.balancedPart hNames) ∧
    F.zeroParadigmPart hNames ∪ F.rectangularPart hNames ∪ F.balancedPart hNames =
      carrier (gammaRVGraphRefinement A F.parameters hNames) := by
  refine ⟨Set.disjoint_left.mpr (fun p hp hq => hq.1.2 hp.2),
    Set.disjoint_left.mpr (fun p hp hq => hq.1.2 hp.2),
    Set.disjoint_left.mpr (fun p hp hq => hp.2.2 hq.2.2),?_⟩
  ext p
  change ((p ∈ carrier (gammaRVGraphRefinement A F.parameters hNames) ∧
      (Fin.elim0,p.2) ∈ F.zeroParadigmRVLabels hNames) ∨
    ((p ∈ carrier (gammaRVGraphRefinement A F.parameters hNames) ∧
      ¬ (Fin.elim0,p.2) ∈ F.zeroParadigmRVLabels hNames) ∧
    (p ∈ carrier (gammaRVGraphRefinement A F.parameters hNames) ∧
      ¬ (Fin.elim0,p.2) ∈ nonrectangleRVLabels (carrier (gammaRVGraphRefinement A F.parameters hNames))))) ∨
    ((p ∈ carrier (gammaRVGraphRefinement A F.parameters hNames) ∧
      ¬ (Fin.elim0,p.2) ∈ F.zeroParadigmRVLabels hNames) ∧
    (p ∈ carrier (gammaRVGraphRefinement A F.parameters hNames) ∧
      (Fin.elim0,p.2) ∈ nonrectangleRVLabels (carrier (gammaRVGraphRefinement A F.parameters hNames)))) ↔ _
  tauto

theorem refinement_paradigm_on_graph (F : UniformMixedCellPresentation G (carrier A))
    (hNames : commonRealNames G ⊆ S) (a : A) :
    F.refinementParadigm hNames (Map.toImage (gammaRVGraphRefinementMap A F.parameters hNames) a) =
      (F.vertical.projection a).val.2 F.vertical.paradigm_index := by
  simp only [refinementParadigm,refinementSource,Map.inverse_apply]

theorem balanced_part_row (F : UniformMixedCellPresentation G (carrier A))
    (hNames : commonRealNames G ⊆ S) (γ : Values.Gamma (M := M)) (hγ : 1 < γ) (a : A)
    (ha : (Map.toImage (gammaRVGraphRefinementMap A F.parameters hNames) a).val ∈ F.balancedPart hNames) :
    ∃ r : RV (M := M), Cells.IsBalanced (mixedPairFibre F.parameters a) (F.localPosition a) r
      ((F.vertical.projection a).val.2 F.vertical.paradigm_index) := by
  apply F.nonrectangular_nonzero_row_balanced hNames γ hγ a ha.2.2
  intro ht
  apply ha.1.2
  apply (F.mem_zero_paradigm_rv_labels hNames _).mpr
  exact (F.refinement_paradigm_on_graph hNames a).trans ht

theorem rectangular_part_fibres_are_products (F : UniformMixedCellPresentation G (carrier A))
    (hNames : commonRealNames G ⊆ S) (r : Fin (m+F.arity) → RV (M := M)) :
    let R := ParameterizedCells.twoFibre (F.rectangularPart hNames) r
    R = Cells.first R ×ˢ Cells.second R := by
  intro R
  apply (relation_eq_projection_product_iff R).mpr
  intro p hp q hq
  have hCross := (relation_eq_projection_product_iff _).mp
    (rectangular_part_fibre_is_product (carrier (gammaRVGraphRefinement A F.parameters hNames)) r) p hp.2 q hq.2
  exact ⟨⟨hCross.1,hp.1.2⟩,hCross⟩

end IntegrationInACVF.Section7.UniformMixedCellPresentation
