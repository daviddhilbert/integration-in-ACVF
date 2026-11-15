import Integration7.UniformCellPositionRows
import Integration7.RVLabelRectangularFibres
import Integration7.MixedCellGraphRefinements
import IntegrationSection4.CellRectangles

/-! Nonrectangular nonzero-paradigm fibres of the uniform cell chart
are balanced for that chart's actual local position. The rectangle
alternative is excluded by the original-Gamma RV-label partition. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section5
open IntegrationInACVF.Section4

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {G : Base (M := M)} {m : ℕ}

theorem nonrectangle_nonzero_cell_balanced
    (γ : Values.Gamma (M := M)) (hγ : 1 < γ)
    {R : Set (VF (M := M) × VF (M := M))} {f : VF (M := M) → VF (M := M)} {t : RV (M := M)}
    (hCell : Cells.CellData R f t) (ht : t ≠ rv (0 : VF (M := M)))
    (hNot : R ≠ Cells.first R ×ˢ Cells.second R) :
    ∃ r : RV (M := M), Cells.IsBalanced R f r t := by
  by_contra hNo
  obtain ⟨E,hE,hRect⟩ := CellRectangles.rectangle γ hγ hCell ht hNo
  apply hNot
  apply (relation_eq_projection_product_iff R).mpr
  intro p hp q hq
  have hp' : p ∈ Cells.first R ×ˢ E := hRect ▸ hp
  have hq' : q ∈ Cells.first R ×ˢ E := hRect ▸ hq
  exact hRect.symm ▸ (show (p.1,q.2) ∈ Cells.first R ×ˢ E from ⟨hp'.1,hq'.2⟩)

namespace UniformMixedCellPresentation
variable {S : Set M} {A : DefSet (M := M) S 2 m}

theorem nonrectangular_nonzero_row_balanced (F : UniformMixedCellPresentation G (carrier A))
    (hNames : commonRealNames G ⊆ S) (γ : Values.Gamma (M := M)) (hγ : 1 < γ) (a : A)
    (hNot : (Fin.elim0,Fin.append a.val.2 (F.parameters.toFun a)) ∈
      nonrectangleRVLabels (carrier (gammaRVGraphRefinement A F.parameters hNames)))
    (ht : (F.vertical.projection a).val.2 F.vertical.paradigm_index ≠ rv (0 : VF (M := M))) :
    ∃ r : RV (M := M), Cells.IsBalanced (mixedPairFibre F.parameters a) (F.localPosition a) r
      ((F.vertical.projection a).val.2 F.vertical.paradigm_index) := by
  have hFibre := gamma_rv_graph_refinement_two_fibre A F.parameters hNames
    (fun a b he => F.parameters_reflect_same_rv a b he) a
  have hNot' := (nonrectangle_labels_iff_fibre_not_product _ _).mp hNot
  have hNotR : mixedPairFibre F.parameters a ≠
      Cells.first (mixedPairFibre F.parameters a) ×ˢ Cells.second (mixedPairFibre F.parameters a) :=
    Eq.mp (congrArg (fun R => R ≠ Cells.first R ×ˢ Cells.second R) hFibre) hNot'
  exact nonrectangle_nonzero_cell_balanced γ hγ (F.local_position_cell_data a) ht hNotR

theorem row_shape_trichotomy (F : UniformMixedCellPresentation G (carrier A))
    (hNames : commonRealNames G ⊆ S) (γ : Values.Gamma (M := M)) (hγ : 1 < γ) (a : A) :
    (F.vertical.projection a).val.2 F.vertical.paradigm_index = rv (0 : VF (M := M)) ∨
    mixedPairFibre F.parameters a = Cells.first (mixedPairFibre F.parameters a) ×ˢ
      Cells.second (mixedPairFibre F.parameters a) ∨
    ∃ r : RV (M := M), Cells.IsBalanced (mixedPairFibre F.parameters a) (F.localPosition a) r
      ((F.vertical.projection a).val.2 F.vertical.paradigm_index) := by
  by_cases ht : (F.vertical.projection a).val.2 F.vertical.paradigm_index = rv (0 : VF (M := M))
  · exact Or.inl ht
  · by_cases hR : mixedPairFibre F.parameters a = Cells.first (mixedPairFibre F.parameters a) ×ˢ
        Cells.second (mixedPairFibre F.parameters a)
    · exact Or.inr (Or.inl hR)
    · exact Or.inr (Or.inr (nonrectangle_nonzero_cell_balanced γ hγ (F.local_position_cell_data a) ht hR))

end UniformMixedCellPresentation
end IntegrationInACVF.Section7
