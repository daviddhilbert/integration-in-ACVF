module

public import Integration7.SelectedCellPositionRows
public import Integration7.UniformNonrectangleCellAlternatives
public import Integration7.UniformBalancedCellGeometry

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! Selecting whole refinement-parameter fibres gives an actual uniform
cell presentation with the same centre, paradigm and complete parameter
fibres. Nonrectangular nonzero selections are actual balanced-row charts. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section5
open IntegrationInACVF.Section4

namespace IntegrationInACVF.Section7.UniformMixedCellPresentation
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {m : ℕ}
variable {G : Base (M := M)} {A : Set (Point (M := M) 2 m)}
variable (F : UniformMixedCellPresentation G A) (R : Set (Point (M := M) 0 F.arity))

def select (hR : GammaSetDefinable G R) : UniformMixedCellPresentation G (F.parameters.selectedDomain R) where
  vertical := F.vertical.selectParameters F.labels R hR
  arity := F.arity
  labels := F.vertical.selectedScalarRVMap F.labels R hR
  reflects a b he := F.reflects (F.vertical.selectedScalarInclusion F.labels R a)
    (F.vertical.selectedScalarInclusion F.labels R b) he
  rows a := ⟨F.vertical.selectedPositionRow F.labels R hR a
    (Classical.choice (F.rows (F.vertical.selectedScalarInclusion F.labels R a)))⟩

theorem select_parameters_value (hR : GammaSetDefinable G R) (a : F.parameters.selectedDomain R) :
    (F.select R hR).parameters.toFun a = F.parameters.toFun (F.parameters.selectedInclusion R a) := by
  apply congrArg F.labels.toFun
  exact Subtype.ext rfl

theorem select_centre_value (hR : GammaSetDefinable G R) (a : F.parameters.selectedDomain R) :
    (F.select R hR).centre a = F.centre (F.parameters.selectedInclusion R a) := by
  apply congrArg F.vertical.position
  exact Subtype.ext rfl

theorem select_paradigm_value (hR : GammaSetDefinable G R) (a : F.parameters.selectedDomain R) :
    ((F.select R hR).vertical.projection a).val.2 (F.select R hR).vertical.paradigm_index =
      (F.vertical.projection (F.parameters.selectedInclusion R a)).val.2 F.vertical.paradigm_index := rfl

theorem select_parameter_fibre (hR : GammaSetDefinable G R) (a₀ : F.parameters.selectedDomain R) :
    mixedPairFibre (F.select R hR).parameters a₀ = mixedPairFibre F.parameters (F.parameters.selectedInclusion R a₀) := by
  ext p
  constructor
  · rintro ⟨a,ha,he⟩
    exact ⟨F.parameters.selectedInclusion R a,ha,
      (F.select_parameters_value R hR a).symm.trans (he.trans (F.select_parameters_value R hR a₀))⟩
  · rintro ⟨a,ha,he⟩
    have hSelected : (Fin.elim0,F.parameters.toFun a) ∈ R :=
      (congrArg (fun r => (Fin.elim0,r) ∈ R) he).mpr (F.parameters.selected_inclusion_parameter R a₀)
    let b : F.parameters.selectedDomain R := ⟨a.val,a,rfl,hSelected⟩
    have hb : F.parameters.selectedInclusion R b = a := Subtype.ext rfl
    exact ⟨b,ha,(F.select_parameters_value R hR b).trans
      ((congrArg F.parameters.toFun hb).trans (he.trans (F.select_parameters_value R hR a₀).symm))⟩

theorem selected_nonrectangle_nonzero_balanced_rows (hR : GammaSetDefinable G R)
    (γ : Values.Gamma (M := M)) (hγ : 1 < γ)
    (hShape : ∀ a : F.parameters.selectedDomain R,
      let a₀ := F.parameters.selectedInclusion R a
      mixedPairFibre F.parameters a₀ ≠ Cells.first (mixedPairFibre F.parameters a₀) ×ˢ Cells.second (mixedPairFibre F.parameters a₀))
    (ht : ∀ a : F.parameters.selectedDomain R,
      (F.vertical.projection (F.parameters.selectedInclusion R a)).val.2 F.vertical.paradigm_index ≠ rv (0 : VF (M := M))) :
    (F.select R hR).BalancedRows := by
  intro a
  have hFibre := F.select_parameter_fibre R hR a
  have hNot := Eq.mpr (congrArg (fun Q => Q ≠ Cells.first Q ×ˢ Cells.second Q) hFibre) (hShape a)
  have ht' : ((F.select R hR).vertical.projection a).val.2 (F.select R hR).vertical.paradigm_index ≠
      rv (0 : VF (M := M)) := by
    exact (F.select_paradigm_value R hR a) ▸ ht a
  exact nonrectangle_nonzero_cell_balanced γ hγ ((F.select R hR).local_position_cell_data a) ht' hNot

end IntegrationInACVF.Section7.UniformMixedCellPresentation
