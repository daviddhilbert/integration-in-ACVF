module

public import Integration7.NativeBalancedCellFamilies

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! Nondegeneracy of the selected balanced chart follows from the
actual three-part partition, with no additional paradigm assumption. -/
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

theorem balanced_native_chart_paradigm_nonzero (F : UniformMixedCellPresentation G (carrier A))
    (hNames : commonRealNames G ⊆ S) (a : F.balancedNativeSource hNames) :
    ((F.balancedNativeChart hNames).vertical.projection a).val.2
      (F.balancedNativeChart hNames).vertical.paradigm_index ≠ rv (0 : VF (M := M)) := by
  intro ht
  let R := F.balancedParameterLabels hNames
  let hR := F.balanced_parameter_labels_gamma hNames
  let a₀ := F.parameters.selectedInclusion R a
  have hB := F.selected_balanced_source_mem hNames a
  apply hB.1.2
  apply (F.mem_zero_paradigm_rv_labels hNames _).mpr
  have hpar := F.select_paradigm_value R hR a
  exact (F.refinement_paradigm_on_graph hNames a₀).trans (hpar.symm.trans ht)

end IntegrationInACVF.Section7.UniformMixedCellPresentation
