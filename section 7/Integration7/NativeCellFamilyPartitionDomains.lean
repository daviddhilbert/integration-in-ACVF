module

public import Integration7.NativeBalancedCellFamilies
public import Integration7.UniformZeroParadigmContractions
public import Integration7.NativeRectangleFamilyHeadGeometry

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! Actual native domains realize the three-part cell-family partition.
The selected balanced chart refines to exactly the balanced part of the
original graph family; the rectangular part has literal product fibres. -/
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

def rectangularNativePart (F : UniformMixedCellPresentation G (carrier A)) (hNames : commonRealNames G ⊆ S) :
    DefSet (M := M) S 2 (m+F.arity) :=
  PresentedSet.mk (F.rectangularPart hNames) (SetDefinable.mono _
    (gamma_native_set_common_names (F.rectangular_part_gamma hNames)) hNames)

theorem rectangular_native_part_gamma (F : UniformMixedCellPresentation G (carrier A))
    (hNames : commonRealNames G ⊆ S) : GammaSetDefinable G (carrier (F.rectangularNativePart hNames)) :=
  F.rectangular_part_gamma hNames

theorem rectangular_native_part_finite_labels (F : UniformMixedCellPresentation G (carrier A))
    (hNames : commonRealNames G ⊆ S)
    (hfin : ∀ x : Fin 2 → VF (M := M), {r : Fin m → RV (M := M) | (x,r) ∈ carrier A}.Finite) :
    ∀ x : Fin 2 → VF (M := M),
      {r : Fin (m+F.arity) → RV (M := M) | (x,r) ∈ carrier (F.rectangularNativePart hNames)}.Finite := by
  intro x
  exact (gamma_rv_graph_refinement_finite_labels A hfin F.parameters hNames x).subset (fun r hr => hr.1.1)

theorem rectangular_native_part_fibres (F : UniformMixedCellPresentation G (carrier A))
    (hNames : commonRealNames G ⊆ S) : RectangularRVFibres (carrier (F.rectangularNativePart hNames)) :=
  F.rectangular_part_fibres_are_products hNames

def balancedNativeRefinement (F : UniformMixedCellPresentation G (carrier A)) (hNames : commonRealNames G ⊆ S) :
    DefSet (M := M) S 2 (m+F.arity) :=
  gammaRVGraphRefinement (F.balancedNativeSource hNames) (F.balancedNativeChart hNames).parameters hNames

set_option maxHeartbeats 1600000 in
theorem balanced_native_refinement_carrier (F : UniformMixedCellPresentation G (carrier A))
    (hNames : commonRealNames G ⊆ S) : carrier (F.balancedNativeRefinement hNames) = F.balancedPart hNames := by
  let R := F.balancedParameterLabels hNames
  let hR := F.balanced_parameter_labels_gamma hNames
  ext p
  constructor
  · rintro ⟨a,ha⟩
    let a₀ := F.parameters.selectedInclusion R a
    have hPar := F.select_parameters_value R hR a
    have hVal : (gammaRVGraphRefinementMap A F.parameters hNames a₀).val =
        (gammaRVGraphRefinementMap (F.balancedNativeSource hNames) (F.balancedNativeChart hNames).parameters hNames a).val := by
      exact Prod.ext rfl (congrArg (Fin.append a.val.2) hPar.symm)
    have hB := F.selected_balanced_source_mem hNames a
    exact (congrArg (fun q => q ∈ F.balancedPart hNames) (hVal.trans ha)).mp hB
  · intro hp
    obtain ⟨a,ha⟩ := hp.1.1
    have hB : (gammaRVGraphRefinementMap A F.parameters hNames a).val ∈ F.balancedPart hNames :=
      (congrArg (fun q => q ∈ F.balancedPart hNames) ha).mpr hp
    have hSource : a.val ∈ F.balancedSource hNames := ⟨a,rfl,hB⟩
    have hSelected : a.val ∈ F.parameters.selectedDomain R :=
      (congrArg (fun D => a.val ∈ D) (F.balanced_parameter_selection_eq hNames)).mpr hSource
    let b : F.balancedNativeSource hNames := ⟨a.val,hSelected⟩
    have hb : F.parameters.selectedInclusion R b = a := Subtype.ext rfl
    have hPar := (F.select_parameters_value R hR b).trans (congrArg F.parameters.toFun hb)
    refine ⟨b,?_⟩
    exact (Prod.ext rfl (congrArg (Fin.append a.val.2) hPar)).trans ha

theorem balanced_native_refinement_gamma (F : UniformMixedCellPresentation G (carrier A))
    (hNames : commonRealNames G ⊆ S) : GammaSetDefinable G (carrier (F.balancedNativeRefinement hNames)) :=
  gamma_rv_graph_refinement_target_gamma _ _ hNames

theorem balanced_native_refinement_finite_labels (F : UniformMixedCellPresentation G (carrier A))
    (hNames : commonRealNames G ⊆ S)
    (hfin : ∀ x : Fin 2 → VF (M := M), {r : Fin m → RV (M := M) | (x,r) ∈ carrier A}.Finite) :
    ∀ x : Fin 2 → VF (M := M),
      {r : Fin (m+F.arity) → RV (M := M) | (x,r) ∈ carrier (F.balancedNativeRefinement hNames)}.Finite :=
  gamma_rv_graph_refinement_finite_labels _ (F.balanced_native_source_finite_labels hNames hfin) _ hNames

theorem native_shape_partition_cover (F : UniformMixedCellPresentation G (carrier A))
    (hNames : commonRealNames G ⊆ S) :
    carrier (F.zeroNativePart hNames) ∪ carrier (F.rectangularNativePart hNames) ∪
      carrier (F.balancedNativeRefinement hNames) = carrier (gammaRVGraphRefinement A F.parameters hNames) := by
  have h := (F.shape_partition hNames).2.2.2
  exact (congrArg (fun D => F.zeroParadigmPart hNames ∪ F.rectangularPart hNames ∪ D)
    (F.balanced_native_refinement_carrier hNames)).trans h

end IntegrationInACVF.Section7.UniformMixedCellPresentation
