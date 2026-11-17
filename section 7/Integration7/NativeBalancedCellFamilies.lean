module

public import Integration7.UniformBalancedPartSelections
public import Integration7.NativeRVParameterSelections
public import Integration7.UniformCellVerticalContractions
public import Integration7.UniformBalancedHorizontalContractions

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! The balanced part of an arbitrary uniform cell chart has an actual
native presentation and proved balanced rows. Both translated families
and their opposite-order standard contractions are constructed, with
all old labels and arbitrary retained density still present. -/
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

def balancedNativeSource (F : UniformMixedCellPresentation G (carrier A)) (hNames : commonRealNames G ⊆ S) :
    DefSet (M := M) S 2 m :=
  nativeRVParameterSelection A F.parameters (F.balancedParameterLabels hNames)
    (F.balanced_parameter_labels_gamma hNames) hNames

def balancedNativeChart (F : UniformMixedCellPresentation G (carrier A)) (hNames : commonRealNames G ⊆ S) :
    UniformMixedCellPresentation G (carrier (F.balancedNativeSource hNames)) :=
  F.select (F.balancedParameterLabels hNames) (F.balanced_parameter_labels_gamma hNames)

theorem balanced_native_source_carrier (F : UniformMixedCellPresentation G (carrier A))
    (hNames : commonRealNames G ⊆ S) : carrier (F.balancedNativeSource hNames) = F.balancedSource hNames :=
  F.balanced_parameter_selection_eq hNames

theorem balanced_native_source_gamma (F : UniformMixedCellPresentation G (carrier A))
    (hNames : commonRealNames G ⊆ S) : GammaSetDefinable G (carrier (F.balancedNativeSource hNames)) :=
  gamma_native_rv_parameter_selection A F.parameters _ (F.balanced_parameter_labels_gamma hNames) hNames

theorem balanced_native_source_finite_labels (F : UniformMixedCellPresentation G (carrier A))
    (hNames : commonRealNames G ⊆ S)
    (hfin : ∀ x : Fin 2 → VF (M := M), {r : Fin m → RV (M := M) | (x,r) ∈ carrier A}.Finite) :
    ∀ x : Fin 2 → VF (M := M), {r : Fin m → RV (M := M) | (x,r) ∈ carrier (F.balancedNativeSource hNames)}.Finite :=
  native_rv_parameter_selection_finite_labels A F.parameters _ (F.balanced_parameter_labels_gamma hNames) hNames hfin

theorem balanced_native_source_density_nonzero (F : UniformMixedCellPresentation G (carrier A))
    (hNames : commonRealNames G ⊆ S) (δ : Fin m) (hδ : ∀ a : A, (a.val.2 δ).val ≠ iRVZero) :
    ∀ a : F.balancedNativeSource hNames, (a.val.2 δ).val ≠ iRVZero :=
  native_rv_parameter_selection_density_nonzero A F.parameters _ (F.balanced_parameter_labels_gamma hNames) hNames δ hδ

theorem balanced_native_chart_rows (F : UniformMixedCellPresentation G (carrier A))
    (hNames : commonRealNames G ⊆ S) (γ : Values.Gamma (M := M)) (hγ : 1 < γ) :
    (F.balancedNativeChart hNames).BalancedRows := F.balanced_parameter_selection_rows hNames γ hγ

theorem balanced_native_translation_contractions_exist (C : BaseContext M)
    (hNames : commonRealNames G ⊆ (C.base : Set M))
    (γ : Values.Gamma (M := M)) (hγ : γ ∈ G.gamma) (hγ1 : 1 < γ)
    {A : DefSet (M := M) (C.base : Set M) 2 m} (F : UniformMixedCellPresentation G (carrier A)) :
    let Q := F.balancedNativeChart hNames
    let hB := F.balanced_native_chart_rows hNames γ hγ1
    ∃ E : StandardContraction (Q.verticalTranslationImage hNames) (Equiv.refl _),
    ∃ L : StandardContraction (Q.horizontalTranslationImage hB hNames) (Equiv.swap 0 1),
      GammaProgramDefinable G E.program ∧ GammaProgramDefinable G L.program := by
  intro Q hB
  obtain ⟨E,hE⟩ := Q.vertical_translation_standard_contraction_exists C hNames γ hγ hγ1
  obtain ⟨L,hL⟩ := Q.horizontal_translation_standard_contraction_exists C hNames γ hγ hγ1 hB
  exact ⟨E,L,hE,hL⟩

end IntegrationInACVF.Section7.UniformMixedCellPresentation
