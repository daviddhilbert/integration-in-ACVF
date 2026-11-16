module

public import Integration7.UniformCellPartitionContractionRestrictions

@[expose] public section

/-! The three actual cell-family pieces and their RV-label predicates
as one finite family. The predicates are a disjoint cover, and every
specified contraction has actual target restriction presentations. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section5
open IntegrationInACVF.Section5

namespace IntegrationInACVF.Section7.UniformMixedCellPresentation
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {G : Base (M := M)} {S : Set M} {m : ℕ}
variable {A : DefSet (M := M) S 2 m}

def shapeNativePieces (F : UniformMixedCellPresentation G (carrier A)) (hNames : commonRealNames G ⊆ S) :
    Fin 3 → DefSet (M := M) S 2 (m+F.arity) :=
  ![F.zeroNativePart hNames,F.rectangularNativePart hNames,F.balancedNativeRefinement hNames]

def shapeRVLabels (F : UniformMixedCellPresentation G (carrier A)) (hNames : commonRealNames G ⊆ S) :
    Fin 3 → Set (Point (M := M) 0 (m+F.arity)) :=
  ![F.zeroParadigmRVLabels hNames,F.rectangularPartRVLabels hNames,F.balancedPartRVLabels hNames]

theorem shape_native_piece_gamma (F : UniformMixedCellPresentation G (carrier A))
    (hNames : commonRealNames G ⊆ S) (i : Fin 3) :
    GammaSetDefinable G (carrier (F.shapeNativePieces hNames i)) := by
  fin_cases i
  · exact F.zero_native_part_gamma hNames
  · exact F.rectangular_native_part_gamma hNames
  · exact F.balanced_native_refinement_gamma hNames

theorem shape_native_piece_finite_labels (F : UniformMixedCellPresentation G (carrier A))
    (hNames : commonRealNames G ⊆ S)
    (hfin : ∀ x : Fin 2 → VF (M := M), {r : Fin m → RV (M := M) | (x,r) ∈ carrier A}.Finite) (i : Fin 3) :
    ∀ x : Fin 2 → VF (M := M), {r | (x,r) ∈ carrier (F.shapeNativePieces hNames i)}.Finite := by
  fin_cases i
  · exact F.zero_native_part_finite_labels hNames hfin
  · exact F.rectangular_native_part_finite_labels hNames hfin
  · exact F.balanced_native_refinement_finite_labels hNames hfin

theorem shape_native_piece_subset (F : UniformMixedCellPresentation G (carrier A))
    (hNames : commonRealNames G ⊆ S) (i : Fin 3) :
    carrier (F.shapeNativePieces hNames i) ⊆ carrier (gammaRVGraphRefinement A F.parameters hNames) := by
  fin_cases i
  · exact fun _ h => h.1
  · exact fun _ h => h.1.1
  · intro p hp
    have h := Eq.mp (congrArg (fun D => p ∈ D) (F.balanced_native_refinement_carrier hNames)) hp
    exact h.1.1

theorem shape_rv_labels_gamma (F : UniformMixedCellPresentation G (carrier A))
    (hNames : commonRealNames G ⊆ S) (i : Fin 3) : GammaSetDefinable G (F.shapeRVLabels hNames i) := by
  fin_cases i
  · exact F.zero_paradigm_rv_labels_gamma hNames
  · exact F.rectangular_part_rv_labels_gamma hNames
  · exact F.balanced_part_rv_labels_gamma hNames

theorem shape_rv_labels_cover (F : UniformMixedCellPresentation G (carrier A))
    (hNames : commonRealNames G ⊆ S) :
    (F.shapeRVLabels hNames 0 ∪ F.shapeRVLabels hNames 1) ∪ F.shapeRVLabels hNames 2 = Set.univ := by
  ext p
  change ((p ∈ F.zeroParadigmRVLabels hNames ∨ p ∈ F.rectangularPartRVLabels hNames) ∨
    p ∈ F.balancedPartRVLabels hNames) ↔ p ∈ Set.univ
  simp only [rectangularPartRVLabels,balancedPartRVLabels,Set.mem_sdiff,Set.mem_inter_iff,Set.mem_univ,true_and]
  tauto

theorem shape_rv_labels_disjoint (F : UniformMixedCellPresentation G (carrier A))
    (hNames : commonRealNames G ⊆ S) : Pairwise (fun i j => Disjoint (F.shapeRVLabels hNames i) (F.shapeRVLabels hNames j)) := by
  have h01 : Disjoint (F.shapeRVLabels hNames 0) (F.shapeRVLabels hNames 1) := by
    apply Set.disjoint_left.mpr
    intro p hp hq
    exact hq.1.2 hp
  have h02 : Disjoint (F.shapeRVLabels hNames 0) (F.shapeRVLabels hNames 2) := by
    apply Set.disjoint_left.mpr
    intro p hp hq
    exact hq.1.2 hp
  have h12 : Disjoint (F.shapeRVLabels hNames 1) (F.shapeRVLabels hNames 2) := by
    apply Set.disjoint_left.mpr
    intro p hp hq
    exact hp.2 hq.2
  intro i j hne
  fin_cases i <;> fin_cases j
  · exact (hne rfl).elim
  · exact h01
  · exact h02
  · exact h01.symm
  · exact (hne rfl).elim
  · exact h12
  · exact h02.symm
  · exact h12.symm
  · exact (hne rfl).elim

theorem shape_contraction_presentations (F : UniformMixedCellPresentation G (carrier A))
    (hNames : commonRealNames G ⊆ S) {σ : Equiv.Perm (Fin 2)}
    (T : StandardContraction (gammaRVGraphRefinement A F.parameters hNames) σ)
    (hT : GammaProgramDefinable G T.program) (i : Fin 3) :
    Nonempty (StandardTargetRestrictionPresentation (G := G) T (F.shapeNativePieces hNames i)
      (rvLabelCut T.target (gamma_program_final_set T.program hT) (suffixIndex T.program.rvArity_le)
        (F.shapeRVLabels hNames i) (F.shape_rv_labels_gamma hNames i) hNames)) := by
  fin_cases i
  · exact F.zero_part_contraction_presentation hNames T hT
  · exact F.rectangular_part_contraction_presentation hNames T hT
  · exact F.balanced_part_contraction_presentation hNames T hT

end IntegrationInACVF.Section7.UniformMixedCellPresentation
