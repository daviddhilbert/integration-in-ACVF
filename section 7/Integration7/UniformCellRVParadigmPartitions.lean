module

public import Integration7.UniformCellVerticalTranslations
public import Integration7.NativeZeroCoordinateLoci

@[expose] public section

/-! The actual uniform vertical paradigm is constant on each retained
RV label. Its zero/nonzero split is original-Gamma definable, using the
zero-coordinate locus in the actual translated family. -/
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

theorem refinement_paradigm_constant_on_labels (F : UniformMixedCellPresentation G (carrier A))
    (hNames : commonRealNames G ⊆ S) (p q : gammaRVGraphRefinement A F.parameters hNames)
    (hRV : p.val.2 = q.val.2) : F.refinementParadigm hNames p = F.refinementParadigm hNames q := by
  have hP := (F.refinement_source_parameters hNames p).trans
    ((congrArg (fun r : Fin (m+F.arity) → RV (M := M) => r ∘ Fin.natAdd m) hRV).trans
      (F.refinement_source_parameters hNames q).symm)
  have hSame := F.reflects (F.vertical.scalarProjection (F.refinementSource hNames p))
    (F.vertical.scalarProjection (F.refinementSource hNames q)) hP
  have hLabels := ((sameRV_iff _ _).mp hSame).2
  exact congrFun hLabels F.vertical.paradigm_index

theorem vertical_translation_head_paradigm (F : UniformMixedCellPresentation G (carrier A))
    (hNames : commonRealNames G ⊆ S) (q : gammaRVGraphRefinement A F.parameters hNames) :
    rv (vfAt (F.verticalTranslation hNames q).val 0) = F.refinementParadigm hNames q := by
  apply (Set.ext_iff.mp (F.source_head_fibre hNames q) (vfAt q.val 0)).mp
  have hReplace : replace 0 q.val (vfAt q.val 0) = q.val := Prod.ext (Function.update_eq_self 0 q.val.1) rfl
  change replace 0 q.val (vfAt q.val 0) ∈ carrier (gammaRVGraphRefinement A F.parameters hNames)
  rw [hReplace]
  exact q.property

def zeroParadigmRVLabels (F : UniformMixedCellPresentation G (carrier A))
    (hNames : commonRealNames G ⊆ S) : Set (Point (M := M) 0 (m+F.arity)) :=
  {p | ∃ x : Fin 2 → VF (M := M), (x,p.2) ∈ carrier (F.verticalTranslationImage hNames) ∧ vfAt (x,p.2) 0 = 0}

theorem zero_paradigm_rv_labels_gamma (F : UniformMixedCellPresentation G (carrier A))
    (hNames : commonRealNames G ⊆ S) : GammaSetDefinable G (F.zeroParadigmRVLabels hNames) :=
  gamma_exists_vf_coordinates ((gammaLogicInput G).inter
    (F.vertical_translation_image_gamma hNames) (gamma_zero_vf_coordinate G 0))

set_option maxHeartbeats 1000000 in
theorem mem_zero_paradigm_rv_labels (F : UniformMixedCellPresentation G (carrier A))
    (hNames : commonRealNames G ⊆ S) (q : gammaRVGraphRefinement A F.parameters hNames) :
    (Fin.elim0,q.val.2) ∈ F.zeroParadigmRVLabels hNames ↔
      F.refinementParadigm hNames q = rv (0 : VF (M := M)) := by
  constructor
  · rintro ⟨x,⟨p,hp⟩,hx⟩
    have hRV := congrArg (fun z : Point (M := M) 2 (m+F.arity) => z.2) hp
    have hHead := congrArg (fun z : Point (M := M) 2 (m+F.arity) => vfAt z 0) hp
    have hZero : vfAt (F.verticalTranslation hNames p).val 0 = 0 := hHead.trans hx
    exact (F.refinement_paradigm_constant_on_labels hNames p q hRV).symm.trans
      ((F.vertical_translation_head_paradigm hNames p).symm.trans (congrArg rv hZero))
  · intro ht
    have hZero := (rv_eq_zero_iff _).mp ((F.vertical_translation_head_paradigm hNames q).trans ht)
    refine ⟨(F.verticalTranslation hNames q).val.1,?_,hZero⟩
    exact (F.verticalTranslation hNames q).property

def zeroParadigmPart (F : UniformMixedCellPresentation G (carrier A)) (hNames : commonRealNames G ⊆ S) :
    Set (Point (M := M) 2 (m+F.arity)) :=
  carrier (gammaRVGraphRefinement A F.parameters hNames) ∩ {p | (Fin.elim0,p.2) ∈ F.zeroParadigmRVLabels hNames}

def nonzeroParadigmPart (F : UniformMixedCellPresentation G (carrier A)) (hNames : commonRealNames G ⊆ S) :
    Set (Point (M := M) 2 (m+F.arity)) :=
  carrier (gammaRVGraphRefinement A F.parameters hNames) \ {p | (Fin.elim0,p.2) ∈ F.zeroParadigmRVLabels hNames}

theorem zero_paradigm_part_gamma (F : UniformMixedCellPresentation G (carrier A))
    (hNames : commonRealNames G ⊆ S) : GammaSetDefinable G (F.zeroParadigmPart hNames) :=
  (gammaLogicInput G).inter (gamma_rv_graph_refinement_target_gamma A F.parameters hNames)
    (gamma_mixed_coordinate_preimage (F.zero_paradigm_rv_labels_gamma hNames) (Fin.elim0 : Fin 0 → Fin 2) id)

theorem nonzero_paradigm_part_gamma (F : UniformMixedCellPresentation G (carrier A))
    (hNames : commonRealNames G ⊆ S) : GammaSetDefinable G (F.nonzeroParadigmPart hNames) :=
  (gammaLogicInput G).sdiff (gamma_rv_graph_refinement_target_gamma A F.parameters hNames)
    (gamma_mixed_coordinate_preimage (F.zero_paradigm_rv_labels_gamma hNames) (Fin.elim0 : Fin 0 → Fin 2) id)

theorem zero_nonzero_paradigm_partition (F : UniformMixedCellPresentation G (carrier A))
    (hNames : commonRealNames G ⊆ S) :
    Disjoint (F.zeroParadigmPart hNames) (F.nonzeroParadigmPart hNames) ∧
      F.zeroParadigmPart hNames ∪ F.nonzeroParadigmPart hNames = carrier (gammaRVGraphRefinement A F.parameters hNames) := by
  constructor
  · exact Set.disjoint_left.mpr (fun p hp hq => hq.2 hp.2)
  · ext p
    change (p ∈ carrier (gammaRVGraphRefinement A F.parameters hNames) ∧
      (Fin.elim0,p.2) ∈ F.zeroParadigmRVLabels hNames) ∨
      (p ∈ carrier (gammaRVGraphRefinement A F.parameters hNames) ∧
      ¬ (Fin.elim0,p.2) ∈ F.zeroParadigmRVLabels hNames) ↔ _
    tauto

end IntegrationInACVF.Section7.UniformMixedCellPresentation
