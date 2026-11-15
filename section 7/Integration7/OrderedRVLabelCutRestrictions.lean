import Integration7.RVLabelCutHeadPreparations
import IntegrationSection6.OrderedTargetEqualityTransport
import IntegrationSection6.OrderedSelectedWeights

/-! Actual ordered contractions restrict to arbitrary original-Gamma
predicates on selected old RV labels over the same small real base.
All VF-volume and recursive selected-volume selectors are preserved. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
open IntegrationInACVF.Section5 IntegrationInACVF.Section6
namespace IntegrationInACVF.Section7
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {S : Set M} {n a l : ℕ}
variable {U : DefSet (M := M) S n a} {V : DefSet (M := M) S 0 l}

theorem ordered_rv_label_cut_restriction_exists (T : OrderedContractionProgram S U V) :
    ∀ (hU : GammaSetDefinable B (carrier U)) (hT : GammaProgramDefinable B T)
      {k : ℕ} (ρ : Fin k → Fin a) (R : Set (Point (M := M) 0 k)) (hR : GammaSetDefinable B R) (hNames : commonRealNames B ⊆ S),
    ∃ P : OrderedContractionProgram S (rvLabelCut U hU ρ R hR hNames)
      (rvLabelCut V (gamma_program_final_set T hT) (fun j => suffixIndex T.rvArity_le (ρ j)) R hR hNames),
      GammaProgramDefinable B P ∧
      P.volumeIndex = T.volumeIndex ∧
      ∀ (k' : ℕ) (τ : Fin k' → Fin a), orderedSelectedIndex P τ = orderedSelectedIndex T τ := by
  induction T with
  | zero U =>
    intro hU hT k ρ R hR hNames
    have hIdx : (fun j => suffixIndex (OrderedContractionProgram.zero U).rvArity_le (ρ j)) = ρ := by
      funext j
      apply Fin.ext
      simp [suffixIndex]
    have hEnd : rvLabelCut U hU ρ R hR hNames =
        rvLabelCut U hT (fun j => suffixIndex (OrderedContractionProgram.zero U).rvArity_le (ρ j)) R hR hNames := by
      rw [hIdx]
    let P := orderedCastTarget (.zero (rvLabelCut U hU ρ R hR hNames)) hEnd
    refine ⟨P,gamma_orderedCastTarget _ _ (gamma_rv_label_cut U hU ρ R hR),?_,?_⟩
    · exact orderedCastTarget_volumeIndex _ _
    · intro k' τ
      exact orderedCastTarget_selectedIndex _ _ τ
  | @step n a l U V T tail ih =>
    intro hU hT k ρ R hR hNames
    have hA := gamma_headImage T.target hT.2.1
    obtain ⟨P,hP,hVolume,hSelected⟩ := ih hA hT.2.2 (headSelectedLabelIndex T ρ) R hR hNames
    have hIdx : (fun j => suffixIndex tail.rvArity_le (headSelectedLabelIndex T ρ j)) =
        (fun j => suffixIndex (OrderedContractionProgram.step T tail).rvArity_le (ρ j)) := by
      funext j
      exact suffixIndex_step_tail T tail (ρ j)
    have hEnd :
        rvLabelCut V (gamma_program_final_set tail hT.2.2)
          (fun j => suffixIndex tail.rvArity_le (headSelectedLabelIndex T ρ j)) R hR hNames =
        rvLabelCut V (gamma_program_final_set (.step T tail) hT)
          (fun j => suffixIndex (OrderedContractionProgram.step T tail).rvArity_le (ρ j)) R hR hNames :=
      congrArg (fun θ => rvLabelCut V (gamma_program_final_set tail hT.2.2) θ R hR hNames) hIdx
    let H := rvLabelCutHeadPreparation T hU hT.2.1 ρ R hR hNames
    let hStart := rv_label_cut_head_preparation_contracted T hU hT.2.1 ρ R hR hNames
    let P' := orderedCastSource (orderedCastTarget P hEnd) hStart.symm
    have hP' : GammaProgramDefinable B P' :=
      gamma_orderedCastSource _ _ (gamma_orderedCastTarget _ _ hP)
    have hV' : P'.volumeIndex = tail.volumeIndex :=
      (orderedCastSource_volumeIndex _ _).trans ((orderedCastTarget_volumeIndex _ _).trans hVolume)
    have hS' (k' : ℕ) (τ : Fin k' → Fin (1+T.arity)) :
        orderedSelectedIndex P' τ = orderedSelectedIndex tail τ :=
      (orderedCastSource_selectedIndex _ _ τ).trans
        ((orderedCastTarget_selectedIndex _ _ τ).trans (hSelected k' τ))
    refine ⟨.step H P',⟨gamma_rv_label_cut_head_preparation_map T hU hT.1 hT.2.1 ρ R hR hNames,
      gamma_rv_label_cut_head_preparation_target T hU hT.2.1 ρ R hR hNames,hP'⟩,?_,?_⟩
    · funext i
      cases i using Fin.cases with
      | zero => rfl
      | succ i => exact congrFun hV' i
    · intro k' τ
      exact hS' (1+k') (headVolumeIndex T τ)

end IntegrationInACVF.Section7
