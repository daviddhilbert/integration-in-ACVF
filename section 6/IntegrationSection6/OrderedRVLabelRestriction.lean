import IntegrationSection6.RVLabelHeadPreparations
import IntegrationSection6.OrderedTargetEqualityTransport
import IntegrationSection6.OrderedSelectedWeights

/-! Actual ordered contractions restrict to fixed selected old RV labels.
Every VF-volume and recursive selected-volume selector is preserved. This
is a construction of programs and Gamma certificates, not an invariance
assumption on their common-blowup classes. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
open IntegrationInACVF.Section5
namespace IntegrationInACVF.Section6
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {n a l : ℕ}
variable {U : DefSet (M := M) Set.univ n a} {V : DefSet (M := M) Set.univ 0 l}

theorem ordered_rv_label_restriction_exists (T : OrderedContractionProgram Set.univ U V) :
    ∀ (hU : GammaSetDefinable B (carrier U)) (hT : GammaProgramDefinable B T)
      {k : ℕ} (ρ : Fin k → Fin a) (t : Fin k → RV (M := M)),
    ∃ P : OrderedContractionProgram Set.univ (rvLabelSlice U hU ρ t)
      (rvLabelSlice V (gamma_program_final_set T hT) (fun j => suffixIndex T.rvArity_le (ρ j)) t),
      GammaProgramDefinable ⟨B.real ∪ Set.range (fun j => (t j).val),B.gamma⟩ P ∧
      P.volumeIndex = T.volumeIndex ∧
      ∀ (k' : ℕ) (τ : Fin k' → Fin a), orderedSelectedIndex P τ = orderedSelectedIndex T τ := by
  induction T with
  | zero U =>
    intro hU hT k ρ t
    have hIdx : (fun j => suffixIndex (OrderedContractionProgram.zero U).rvArity_le (ρ j)) = ρ := by
      funext j
      apply Fin.ext
      simp [suffixIndex]
    have hEnd : rvLabelSlice U hU ρ t =
        rvLabelSlice U hT (fun j => suffixIndex (OrderedContractionProgram.zero U).rvArity_le (ρ j)) t := by
      rw [hIdx]
    let P := orderedCastTarget (.zero (rvLabelSlice U hU ρ t)) hEnd
    refine ⟨P,gamma_orderedCastTarget _ _ (rvLabelSlice_gamma U hU ρ t),?_,?_⟩
    · exact orderedCastTarget_volumeIndex _ _
    · intro k' τ
      exact orderedCastTarget_selectedIndex _ _ τ
  | @step n a l U V T tail ih =>
    intro hU hT k ρ t
    have hA := gamma_headImage T.target hT.2.1
    obtain ⟨P,hP,hVolume,hSelected⟩ := ih hA hT.2.2 (headSelectedLabelIndex T ρ) t
    have hIdx : (fun j => suffixIndex tail.rvArity_le (headSelectedLabelIndex T ρ j)) =
        (fun j => suffixIndex (OrderedContractionProgram.step T tail).rvArity_le (ρ j)) := by
      funext j
      exact suffixIndex_step_tail T tail (ρ j)
    have hEnd :
        rvLabelSlice V (gamma_program_final_set tail hT.2.2)
          (fun j => suffixIndex tail.rvArity_le (headSelectedLabelIndex T ρ j)) t =
        rvLabelSlice V (gamma_program_final_set (.step T tail) hT)
          (fun j => suffixIndex (OrderedContractionProgram.step T tail).rvArity_le (ρ j)) t :=
      congrArg (fun θ => rvLabelSlice V (gamma_program_final_set tail hT.2.2) θ t) hIdx
    let H := rvLabelHeadPreparation T hU hT.2.1 ρ t
    let hStart := rvLabelHeadPreparation_contracted T hU hT.2.1 ρ t
    let P' := orderedCastSource (orderedCastTarget P hEnd) hStart.symm
    have hP' : GammaProgramDefinable ⟨B.real ∪ Set.range (fun j => (t j).val),B.gamma⟩ P' :=
      gamma_orderedCastSource _ _ (gamma_orderedCastTarget _ _ hP)
    have hV' : P'.volumeIndex = tail.volumeIndex :=
      (orderedCastSource_volumeIndex _ _).trans ((orderedCastTarget_volumeIndex _ _).trans hVolume)
    have hS' (k' : ℕ) (τ : Fin k' → Fin (1+T.arity)) :
        orderedSelectedIndex P' τ = orderedSelectedIndex tail τ :=
      (orderedCastSource_selectedIndex _ _ τ).trans
        ((orderedCastTarget_selectedIndex _ _ τ).trans (hSelected k' τ))
    refine ⟨.step H P',⟨gamma_rvLabelHeadPreparation_map T hU hT.1 hT.2.1 ρ t,
      gamma_rvLabelHeadPreparation_target T hU hT.2.1 ρ t,hP'⟩,?_,?_⟩
    · funext i
      cases i using Fin.cases with
      | zero => rfl
      | succ i => exact congrFun hV' i
    · intro k' τ
      exact hS' (1+k') (headVolumeIndex T τ)

end IntegrationInACVF.Section6
