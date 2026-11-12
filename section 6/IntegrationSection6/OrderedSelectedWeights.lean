import IntegrationSection6.OrderedSelectedVolume
import IntegrationSection6.FiniteGammaWeightedIsos

/-! The recursive selected volume has exactly the weight of the ordinary
contraction volume followed by the selected original labels. Thus the
explicit recursive order gives the same RV[k] object up to isomorphism. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5 SpecialTransformations.Section7
open IntegrationInACVF.Section5
namespace IntegrationInACVF.Section6
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {S : Set M}

theorem rawWeight_append {a b : ℕ} (u : Fin a → M) (v : Fin b → M) :
    rawWeight (Fin.append u v) = rawWeight u + rawWeight v := by
  unfold rawWeight
  rw [Fin.sum_univ_add]
  simp only [Fin.append_left,Fin.append_right]

theorem rawWeight_succ {n : ℕ} (t : Fin (n+1) → M) :
    rawWeight t = (if t 0 ≠ iRVZero then 1 else 0) + rawWeight (fun j => t j.succ) := by
  unfold rawWeight
  rw [Fin.sum_univ_succ]

theorem suffixIndex_step_tail {n m l : ℕ} {A : DefSet (M := M) S (n+1) m}
    {U : DefSet (M := M) S 0 l} (T : HeadPreparation A)
    (tail : OrderedContractionProgram S T.contractedSet U) (j : Fin m) :
    suffixIndex tail.rvArity_le (Fin.natAdd 1 (suffixIndex (specialRelative_rvArity_le T.special) j)) =
      suffixIndex (OrderedContractionProgram.step T tail).rvArity_le j := by
  apply Fin.ext
  have hT := specialRelative_rvArity_le T.special
  have htail := tail.rvArity_le
  change l-(1+T.arity)+(1+(T.arity-m+j.val)) = l-m+j.val
  omega

theorem orderedSelectedIndex_weight {n m l : ℕ} {A : DefSet (M := M) S n m}
    {U : DefSet (M := M) S 0 l} (T : OrderedContractionProgram S A U)
    {k : ℕ} (ρ : Fin k → Fin m) (r : Fin l → RV (M := M)) :
    rawWeight (fun j => (r (orderedSelectedIndex T ρ j)).val) =
      rawWeight (fun i => (r (T.volumeIndex i)).val) +
        rawWeight (fun j => (r (suffixIndex T.rvArity_le (ρ j))).val) := by
  induction T generalizing k with
  | zero A =>
    have hidx (j : Fin k) : suffixIndex (OrderedContractionProgram.zero A).rvArity_le (ρ j) = ρ j := by
      apply Fin.ext
      simp [suffixIndex]
    simp only [orderedSelectedIndex,rawWeight,Finset.univ_eq_empty,Finset.sum_empty,Nat.zero_add,hidx]
    rfl
  | @step n m l A U T tail ih =>
    change rawWeight (fun j => (r (orderedSelectedIndex tail (headVolumeIndex T ρ) j)).val) = _
    rw [ih]
    have hOld : (fun j => (r (suffixIndex tail.rvArity_le (headVolumeIndex T ρ j))).val) =
        Fin.append (fun _ : Fin 1 => (r ((OrderedContractionProgram.step T tail).volumeIndex 0)).val)
          (fun j => (r (suffixIndex (OrderedContractionProgram.step T tail).rvArity_le (ρ j))).val) := by
      funext j
      cases j using Fin.addCases with
      | left j =>
        have hj : j = 0 := Subsingleton.elim _ _
        subst j
        rfl
      | right j =>
        simp only [headVolumeIndex,Fin.append_right,headSelectedLabelIndex]
        rw [suffixIndex_step_tail T tail (ρ j)]
    rw [hOld,rawWeight_append]
    rw [rawWeight_succ (fun i => (r ((OrderedContractionProgram.step T tail).volumeIndex i)).val)]
    have hOne : rawWeight (fun _ : Fin 1 => (r ((OrderedContractionProgram.step T tail).volumeIndex 0)).val) =
        (if (r ((OrderedContractionProgram.step T tail).volumeIndex 0)).val ≠ iRVZero then 1 else 0) := by
      simp [rawWeight]
    rw [hOne]
    change _ + (_ + _) = (_ + rawWeight (fun i => (r (tail.volumeIndex i)).val)) + _
    omega

end IntegrationInACVF.Section6
