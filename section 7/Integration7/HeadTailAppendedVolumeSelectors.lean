import Integration7.HeadTailAppendedStandardPrograms

/-! The appended program restores the head and every tail coordinate
to their original positions, and retains the original density label. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section5
open IntegrationInACVF.Section5 IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {S : Set M} {n a : ℕ} {A : DefSet (M := M) S (n+1) a}

theorem head_tail_appended_volume_head (σ : Equiv.Perm (Fin (n+1)))
    (T : HeadPreparation (vfPermutationImage A σ)) (τ : Equiv.Perm (Fin n))
    (D : StandardContraction T.contractedSet τ) :
    (headTailAppendedStandardProgram σ T τ D).volumeIndex (σ 0) = suffixIndex D.program.rvArity_le 0 := by
  unfold headTailAppendedStandardProgram
  rw [standard_from_program_volume_index]
  have hi : ((headTailPerm τ).trans σ).symm (σ 0) = 0 := by
    change (headTailPerm τ).symm (σ.symm (σ 0)) = 0
    rw [σ.symm_apply_apply]
    rfl
  rw [hi]
  rfl

theorem head_tail_appended_volume_tail (σ : Equiv.Perm (Fin (n+1)))
    (T : HeadPreparation (vfPermutationImage A σ)) (τ : Equiv.Perm (Fin n))
    (D : StandardContraction T.contractedSet τ) (j : Fin n) :
    (headTailAppendedStandardProgram σ T τ D).volumeIndex (σ j.succ) = D.volumeIndex j := by
  unfold headTailAppendedStandardProgram
  rw [standard_from_program_volume_index]
  have hi : ((headTailPerm τ).trans σ).symm (σ j.succ) = (τ.symm j).succ := by
    change (headTailPerm τ).symm (σ.symm (σ j.succ)) = (τ.symm j).succ
    rw [σ.symm_apply_apply]
    rfl
  rw [hi]
  change (orderedCastSource D.program _).volumeIndex (τ.symm j) = D.volumeIndex j
  rw [orderedCastSource_volumeIndex]
  rfl

theorem head_tail_appended_old_index (σ : Equiv.Perm (Fin (n+1)))
    (T : HeadPreparation (vfPermutationImage A σ)) (τ : Equiv.Perm (Fin n))
    (D : StandardContraction T.contractedSet τ) (δ : Fin a) :
    suffixIndex D.program.rvArity_le (Fin.natAdd 1 (suffixIndex (specialRelative_rvArity_le T.special) δ)) =
      suffixIndex (headTailAppendedStandardProgram σ T τ D).program.rvArity_le δ := by
  apply Fin.ext
  have hD := D.program.rvArity_le
  have hT := specialRelative_rvArity_le T.special
  change D.arity-(1+T.arity)+(1+(T.arity-a+δ.val)) = D.arity-a+δ.val
  omega

end IntegrationInACVF.Section7
