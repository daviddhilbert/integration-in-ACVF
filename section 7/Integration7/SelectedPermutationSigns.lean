import Integration7.SelectedVFTailPermutations
import Integration7.PermutationRVJacobian

/-! Adding selected coordinates fixed by a VF order does not alter
its determinant sign. All finite casts are actual conjugations. -/
noncomputable section
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
namespace IntegrationInACVF.Section7
open IntegrationInACVF.Section6

theorem fin_append_permutation_sign {n : ℕ} (d : ℕ) (σ : Equiv.Perm (Fin n)) :
    Equiv.Perm.sign (finAppendEquiv σ d)=Equiv.Perm.sign σ := by
  change Equiv.Perm.sign ((finSumFinEquiv.symm.trans
    (Equiv.sumCongr σ (Equiv.refl (Fin d)))).trans finSumFinEquiv)=_
  rw [Equiv.Perm.sign_symm_trans_trans,Equiv.Perm.sign_sumCongr]
  simp

theorem selected_vf_tail_permutation_sign {n : ℕ} (d : ℕ) (σ : Equiv.Perm (Fin n)) :
    Equiv.Perm.sign (selectedVFTailPermutation d σ)=Equiv.Perm.sign σ := by
  change Equiv.Perm.sign (((finCongr (Nat.add_comm n d)).symm.trans
    (finAppendEquiv σ d)).trans (finCongr (Nat.add_comm n d)))=_
  rw [Equiv.Perm.sign_symm_trans_trans,fin_append_permutation_sign]

theorem selected_vf_tail_rv_permutation_sign {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
    {n : ℕ} (d : ℕ) (σ : Equiv.Perm (Fin n)) :
    rvPermutationSign (M := M) (selectedVFTailPermutation d σ)=rvPermutationSign σ := by
  unfold rvPermutationSign
  rw [selected_vf_tail_permutation_sign]
end IntegrationInACVF.Section7
