import Integration7.SelectedVFTailPermutations
import Integration7.SelectedRVVFTailProgramCarriers
import IntegrationSection6.GammaPermutedFibrePresentations

/-! VF tail realization commutes with each prescribed VF permutation. -/
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section5
open IntegrationInACVF.Section5 IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7

theorem selected_vf_tail_permutation_symm_original {n : ℕ} (d : ℕ)
    (σ : Equiv.Perm (Fin n)) (i : Fin n) :
    (selectedVFTailPermutation d σ).symm (finCongr (Nat.add_comm n d) (Fin.castAdd d i)) =
      finCongr (Nat.add_comm n d) (Fin.castAdd d (σ.symm i)) := by
  apply (selectedVFTailPermutation d σ).injective
  rw [Equiv.apply_symm_apply,selected_vf_tail_permutation_original,Equiv.apply_symm_apply]

theorem selected_vf_tail_permutation_symm_tail {n : ℕ} (d : ℕ)
    (σ : Equiv.Perm (Fin n)) (j : Fin d) :
    (selectedVFTailPermutation d σ).symm (finCongr (Nat.add_comm n d) (Fin.natAdd n j)) =
      finCongr (Nat.add_comm n d) (Fin.natAdd n j) := by
  apply (selectedVFTailPermutation d σ).injective
  rw [Equiv.apply_symm_apply,selected_vf_tail_permutation_tail]

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n a d : ℕ}

theorem native_program_selected_vf_tail_permutation
    (hc : CanonicalStructure.IsCanonical (M := M)) (A : DefSet (M := M) S n a)
    (ρ : Fin d → Fin a) (σ : Equiv.Perm (Fin n)) :
    nativeProgramSelectedRVVFTailLift hc (vfPermutationImage A σ) ρ =
      vfPermutationImage (nativeProgramSelectedRVVFTailLift hc A ρ) (selectedVFTailPermutation d σ) := by
  apply defSet_eq_of_carrier_eq
  ext p
  change (p.1,p.2) ∈ carrier (nativeProgramSelectedRVVFTailLift hc (vfPermutationImage A σ) ρ) ↔
    (p.1,p.2) ∈ carrier (vfPermutationImage (nativeProgramSelectedRVVFTailLift hc A ρ) (selectedVFTailPermutation d σ))
  rw [native_program_selected_rv_vf_tail_carrier,vfPermutationImage_row,
    vfPermutationImage_row,native_program_selected_rv_vf_tail_carrier]
  have hf : (p.1 ∘ (selectedVFTailPermutation d σ).symm) ∘ finCongr (Nat.add_comm n d) ∘ Fin.castAdd d =
      (p.1 ∘ finCongr (Nat.add_comm n d) ∘ Fin.castAdd d) ∘ σ.symm := by
    funext i
    exact congrArg p.1 (selected_vf_tail_permutation_symm_original d σ i)
  have ht : (p.1 ∘ (selectedVFTailPermutation d σ).symm) ∘ finCongr (Nat.add_comm n d) ∘ Fin.natAdd n =
      p.1 ∘ finCongr (Nat.add_comm n d) ∘ Fin.natAdd n := by
    funext j
    exact congrArg p.1 (selected_vf_tail_permutation_symm_tail d σ j)
  rw [hf,ht]

end IntegrationInACVF.Section7
