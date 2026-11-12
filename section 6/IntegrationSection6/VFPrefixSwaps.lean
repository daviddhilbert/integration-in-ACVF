import IntegrationSection6.VFPrefixFibrePresentations
import IntegrationSection6.GammaPermutedFibrePresentations

/-! Swapping the first two VF coordinates commutes with freezing every
remaining coordinate. These are literal coordinate and parameter identities. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section4 SpecialTransformations.Section5
open IntegrationInACVF.Section5
namespace IntegrationInACVF.Section6
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {S : Set M} {n a : ℕ}

def swapFirstTwo (n : ℕ) : Equiv.Perm (Fin (n+2)) := Equiv.swap 0 (0 : Fin (n+1)).succ
abbrev swapTwo : Equiv.Perm (Fin 2) := swapFirstTwo 0

theorem swapFirstTwo_zero (n : ℕ) : swapFirstTwo n 0 = (0 : Fin (n+1)).succ := by simp [swapFirstTwo]
theorem swapFirstTwo_one (n : ℕ) : swapFirstTwo n (0 : Fin (n+1)).succ = 0 := by simp [swapFirstTwo]

theorem swapFirstTwo_tail (j : Fin n) : swapFirstTwo n j.succ.succ = j.succ.succ := by
  apply Equiv.swap_apply_of_ne_of_ne
  · intro h
    have he := congrArg (fun i : Fin (n+2) => i.val) h
    simp only [Fin.val_succ,Fin.val_zero] at he
    omega
  · intro h
    have he := congrArg (fun i : Fin (n+2) => i.val) h
    simp only [Fin.val_succ,Fin.val_zero] at he
    omega

theorem vfPrefixTuple_two (x : Fin n → VF (M := M)) (y : Fin 2 → VF (M := M)) :
    vfPrefixTuple x y = Fin.cons (y 0) (Fin.cons (y (0 : Fin 1).succ) x) := by
  rw [vfPrefixTuple_cons,vfPrefixTuple_cons,vfPrefixTuple_zero]

theorem vfPrefixTuple_two_swap (x : Fin n → VF (M := M)) (y : Fin 2 → VF (M := M)) :
    vfPrefixTuple x (y ∘ swapTwo) = vfPrefixTuple x y ∘ swapFirstTwo n := by
  funext j
  cases j using Fin.cases with
  | zero => simp only [vfPrefixTuple_two,Function.comp_apply,Fin.cons_zero,swapTwo,swapFirstTwo_zero,Fin.cons_succ]
  | succ j =>
    cases j using Fin.cases with
    | zero => simp only [vfPrefixTuple_two,Function.comp_apply,Fin.cons_zero,Fin.cons_succ,swapTwo,swapFirstTwo_one]
    | succ j => simp only [vfPrefixTuple_two,Function.comp_apply,Fin.cons_succ,swapFirstTwo_tail]

theorem vfPrefix_permuted_swap (U : DefSet (M := M) S (n+2) a)
    (σ : Equiv.Perm (Fin (n+2))) (x : Fin n → VF (M := M)) :
    vfPrefixFibre (p := 2) (vfPermutationImage U ((swapFirstTwo n).trans σ)) x =
      vfPermutationImage (vfPrefixFibre (p := 2) (vfPermutationImage U σ) x) swapTwo := by
  apply defSet_eq_of_carrier_eq
  ext q
  have hL := vfPermutationImage_row U ((swapFirstTwo n).trans σ) (vfPrefixTuple x q.1) q.2
  have hR := (vfPermutationImage_row (vfPrefixFibre (p := 2) (vfPermutationImage U σ) x) swapTwo q.1 q.2).trans
    (vfPermutationImage_row U σ (vfPrefixTuple x (q.1 ∘ swapTwo.symm)) q.2)
  have ht : vfPrefixTuple x q.1 ∘ ((swapFirstTwo n).trans σ).symm =
      vfPrefixTuple x (q.1 ∘ swapTwo.symm) ∘ σ.symm := by
    funext i
    change vfPrefixTuple x q.1 ((swapFirstTwo n).symm (σ.symm i)) =
      vfPrefixTuple x (q.1 ∘ swapTwo.symm) (σ.symm i)
    have hFull : (swapFirstTwo n).symm = swapFirstTwo n := Equiv.symm_swap _ _
    have hSmall : swapTwo.symm = swapTwo := Equiv.symm_swap _ _
    rw [hFull,hSmall]
    exact congrFun (vfPrefixTuple_two_swap x q.1).symm (σ.symm i)
  exact hL.trans ((Iff.of_eq (congrArg (fun y => (y,q.2) ∈ carrier U) ht)).trans hR.symm)

end IntegrationInACVF.Section6
