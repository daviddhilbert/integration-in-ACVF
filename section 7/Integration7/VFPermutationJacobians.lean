import Section9.VFJacobian

/-! Simultaneously permuting the input and output VF coordinates leaves
the actual partial Jacobian unchanged. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section9

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n : ℕ}

set_option maxHeartbeats 1600000 in
theorem vf_jacobian_conjugate_permutation
    {f : (Fin n → VFType (M := M)) → Fin n → VFType (M := M)}
    {a : Fin n → VFType (M := M)} {J : VFType (M := M)}
    (hf : HasVFJacobianAt f a J) (σ : Equiv.Perm (Fin n)) :
    HasVFJacobianAt (fun y => f (y ∘ σ.symm) ∘ σ) (a ∘ σ) J := by
  classical
  obtain ⟨A,hA,hdet⟩ := hf
  refine ⟨A.submatrix σ σ,fun i j ε => ?_,?_⟩
  · obtain ⟨δ,hδ⟩ := hA (σ i) (σ j) ε
    refine ⟨δ,fun t ht hnear => ?_⟩
    have hInput : ((a ∘ σ) + Pi.single j t) ∘ σ.symm = a + Pi.single (σ j) t := by
      funext k
      simp only [Function.comp_apply,Pi.add_apply,Equiv.apply_symm_apply,Pi.single_apply]
      by_cases hk : k = σ j
      · subst k
        simp
      · have hk' : σ.symm k ≠ j := fun he => hk (by rw [← he,σ.apply_symm_apply])
        simp only [hk,hk',if_false]
    have hBase : (a ∘ σ) ∘ σ.symm = a := by funext k; simp
    simpa only [hInput,hBase,Function.comp_apply,Matrix.submatrix_apply] using hδ t ht hnear
  · exact (Matrix.det_submatrix_equiv_self σ A).trans hdet

end IntegrationInACVF.Section7
