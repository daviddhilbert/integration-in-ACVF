module

public import Integration7.VFBlockProductPartials
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! The VF Jacobian of the actual ordered Cartesian product is the
product of its two Jacobians, via the literal block diagonal matrix. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section9

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n m : ℕ}
local notation "VF" => VFType (M := M)

theorem has_vf_jacobian_block_product
    (F : (Fin n → VF) → Fin n → VF) (G : (Fin m → VF) → Fin m → VF)
    (a : Fin n → VF) (b : Fin m → VF) (J K : VF)
    (hF : HasVFJacobianAt F a J) (hG : HasVFJacobianAt G b K) :
    HasVFJacobianAt (tupleBlockProduct F G) (Fin.append a b) (J*K) := by
  classical
  obtain ⟨A,hA,hdetA⟩ := hF
  obtain ⟨B,hB,hdetB⟩ := hG
  refine ⟨Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks A 0 0 B),?_,?_⟩
  · intro i j
    obtain ⟨i,rfl⟩ := finSumFinEquiv.surjective i
    obtain ⟨j,rfl⟩ := finSumFinEquiv.surjective j
    cases i with
    | inl i =>
      cases j with
      | inl j =>
        simp only [Matrix.reindex_apply,Matrix.submatrix_apply,Equiv.symm_apply_apply,Matrix.fromBlocks_apply₁₁]
        simpa only [finSumFinEquiv_apply_left,finSumFinEquiv_apply_right] using
          vf_block_product_partial_left_left F G a b j i (A i j) (hA i j)
      | inr j =>
        simp only [Matrix.reindex_apply,Matrix.submatrix_apply,Equiv.symm_apply_apply,Matrix.fromBlocks_apply₁₂,Matrix.zero_apply]
        simpa only [finSumFinEquiv_apply_left,finSumFinEquiv_apply_right] using
          vf_block_product_partial_left_right F G a b j i
    | inr i =>
      cases j with
      | inl j =>
        simp only [Matrix.reindex_apply,Matrix.submatrix_apply,Equiv.symm_apply_apply,Matrix.fromBlocks_apply₂₁,Matrix.zero_apply]
        simpa only [finSumFinEquiv_apply_left,finSumFinEquiv_apply_right] using
          vf_block_product_partial_right_left F G a b j i
      | inr j =>
        simp only [Matrix.reindex_apply,Matrix.submatrix_apply,Equiv.symm_apply_apply,Matrix.fromBlocks_apply₂₂]
        simpa only [finSumFinEquiv_apply_left,finSumFinEquiv_apply_right] using
          vf_block_product_partial_right_right F G a b j i (B i j) (hB i j)
  · rw [Matrix.det_reindex_self,Matrix.det_fromBlocks_zero₂₁,hdetA,hdetB]

end IntegrationInACVF.Section7
