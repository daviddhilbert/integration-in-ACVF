import Integration7.PermutationRVJacobian
import Section4.ResidueParameterField

/-! The genuine determinant sign is already named by every substructure. -/

noncomputable section
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section4.ResiduePurity

namespace IntegrationInACVF.Section7

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n : ℕ}

theorem rvPermutationSign_mem (B : LRV.Substructure M) (e : Equiv.Perm (Fin n)) :
    (rvPermutationSign (M := M) e).val ∈ B :=
  (residueParameterField B).intCast_mem (Equiv.Perm.sign e : ℤ)

end IntegrationInACVF.Section7
