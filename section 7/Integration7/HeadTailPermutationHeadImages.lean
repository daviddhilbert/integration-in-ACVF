import Integration7.HeadTailPermutationFibres
import Integration7.HeadImageCoordinateWitnesses

/-! Taking the head contraction image commutes literally with a
permutation of the retained VF tail. -/
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section5
open IntegrationInACVF.Section5 IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n a : ℕ}

theorem head_image_tail_permutation (A : DefSet (M := M) S (n+1) a) (τ : Equiv.Perm (Fin n)) :
    headImage (vfPermutationImage A (headTailPerm τ)) = vfPermutationImage (headImage A) τ := by
  apply defSet_eq_of_carrier_eq
  ext p
  change (p.1,p.2) ∈ carrier (headImage (vfPermutationImage A (headTailPerm τ))) ↔
    (p.1,p.2) ∈ carrier (vfPermutationImage (headImage A) τ)
  rw [vfPermutationImage_row,mem_head_image_coordinate_witness,mem_head_image_coordinate_witness]
  apply exists_congr
  intro v
  rw [vfPermutationImage_row,headTailPerm_cons]

end IntegrationInACVF.Section7
