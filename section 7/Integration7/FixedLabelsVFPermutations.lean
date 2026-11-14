import Integration7.NativeFixedRVLabels
import IntegrationSection6.StandardProgramPresentations

/-! Adjoining fixed RV labels commutes with actual VF coordinate
permutations, retaining the exact native definable domains. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section5 IntegrationInACVF.Section5 IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {S : Set M} {n a d : ℕ}

theorem fixed_rv_label_domain_vf_permutation (A : DefSet (M := M) S n a)
    (t : Fin d → RV (M := M)) (ht : ∀ i, (t i).val ∈ S) (σ : Equiv.Perm (Fin n)) :
    fixedRVLabelDomain (vfPermutationImage A σ) t ht = vfPermutationImage (fixedRVLabelDomain A t ht) σ := by
  apply PresentedSet.eq_of_carrier_eq
  ext p
  rw [fixed_rv_label_domain_carrier]
  change ((p.1,p.2 ∘ Fin.castAdd d) ∈ carrier (vfPermutationImage A σ) ∧ p.2 ∘ Fin.natAdd a = t) ↔
    (p.1,p.2) ∈ carrier (vfPermutationImage (fixedRVLabelDomain A t ht) σ)
  rw [vfPermutationImage_row,vfPermutationImage_row,fixed_rv_label_domain_carrier]
  rfl

end IntegrationInACVF.Section7
