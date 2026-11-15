import IntegrationSection6.GammaPermutedUnaryMaps

/-! Literal inverse and conjugation values for the actual VF permutation maps. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section5
open IntegrationInACVF.Section5 IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {S : Set M} {n a b : ℕ}

theorem vf_permutation_inverse_value (A : DefSet (M := M) S n a)
    (σ : Equiv.Perm (Fin n)) (u : vfPermutationImage A σ) :
    (Map.inverse (vfPermutationBijection A σ) (vfPermutationBijection_bijective A σ) u).val =
      vfPermutation σ.symm u.val := by
  let p := Map.inverse (vfPermutationBijection A σ) (vfPermutationBijection_bijective A σ) u
  have h := congrArg (fun q : vfPermutationImage A σ => q.val)
    (Map.apply_inverse (vfPermutationBijection A σ) (vfPermutationBijection_bijective A σ) u)
  change vfPermutation σ p.val = u.val at h
  exact (vfPermutation_inverse σ p.val).symm.trans (congrArg (vfPermutation σ.symm) h)

theorem vf_permuted_map_value {A : DefSet (M := M) S n a} {B : DefSet (M := M) S n b}
    (f : Map A B) (σ : Equiv.Perm (Fin n)) (u : vfPermutationImage A σ) :
    (vfPermutedMap f σ u).val = vfPermutation σ
      (f (Map.inverse (vfPermutationBijection A σ) (vfPermutationBijection_bijective A σ) u)).val := rfl

end IntegrationInACVF.Section7
