import IntegrationSection6.GammaPermutedFibrePresentations

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section5
open IntegrationInACVF.Section5
namespace IntegrationInACVF.Section6
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {S : Set M} {n a : ℕ}

theorem vfPermutation_finite_rv_fibres (U : DefSet (M := M) S n a) (σ : Equiv.Perm (Fin n))
    (hfin : ∀ x : Fin n → VF (M := M), {r : Fin a → RV (M := M) | (x,r) ∈ carrier U}.Finite) :
    ∀ x : Fin n → VF (M := M), {r : Fin a → RV (M := M) | (x,r) ∈ carrier (vfPermutationImage U σ)}.Finite := by
  intro x
  have he : {r : Fin a → RV (M := M) | (x,r) ∈ carrier (vfPermutationImage U σ)} =
      {r | (x ∘ σ.symm,r) ∈ carrier U} := Set.ext (vfPermutationImage_row U σ x)
  rw [he]
  exact hfin _

end IntegrationInACVF.Section6
