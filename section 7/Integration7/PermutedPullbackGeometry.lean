import IntegrationSection6.GammaPermutedUnaryMaps

/-! VF permutations preserve full RV pullbacks. A permutation followed
by its inverse gives an actual definable bijection fixing every point
coordinate, even though its target retains the two image presentations. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section5
open IntegrationInACVF.Section5 IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {S : Set M} {n m : ℕ}

theorem vf_permutation_image_pullback (A : DefSet (M := M) S n m)
    (hA : IsRVPullback (carrier A)) (σ : Equiv.Perm (Fin n)) :
    IsRVPullback (carrier (vfPermutationImage A σ)) := by
  apply (isRVPullback_iff _).mpr
  intro p hp q he
  have hpA := (vfPermutationImage_row A σ p.1 p.2).mp hp
  apply (vfPermutationImage_row A σ q.1 q.2).mpr
  apply (isRVPullback_iff _).mp hA _ hpA
  obtain ⟨hVF,hRV⟩ := (sameRV_iff _ _).mp he
  apply (sameRV_iff _ _).mpr
  exact ⟨fun j => hVF (σ.symm j),hRV⟩

def doubleVFPermutationMap (A : DefSet (M := M) S n m) (σ : Equiv.Perm (Fin n)) :
    Map A (vfPermutationImage (vfPermutationImage A σ) σ.symm) :=
  Map.comp (vfPermutationBijection (vfPermutationImage A σ) σ.symm) (vfPermutationBijection A σ)

theorem double_vf_permutation_bijective (A : DefSet (M := M) S n m) (σ : Equiv.Perm (Fin n)) :
    Function.Bijective (doubleVFPermutationMap A σ) :=
  (vfPermutationBijection_bijective _ σ.symm).comp (vfPermutationBijection_bijective A σ)

theorem double_vf_permutation_value (A : DefSet (M := M) S n m) (σ : Equiv.Perm (Fin n)) (p : A) :
    (doubleVFPermutationMap A σ p).val = p.val :=
  vfPermutation_inverse σ p.val

end IntegrationInACVF.Section7
