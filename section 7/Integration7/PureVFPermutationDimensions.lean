module

public import Integration7.MixedVFPermutationDomains

@[expose] public section

/-! Actual definable VF coordinate permutations preserve the dimension
of pure VF exceptional sets over the original real parameter base. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n : ℕ}

def pureVFPermutationMap (E : DefSet (rawVFSpace (M := M) n) S) (σ : Equiv.Perm (Fin n)) :
    Map E (DefSet.univ (rawVFSpace (M := M) n) S) :=
  (Map.fst (rawVFSpace n) (rawRVSpace 1) S (DefSet.univ (rawMixedSpace n 1) S)).comp
    ((vfSelect σ (pureVFGraphMap E).image).comp (pureVFGraphMap E).toImage)

@[simp] theorem pure_vf_permutation_map_value
    (E : DefSet (rawVFSpace (M := M) n) S) (σ : Equiv.Perm (Fin n)) (x : E) :
    (pureVFPermutationMap E σ x).val = x.val ∘ σ := rfl

theorem pure_vf_permutation_map_bijective
    (E : DefSet (rawVFSpace (M := M) n) S) (σ : Equiv.Perm (Fin n)) :
    Function.Bijective (pureVFPermutationMap E σ).toImage := by
  constructor
  · intro x y h
    have he := congrArg Subtype.val h
    change x.val ∘ σ = y.val ∘ σ at he
    apply Subtype.ext
    funext i
    have hi := congrFun he (σ.symm i)
    simpa only [pure_vf_permutation_map_value,Function.comp_apply,σ.apply_symm_apply] using hi
  · rintro ⟨x,u,hu⟩
    exact ⟨u,Subtype.ext hu⟩

theorem pure_vf_dimension_eq_of_bijective
    {A B : DefSet (rawVFSpace (M := M) n) S} (f : Map A B) (hf : Function.Bijective f) :
    vfDim (rawRVSpace (M := M) 1) B = vfDim (rawRVSpace (M := M) 1) A := by
  have hi : Function.Injective (f.inverse hf) := (Equiv.ofBijective f hf).symm.injective
  exact le_antisymm
    (Dimension.dim_le_of_finiteFibres rawVFSpace (AuxiliaryCoordinates.space (rawRVSpace (M := M) 1))
      (f.inverse hf) (Map.finiteFibres_of_injective hi) ⟨n,pure_vf_has_dimension_bound A⟩)
    (Dimension.dim_le_of_finiteFibres rawVFSpace (AuxiliaryCoordinates.space (rawRVSpace (M := M) 1))
      f (Map.finiteFibres_of_injective hf.1) ⟨n,pure_vf_has_dimension_bound B⟩)

theorem pure_vf_permutation_dimension
    (E : DefSet (rawVFSpace (M := M) n) S) (σ : Equiv.Perm (Fin n)) :
    vfDim (rawRVSpace (M := M) 1) (pureVFPermutationMap E σ).image = vfDim (rawRVSpace (M := M) 1) E :=
  pure_vf_dimension_eq_of_bijective _ (pure_vf_permutation_map_bijective E σ)

end IntegrationInACVF.Section7
