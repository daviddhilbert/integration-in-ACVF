import Integration7.PureVFFormulaLoci
import Section4.CoordinateMaps

/-! Literal VF coordinate permutations on raw mixed domains, together
with their definable inverse and unchanged RV labels. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n a : ℕ}

def mixedVFPermutationDomain (A : DefSet (rawMixedSpace (M := M) n a) S)
    (σ : Equiv.Perm (Fin n)) : DefSet (rawMixedSpace (M := M) n a) S := (vfSelect σ A).image

def mixedVFPermutationBijection (A : DefSet (rawMixedSpace (M := M) n a) S)
    (σ : Equiv.Perm (Fin n)) : Map A (mixedVFPermutationDomain A σ) := (vfSelect σ A).toImage

theorem mixed_vf_permutation_bijective (A : DefSet (rawMixedSpace (M := M) n a) S)
    (σ : Equiv.Perm (Fin n)) : Function.Bijective (mixedVFPermutationBijection A σ) := by
  constructor
  · intro p q hpq
    have h := congrArg Subtype.val hpq
    change (p.val.1 ∘ σ,p.val.2) = (q.val.1 ∘ σ,q.val.2) at h
    apply Subtype.ext
    apply Prod.ext
    · funext i
      have hi := congrArg (fun w => w.1 (σ.symm i)) h
      simpa only [vfSelect_apply,Function.comp_apply,σ.apply_symm_apply] using hi
    · have h₂ := congrArg Prod.snd h
      exact h₂
  · rintro ⟨p,u,hu⟩
    exact ⟨u,Subtype.ext hu⟩

theorem mixed_vf_permutation_inverse_value
    (A : DefSet (rawMixedSpace (M := M) n a) S) (σ : Equiv.Perm (Fin n))
    (p : mixedVFPermutationDomain A σ) :
    (Map.inverse (mixedVFPermutationBijection A σ) (mixed_vf_permutation_bijective A σ) p).val =
      (p.val.1 ∘ σ.symm,p.val.2) := by
  let u := Map.inverse (mixedVFPermutationBijection A σ) (mixed_vf_permutation_bijective A σ) p
  have h := congrArg Subtype.val (Map.apply_inverse (mixedVFPermutationBijection A σ)
    (mixed_vf_permutation_bijective A σ) p)
  change (u.val.1 ∘ σ,u.val.2) = p.val at h
  apply Prod.ext
  · funext i
    have hi := congrArg (fun w => w.1 (σ.symm i)) h
    simpa only [Function.comp_apply,σ.apply_symm_apply] using hi
  · have h₂ := congrArg Prod.snd h
    exact h₂

theorem mem_mixed_vf_permutation_domain
    (A : DefSet (rawMixedSpace (M := M) n a) S) (σ : Equiv.Perm (Fin n))
    (x : Fin n → VFType (M := M)) (r : Fin a → CanonicalRV.RVSort M) :
    (x,r) ∈ (mixedVFPermutationDomain A σ).carrier ↔ (x ∘ σ.symm,r) ∈ A.carrier := by
  constructor
  · intro h
    let p : mixedVFPermutationDomain A σ := ⟨(x,r),h⟩
    have hp := (Map.inverse (mixedVFPermutationBijection A σ) (mixed_vf_permutation_bijective A σ) p).property
    rwa [mixed_vf_permutation_inverse_value A σ p] at hp
  · intro h
    refine ⟨⟨(x ∘ σ.symm,r),h⟩,?_⟩
    apply Prod.ext
    · funext i
      exact congrArg x (σ.symm_apply_apply i)
    · rfl

end IntegrationInACVF.Section7
