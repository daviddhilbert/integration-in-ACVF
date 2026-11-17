module

public import Integration7.MixedVFPermutationDomains
public import Integration7.SelectedVolumeRowContexts

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! VF reindexing of actual selected volume families. The original
RV labels, selected tuple and density are transported by the definable
inverse of the VF coordinate permutation. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.DefinableGeometry

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {C : BaseContext M} {n a k : ℕ}

def SelectedVFVolumeFamily.permuteBase (F : SelectedVFVolumeFamily C n a k)
    (σ : Equiv.Perm (Fin n)) : SelectedVFVolumeFamily C n a k where
  domain := mixedVFPermutationDomain F.domain σ
  selected := F.selected
  finite_selected x t := (F.finite_selected (x ∘ σ.symm) t).subset (by
    rintro r ⟨hr,ht⟩
    exact ⟨(mem_mixed_vf_permutation_domain F.domain σ x r).mp hr,ht⟩)
  form := F.form.pullback
    (Map.inverse (mixedVFPermutationBijection F.domain σ) (mixed_vf_permutation_bijective F.domain σ))

theorem SelectedVFVolumeFamily.permuteBase_row_carrier
    (F : SelectedVFVolumeFamily C n a k) (σ : Equiv.Perm (Fin n))
    (x : Fin n → VFType (M := M)) (r : Fin a → CanonicalRV.RVSort M) :
    r ∈ ((F.permuteBase σ).rowInContext x).underlying.obj.domain.carrier ↔
      (x ∘ σ.symm,r) ∈ F.domain.carrier :=
  mem_mixed_vf_permutation_domain F.domain σ x r

theorem SelectedVFVolumeFamily.permuteBase_density
    (F : SelectedVFVolumeFamily C n a k) (σ : Equiv.Perm (Fin n))
    (p : (F.permuteBase σ).domain) :
    (F.permuteBase σ).form.value p = F.form.value
      ⟨(p.val.1 ∘ σ.symm,p.val.2),(mem_mixed_vf_permutation_domain F.domain σ p.val.1 p.val.2).mp p.property⟩ := by
  apply congrArg F.form.value
  exact Subtype.ext (mixed_vf_permutation_inverse_value F.domain σ p)

theorem vf_parameter_volume_context_permutation_subset
    (C : BaseContext M) (σ : Equiv.Perm (Fin n)) (x : Fin n → VFType (M := M)) :
    ((vfParameterVolumeContext C (x ∘ σ.symm)).base : Set M) ⊆
      ((vfParameterVolumeContext C x).base : Set M) := by
  change (Substructure.closure LRV ((C.base : Set M) ∪ Set.range (fun i => ((x ∘ σ.symm) i).val)) :
    Substructure LRV M) ≤ (vfParameterVolumeContext C x).base
  apply Substructure.closure_le.mpr
  rintro z (hz | ⟨i,rfl⟩)
  · exact vfParameterVolumeContext_contains C x (Or.inl hz)
  · exact vfParameterVolumeContext_contains C x (Or.inr ⟨σ.symm i,rfl⟩)

end IntegrationInACVF.Section7
