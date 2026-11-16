module

public import Integration7.PermutedVolumeFamilies
public import Integration7.PointwiseRVVolumeFunctions
public import Integration7.BlowupParameterExtension

@[expose] public section

/-! Reindexed VF families have the literal original RV fibre, with
its unchanged density, in the same finitely generated VF context. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.DefinableGeometry

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {C : BaseContext M} {n a b k : ℕ}

def permutedVolumeFamilyRowIso
    (hc : CanonicalStructure.IsCanonical (M := M)) (F : SelectedVFVolumeFamily C n a k)
    (σ : Equiv.Perm (Fin n)) (x : Fin n → VFType (M := M)) :
    RVVolumeIso ((F.permuteBase σ).rowInContext x)
      ((F.rowInContext (x ∘ σ.symm)).extend (vf_parameter_volume_context_permutation_subset C σ x)) := by
  let D := vfParameterVolumeContext C x
  let U := (F.permuteBase σ).rowInContext x
  let V := (F.rowInContext (x ∘ σ.symm)).extend (vf_parameter_volume_context_permutation_subset C σ x)
  let f : Map U.underlying.obj.domain V.underlying.obj.domain :=
    Map.inclusion (fun r hr => (F.permuteBase_row_carrier σ x r).mp hr)
  have hf : Function.Bijective f := by
    constructor
    · intro u v h
      have he := congrArg Subtype.val h
      exact Subtype.ext he
    · intro v
      exact ⟨⟨v.val,(F.permuteBase_row_carrier σ x v.val).mpr v.property⟩,rfl⟩
  have hCoord : ∀ u, V.underlying.obj.value (f u) = U.underlying.obj.value u := fun _ => rfl
  have hForm : ∀ u, V.form.value (f u) = U.form.value u := by
    intro u
    change F.form.value ⟨(x ∘ σ.symm,u.val),_⟩ = (F.permuteBase σ).form.value ⟨(x,u.val),_⟩
    exact (F.permuteBase_density σ ⟨(x,u.val),u.property⟩).symm
  exact RVVolumeIso.of_preserving_coordinates_full hc D
    (rvFiniteIsoOfAmbient (rvIsoOfVolumePreservingBijection f hf hCoord)) hCoord hForm

theorem permuted_volume_family_common_at
    (hc : CanonicalStructure.IsCanonical (M := M))
    (F : SelectedVFVolumeFamily C n a k) (G : SelectedVFVolumeFamily C n b k)
    (σ : Equiv.Perm (Fin n)) (x : Fin n → VFType (M := M))
    (h : VolumeBlowupEquivalent (F.rowInContext (x ∘ σ.symm)) (G.rowInContext (x ∘ σ.symm))) :
    VolumeBlowupEquivalent ((F.permuteBase σ).rowInContext x) ((G.permuteBase σ).rowInContext x) := by
  let D := vfParameterVolumeContext C x
  have hF := VolumeBlowupEquivalent.of_iso D (permutedVolumeFamilyRowIso hc F σ x)
  have hG := VolumeBlowupEquivalent.of_iso D ((permutedVolumeFamilyRowIso hc G σ x).symm hc D)
  exact (hF.trans hc D (h.extend (vf_parameter_volume_context_permutation_subset C σ x))).trans hc D hG

def pointwiseRVVolumeFunctionPermuteBase
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M) (σ : Equiv.Perm (Fin n)) :
    PointwiseRVVolumeFunction hc C n k → PointwiseRVVolumeFunction hc C n k :=
  Quotient.map (fun F => ⟨F.1,F.2.permuteBase σ⟩) (by
    intro F G h x
    exact (positiveVolumeBlowupClass_eq_iff hc (vfParameterVolumeContext C x)).mpr
      (permuted_volume_family_common_at hc F.2 G.2 σ x
        ((positiveVolumeBlowupClass_eq_iff hc (vfParameterVolumeContext C (x ∘ σ.symm))).mp (h (x ∘ σ.symm)))))

end IntegrationInACVF.Section7
