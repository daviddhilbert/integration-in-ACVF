module

public import Integration7.PermutedVolumeFamilyRows
public import Integration7.PureVFPermutationDimensions
public import Integration7.AERVVolumeFunctions

@[expose] public section

/-! Arbitrary VF coordinate permutations act on the actual
almost-everywhere function quotient. Exceptional sets are carried by
genuine definable bijections and retain their VF dimension. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section4

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n a b k : ℕ}

theorem ae_volume_family_permute_base
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (F : SelectedVFVolumeFamily C (n+1) a k) (G : SelectedVFVolumeFamily C (n+1) b k)
    (σ : Equiv.Perm (Fin (n+1))) (h : AERVVolumeFunctionEquivalent hc C ⟨a,F⟩ ⟨b,G⟩) :
    AERVVolumeFunctionEquivalent hc C ⟨a,F.permuteBase σ⟩ ⟨b,G.permuteBase σ⟩ := by
  obtain ⟨E,hE,hRows⟩ := h
  refine ⟨(pureVFPermutationMap E σ).image,by rw [pure_vf_permutation_dimension]; exact hE,?_⟩
  intro x hx
  have hy : x ∘ σ.symm ∉ E.carrier := by
    intro h
    apply hx
    refine ⟨⟨x ∘ σ.symm,h⟩,?_⟩
    funext i
    exact congrArg x (σ.symm_apply_apply i)
  exact (positiveVolumeBlowupClass_eq_iff hc (vfParameterVolumeContext C x)).mpr
    (permuted_volume_family_common_at hc F G σ x
      ((positiveVolumeBlowupClass_eq_iff hc (vfParameterVolumeContext C (x ∘ σ.symm))).mp (hRows _ hy)))

def aeRVVolumeFunctionPermuteBase
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M) (σ : Equiv.Perm (Fin (n+1))) :
    AERVVolumeFunction hc C n k → AERVVolumeFunction hc C n k :=
  Quotient.map (fun F => ⟨F.1,F.2.permuteBase σ⟩)
    (fun F G h => ae_volume_family_permute_base hc C F.2 G.2 σ h)

theorem ae_rv_volume_function_permute_base_representative
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M) (σ : Equiv.Perm (Fin (n+1)))
    (F : SelectedVFVolumeFamily C (n+1) a k) :
    aeRVVolumeFunctionPermuteBase hc C σ (Quotient.mk _ ⟨a,F⟩) = Quotient.mk _ ⟨a,F.permuteBase σ⟩ := rfl

theorem ae_rv_volume_permute_base_of_pointwise
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M) (σ : Equiv.Perm (Fin (n+1)))
    (f : PointwiseRVVolumeFunction hc C (n+1) k) :
    aeRVVolumeFunctionPermuteBase hc C σ (pointwiseToAERVVolumeFunction hc C f) =
      pointwiseToAERVVolumeFunction hc C (pointwiseRVVolumeFunctionPermuteBase hc C σ f) := by
  induction f using Quotient.inductionOn with
  | h F => rfl

end IntegrationInACVF.Section7
