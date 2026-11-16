module

public import Integration7.AEOrdinaryVolumePermutations
public import Integration7.AEOrdinaryRVVolumeIntegrals
public import Integration7.VFVolumeIntegralPermutationCovariance

@[expose] public section

/-! Ordinary-valued families have the same exact raw coordinate
covariance as positive-valued families, through their actual unit-density
VF realizations. No point cancellation or normalization is used. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.DefinableGeometry
namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n a : ℕ}
variable (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)

def ordinaryPermutationRealizationBijection (F : OrdinaryVFVolumeFamily C (n+1) a)
    (σ : Equiv.Perm (Fin (n+1))) :
    VFVolumeBijection (F.permuteBase σ).fullVFObject (F.fullVFObject.permuteVF σ) := by
  apply VFVolumeBijection.of_preserving_vf_and_density hc C (Map.id _) Function.bijective_id
  · intro q; rfl
  · intro q
    rfl

variable (Ξ : Set (Values.Gamma (M := M))) (hΞ : Cardinal.mk Ξ < C.κ)
variable (hGenerated : VFGammaGeneratedBase (⟨(C.base : Set M),Ξ⟩ : Base (M := M)))
variable (hNames : commonRealNames (⟨(C.base : Set M),Ξ⟩ : Base (M := M)) ⊆ (C.base : Set M))
variable (γ : Values.Gamma (M := M)) (hγ : γ ∈ Ξ) (hγ1 : 1 < γ)

theorem ae_ordinary_volume_integral_permute_base
    (f : AEOrdinaryRVVolumeFunction hc C n) (σ : Equiv.Perm (Fin (n+1))) :
    aeOrdinaryRVVolumeFunctionIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1
      (aeOrdinaryRVVolumeFunctionPermuteBase hc C σ f) =
    positiveVolumeClassPermute hc C σ
      (aeOrdinaryRVVolumeFunctionIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 f) := by
  induction f using Quotient.inductionOn with
  | h F =>
    change positiveVolumeIntegrationEquiv hc C Ξ hΞ hGenerated hNames γ hγ hγ1
      (positiveVFVolumeIsoClass hc C (F.2.permuteBase σ).fullVFObject) = _
    have hClass := (positiveVFVolumeIsoClass_eq_iff hc C).mpr
      ⟨VFVolumeIso.of_bijection (ordinaryPermutationRealizationBijection hc C F.2 σ)⟩
    exact (congrArg (positiveVolumeIntegrationEquiv hc C Ξ hΞ hGenerated hNames γ hγ hγ1) hClass).trans
      (positive_vf_volume_integral_permutation_covariance hc C Ξ hΞ hGenerated hNames γ hγ hγ1 F.2.fullVFObject σ)
end IntegrationInACVF.Section7
