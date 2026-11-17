module

public import Integration7.GradedAEVolumeFunctions
public import Integration7.AEOrdinaryVolumeIntegralLinearMap
public import Integration7.AppendedVolumeIntegralOrdinaryLinearMaps

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! Integration of the full finite graded function space is additive
and ordinary-linear, with the genuine coefficient-first homogeneous
integrals placed in their arithmetic total degrees. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open scoped DirectSum

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

def aeVolumeFunctionComponentIntegralLinearMap
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (Ξ : Set (Values.Gamma (M := M))) (hΞ : Cardinal.mk Ξ < C.κ)
    (hGenerated : VFGammaGeneratedBase (⟨(C.base : Set M),Ξ⟩ : Base (M := M)))
    (hNames : commonRealNames (⟨(C.base : Set M),Ξ⟩ : Base (M := M)) ⊆ (C.base : Set M))
    (γ : Values.Gamma (M := M)) (hγ : γ ∈ Ξ) (hγ1 : 1 < γ) (n j : ℕ) :
    AEVolumeFunctionComponent hc C n j →ₗ[RVVolumeBlowupClasses hc C 0] RVVolumeBlowupClasses hc C ((n+j)+1) := by
  cases j with
  | zero => exact aeOrdinaryRVVolumeFunctionIntegralLinearMap hc C Ξ hΞ hGenerated hNames γ hγ hγ1 n
  | succ k =>
    have h : n+(k+1)=appendVolumeDegree (n+1) k := by rw [append_volume_degree_eq]; omega
    exact (positiveVolumeClassDegreeReindexOrdinaryLinearEquiv hc C h).toLinearMap.comp
      (aeRVVolumeFunctionAppendedIntegralOrdinaryLinearMap hc C Ξ hΞ hGenerated hNames γ hγ hγ1 n k)

def gradedAEVolumeIntegralOrdinaryLinearMap
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (Ξ : Set (Values.Gamma (M := M))) (hΞ : Cardinal.mk Ξ < C.κ)
    (hGenerated : VFGammaGeneratedBase (⟨(C.base : Set M),Ξ⟩ : Base (M := M)))
    (hNames : commonRealNames (⟨(C.base : Set M),Ξ⟩ : Base (M := M)) ⊆ (C.base : Set M))
    (γ : Values.Gamma (M := M)) (hγ : γ ∈ Ξ) (hγ1 : 1 < γ) (n : ℕ) :
    GradedAEVolumeFunction hc C n →ₗ[RVVolumeBlowupClasses hc C 0] RVVolumeBlowupSemiring hc C :=
  DirectSum.toModule _ _ _ (fun j =>
    (DirectSum.lof (RVVolumeBlowupClasses hc C 0) ℕ (RVVolumeBlowupClasses hc C) ((n+j)+1)).comp
      (aeVolumeFunctionComponentIntegralLinearMap hc C Ξ hΞ hGenerated hNames γ hγ hγ1 n j))

theorem graded_ae_volume_integral_of
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (Ξ : Set (Values.Gamma (M := M))) (hΞ : Cardinal.mk Ξ < C.κ)
    (hGenerated : VFGammaGeneratedBase (⟨(C.base : Set M),Ξ⟩ : Base (M := M)))
    (hNames : commonRealNames (⟨(C.base : Set M),Ξ⟩ : Base (M := M)) ⊆ (C.base : Set M))
    (γ : Values.Gamma (M := M)) (hγ : γ ∈ Ξ) (hγ1 : 1 < γ) (n j : ℕ)
    (f : AEVolumeFunctionComponent hc C n j) :
    gradedAEVolumeIntegralOrdinaryLinearMap hc C Ξ hΞ hGenerated hNames γ hγ hγ1 n
      (DirectSum.of (AEVolumeFunctionComponent hc C n) j f) =
      DirectSum.of (RVVolumeBlowupClasses hc C) ((n+j)+1)
        (aeVolumeFunctionComponentIntegralLinearMap hc C Ξ hΞ hGenerated hNames γ hγ hγ1 n j f) :=
  DirectSum.toAddMonoid_of _ j f

end IntegrationInACVF.Section7
