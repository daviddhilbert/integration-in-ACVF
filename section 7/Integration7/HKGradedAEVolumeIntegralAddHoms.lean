import Integration7.HKGradedAEVolumeFunctions
import Integration7.HKAEZeroIntegralAddHom
import Integration7.AppendedVolumeIntegralAddHom

/-! Genuine homogeneous integrals assemble additively in the actual
weighted-zero graded coefficient semiring, retaining arithmetic degrees. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open scoped DirectSum

namespace IntegrationInACVF.Section7.HK
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
variable (Ξ : Set (Values.Gamma (M := M))) (hΞ : Cardinal.mk Ξ < C.κ)
variable (hGenerated : VFGammaGeneratedBase (⟨(C.base : Set M),Ξ⟩ : Base (M := M)))
variable (hNames : commonRealNames (⟨(C.base : Set M),Ξ⟩ : Base (M := M)) ⊆ (C.base : Set M))
variable (γ : Values.Gamma (M := M)) (hγ : γ ∈ Ξ) (hγ1 : 1 < γ)

def aeVolumeFunctionComponentIntegralAddHom (n j : ℕ) :
    AEVolumeFunctionComponent hc C n j →+ PositiveVolumeBlowupClasses hc C (n+j) := by
  cases j with
  | zero => exact aeZeroVolumeFunctionIntegralAddHom hc C Ξ hΞ hGenerated hNames γ hγ hγ1 n
  | succ k =>
    have h : n+(k+1)=appendVolumeDegree (n+1) k := by rw [append_volume_degree_eq]; omega
    exact (positiveVolumeClassDegreeReindexAddEquiv hc C h).toAddMonoidHom.comp
      (aeRVVolumeFunctionAppendedIntegralAddHom hc C Ξ hΞ hGenerated hNames γ hγ hγ1 n k)

def gradedAEVolumeIntegralAddHom (n : ℕ) :
    GradedAEVolumeFunction hc C n →+ RVVolumeBlowupSemiring hc C := by
  letI : ∀ d, AddCommMonoid (RVBlowupClasses hc C d) := rvVolumeBlowupClassesAddCommMonoid hc C
  exact DirectSum.toAddMonoid (fun j =>
    (DirectSum.of (RVBlowupClasses hc C) ((n+j)+1)).comp
      (aeVolumeFunctionComponentIntegralAddHom hc C Ξ hΞ hGenerated hNames γ hγ hγ1 n j))

theorem graded_ae_volume_integral_of (n j : ℕ) (f : AEVolumeFunctionComponent hc C n j) :
    gradedAEVolumeIntegralAddHom hc C Ξ hΞ hGenerated hNames γ hγ hγ1 n
      (DirectSum.of (AEVolumeFunctionComponent hc C n) j f) =
      DirectSum.of (RVBlowupClasses hc C) ((n+j)+1)
        (aeVolumeFunctionComponentIntegralAddHom hc C Ξ hΞ hGenerated hNames γ hγ hγ1 n j f) :=
  DirectSum.toAddMonoid_of _ j f

theorem ae_volume_component_integral_zero (n : ℕ) (f : AEZeroVolumeFunction hc C n) :
    aeVolumeFunctionComponentIntegralAddHom hc C Ξ hΞ hGenerated hNames γ hγ hγ1 n 0 f =
      aeZeroVolumeFunctionIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 f := rfl

theorem ae_volume_component_integral_positive_heq (n k : ℕ) (f : AERVVolumeFunction hc C n k) :
    HEq (aeVolumeFunctionComponentIntegralAddHom hc C Ξ hΞ hGenerated hNames γ hγ hγ1 n (k+1) f)
      (aeRVVolumeFunctionAppendedIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 f) := by
  have h : n+(k+1)=appendVolumeDegree (n+1) k := by rw [append_volume_degree_eq]; omega
  exact positive_volume_class_reindex_degree_heq hc C h
    (aeRVVolumeFunctionAppendedIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 f)

end IntegrationInACVF.Section7.HK
