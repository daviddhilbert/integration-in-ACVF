module

public import Integration7.NormalizedVolumeFunctions
public import Integration7.SupportedVolumeFunctionJacobians

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! The checked positive homogeneous Jacobian theorem passes to actual
normalized function generators and finite linear combinations of them. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4
open SpecialTransformations.DefinableGeometry

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
variable (Ξ : Set (Values.Gamma (M := M))) (hΞ : Cardinal.mk Ξ < C.κ)
variable (hGenerated : VFGammaGeneratedBase (⟨(C.base : Set M),Ξ⟩ : Base (M := M)))
variable (hNames : commonRealNames (⟨(C.base : Set M),Ξ⟩ : Base (M := M)) ⊆ (C.base : Set M))
variable (γ : Values.Gamma (M := M)) (hγ : γ ∈ Ξ) (hγ1 : 1 < γ)

def normalizedPositiveVolumeFunction (n k : ℕ) (f : AERVVolumeFunction hc C n k) :
    NormalizedVolumeFunction hc C n :=
  normalizedVolumeFunctionGenerator hc C n
    (DirectSum.of (AEVolumeFunctionComponent hc C n) (k+1) f)

theorem normalized_positive_integral_eq_of_canonical {n k : ℕ}
    (f g : AERVVolumeFunction hc C n k)
    (h : aeRVVolumeFunctionIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 f =
      aeRVVolumeFunctionIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 g) :
    normalizedVolumeIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 n
      (normalizedPositiveVolumeFunction hc C n k f) =
    normalizedVolumeIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 n
      (normalizedPositiveVolumeFunction hc C n k g) := by
  have hApp : aeRVVolumeFunctionAppendedIntegralOrdinaryLinearMap hc C Ξ hΞ hGenerated hNames γ hγ hγ1 n k f =
      aeRVVolumeFunctionAppendedIntegralOrdinaryLinearMap hc C Ξ hΞ hGenerated hNames γ hγ hγ1 n k g := by
    apply (canonicalFromAppendedVolumeOrdinaryLinearEquiv hc C n k).injective
    exact (ae_rv_volume_integral_from_appended hc C Ξ hΞ hGenerated hNames γ hγ hγ1 f).trans
      (h.trans (ae_rv_volume_integral_from_appended hc C Ξ hΞ hGenerated hNames γ hγ hγ1 g).symm)
  simp only [normalizedPositiveVolumeFunction,normalized_volume_integral_generator]
  apply congrArg (normalizedVolumeCoefficientMap hc C)
  change gradedAEVolumeIntegralOrdinaryLinearMap hc C Ξ hΞ hGenerated hNames γ hγ hγ1 n
    (DirectSum.of (AEVolumeFunctionComponent hc C n) (k+1) f) =
    gradedAEVolumeIntegralOrdinaryLinearMap hc C Ξ hΞ hGenerated hNames γ hγ hγ1 n
    (DirectSum.of (AEVolumeFunctionComponent hc C n) (k+1) g)
  rw [graded_ae_volume_integral_of,graded_ae_volume_integral_of]
  apply congrArg (DirectSum.of (RVVolumeBlowupClasses hc C) (n+(k+1)+1))
  change positiveVolumeClassDegreeReindexOrdinaryLinearEquiv hc C _
    (aeRVVolumeFunctionAppendedIntegralOrdinaryLinearMap hc C Ξ hΞ hGenerated hNames γ hγ hγ1 n k f) =
    positiveVolumeClassDegreeReindexOrdinaryLinearEquiv hc C _
    (aeRVVolumeFunctionAppendedIntegralOrdinaryLinearMap hc C Ξ hΞ hGenerated hNames γ hγ hγ1 n k g)
  exact congrArg _ hApp

theorem normalized_positive_jacobian_integral {n k : ℕ}
    {X Y : DefSet (rawVFSpace (M := M) (n+1)) (C.base : Set M)}
    (φ : Map X Y) (hφ : Function.Bijective φ) (f : SupportedAERVVolumeFunction hc C X k) :
    normalizedVolumeIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 n
      (normalizedPositiveVolumeFunction hc C n k (supportedVolumeFunctionForget hc C X f)) =
    normalizedVolumeIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 n
      (normalizedPositiveVolumeFunction hc C n k
        (supportedVolumeFunctionForget hc C Y (supportedVolumeFunctionJacobian hc C φ hφ f))) :=
  normalized_positive_integral_eq_of_canonical hc C Ξ hΞ hGenerated hNames γ hγ hγ1 _ _
    (supported_volume_function_jacobian_integral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 φ hφ f)

end IntegrationInACVF.Section7
