module

public import Integration7.RawSupportedVolumeRange
public import Integration7.RawPositiveGradedChangeOfVariables

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! Numbered raw function theorems on the actual supported modules.
Proposition 7.11 includes ordinary values; the positive-value version of
7.12 is explicit and does not settle the ordinary-input scope question. -/
noncomputable section
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry
namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n : ℕ}
variable (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
variable (Ξ : Set (Values.Gamma (M := M))) (hΞ : Cardinal.mk Ξ < C.κ)
variable (hGenerated : VFGammaGeneratedBase (⟨(C.base : Set M),Ξ⟩ : Base (M := M)))
variable (hNames : commonRealNames (⟨(C.base : Set M),Ξ⟩ : Base (M := M)) ⊆ (C.base : Set M))
variable (γ : Values.Gamma (M := M)) (hγ : γ ∈ Ξ) (hγ1 : 1 < γ)

theorem proposition_7_11
    (X : DefSet (rawVFSpace (M := M) (n+1)) (C.base : Set M)) (E : Set (Fin (n+1))) (hE : E.Nonempty) :
    (rawSupportedGradedVolumeIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1
      (pureVFCoordinateImage X (rawNonemptyVolumeRetainedIndex E hE))).comp
      (rawSupportedNonemptyCoordinateIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 X E hE) =
      rawSupportedGradedVolumeIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 X :=
  raw_supported_nonempty_coordinate_total_fubini hc C Ξ hΞ hGenerated hNames γ hγ hγ1 X E hE

theorem proposition_7_12_positive
    {X Y : DefSet (rawVFSpace (M := M) (n+1)) (C.base : Set M)}
    (φ : Map X Y) (hφ : Function.Bijective φ) :
    (rawSupportedPositiveGradedIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 Y).comp
      (supportedPositiveGradedJacobian hc C φ hφ) =
      rawSupportedPositiveGradedIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 X :=
  raw_positive_graded_change_of_variables hc C Ξ hΞ hGenerated hNames γ hγ hγ1 φ hφ
end IntegrationInACVF.Section7
