module

public import Integration7.HKSupportedGradedCoordinateFubini
public import Integration7.HKRawGradedChangeOfVariables
public import Integration7.NonemptyVolumeCoordinateProjections

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! Corrected raw supported Fubini and unpadded change-of-variables
identities. These are additive raw identities on every actual weighted
coefficient degree; raw full-coefficient operator linearity is separate. -/
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry
namespace IntegrationInACVF.Section7.HK
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n : ℕ}
variable (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
variable (Ξ : Set (Values.Gamma (M := M))) (hΞ : Cardinal.mk Ξ < C.κ)
variable (hGenerated : VFGammaGeneratedBase (⟨(C.base : Set M),Ξ⟩ : Base (M := M)))
variable (hNames : commonRealNames (⟨(C.base : Set M),Ξ⟩ : Base (M := M)) ⊆ (C.base : Set M))
variable (γ : Values.Gamma (M := M)) (hγ : γ ∈ Ξ) (hγ1 : 1 < γ)

theorem proposition_7_11_additive
    (X : DefSet (rawVFSpace (M := M) (n+1)) (C.base : Set M))
    (E : Set (Fin (n+1))) (hE : E.Nonempty) (f : gradedVolumeSupport hc C X) :
    gradedAEVolumeIntegralAddHom hc C Ξ hΞ hGenerated hNames γ hγ hγ1 ((Fintype.card E).pred)
      (supportedGradedCoordinateIntegralAddHom hc C Ξ hΞ hGenerated hNames γ hγ hγ1 X
        (nonemptyVolumeCoordinateProjection E hE) f).val =
      gradedAEVolumeIntegralAddHom hc C Ξ hΞ hGenerated hNames γ hγ hγ1 n f.val :=
  supported_graded_coordinate_total_fubini hc C Ξ hΞ hGenerated hNames γ hγ hγ1 X _ f

theorem proposition_7_12_additive
    {X Y : DefSet (rawVFSpace (M := M) (n+1)) (C.base : Set M)}
    (φ : Map X Y) (hφ : Function.Bijective φ) :
    (rawSupportedGradedIntegralAddHom hc C Ξ hΞ hGenerated hNames γ hγ hγ1 Y).comp
      (supportedGradedVolumeJacobianAddHom hc C φ hφ) =
      rawSupportedGradedIntegralAddHom hc C Ξ hΞ hGenerated hNames γ hγ hγ1 X :=
  raw_graded_change_of_variables hc C Ξ hΞ hGenerated hNames γ hγ hγ1 φ hφ

end IntegrationInACVF.Section7.HK
