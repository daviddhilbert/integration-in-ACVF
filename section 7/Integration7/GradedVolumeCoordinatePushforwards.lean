module

public import Integration7.GradedVolumePermutationLinearMaps
public import Integration7.GradedPrefixIntegralLinearMaps
public import Integration7.GradedAEVolumePrefixComponents
public import Integration7.AERVVolumeCoordinatePushforwards

@[expose] public section

/-! Arbitrary nonempty coordinate projections act on the full raw graded
function module by the actual coordinate split followed by head integration.
The maps are linear over all raw coefficients. Total integration here is
in the displayed split order; no unproved order-invariance is asserted. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open IntegrationInACVF.Section6
open scoped DirectSum
namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n p : ℕ}
variable (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)

def aeVolumeFunctionComponentBaseEquiv {a b : ℕ} (h : a=b) (j : ℕ) :
    AEVolumeFunctionComponent hc C b j ≃ₗ[RVVolumeBlowupClasses hc C 0]
      AEVolumeFunctionComponent hc C a j := by
  cases h
  exact LinearEquiv.refl _ _

def gradedAEVolumeBaseEquiv {a b : ℕ} (h : a=b) :
    GradedAEVolumeFunction hc C b ≃ₗ[RVVolumeBlowupSemiring hc C] GradedAEVolumeFunction hc C a := by
  cases h
  exact LinearEquiv.refl _ _

theorem graded_ae_volume_base_equiv_of {a b : ℕ} (h : a=b) (j : ℕ)
    (f : AEVolumeFunctionComponent hc C b j) :
    gradedAEVolumeBaseEquiv hc C h (DirectSum.of (AEVolumeFunctionComponent hc C b) j f) =
      DirectSum.of (AEVolumeFunctionComponent hc C a) j (aeVolumeFunctionComponentBaseEquiv hc C h j f) := by
  cases h
  rfl

variable (Ξ : Set (Values.Gamma (M := M))) (hΞ : Cardinal.mk Ξ < C.κ)
variable (hGenerated : VFGammaGeneratedBase (⟨(C.base : Set M),Ξ⟩ : Base (M := M)))
variable (hNames : commonRealNames (⟨(C.base : Set M),Ξ⟩ : Base (M := M)) ⊆ (C.base : Set M))
variable (γ : Values.Gamma (M := M)) (hγ : γ ∈ Ξ) (hγ1 : 1 < γ)

def gradedAEVolumeCoordinatePushforward (E : VFCoordinateProjection (n+1) (p+1)) :
    GradedAEVolumeFunction hc C n →ₗ[RVVolumeBlowupSemiring hc C] GradedAEVolumeFunction hc C p :=
  (gradedAEVolumePrefixIntegralLinearMap hc C Ξ hΞ hGenerated hNames γ hγ hγ1 E.discarded p).comp
    ((gradedAEVolumePermutationLinearMap hc C (p+E.discarded) (volumeProjectionFibreOrder E)).comp
      (gradedAEVolumeBaseEquiv hc C (volume_projection_index_eq E)).toLinearMap)

theorem graded_ae_volume_coordinate_pushforward_of (E : VFCoordinateProjection (n+1) (p+1))
    (j : ℕ) (f : AEVolumeFunctionComponent hc C n j) :
    gradedAEVolumeCoordinatePushforward hc C Ξ hΞ hGenerated hNames γ hγ hγ1 E
      (DirectSum.of (AEVolumeFunctionComponent hc C n) j f) =
    DirectSum.of (AEVolumeFunctionComponent hc C p) (appendVolumeDegree E.discarded j)
      (aeVolumeFunctionComponentPrefixIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 E.discarded p j
        (aeVolumeFunctionComponentPermutationLinearMap hc C (p+E.discarded) (volumeProjectionFibreOrder E) j
          (aeVolumeFunctionComponentBaseEquiv hc C (volume_projection_index_eq E) j f))) := by
  change gradedAEVolumePrefixIntegralLinearMap hc C Ξ hΞ hGenerated hNames γ hγ hγ1 E.discarded p
    (gradedAEVolumePermutationLinearMap hc C (p+E.discarded) (volumeProjectionFibreOrder E)
      (gradedAEVolumeBaseEquiv hc C (volume_projection_index_eq E)
        (DirectSum.of (AEVolumeFunctionComponent hc C n) j f))) = _
  rw [graded_ae_volume_base_equiv_of,graded_ae_volume_permutation_of,graded_ae_volume_prefix_linear_value,
    graded_ae_volume_prefix_integral_of]

theorem graded_ae_volume_coordinate_ordered_integral (E : VFCoordinateProjection (n+1) (p+1))
    (f : GradedAEVolumeFunction hc C n) :
    gradedAEVolumeIntegralOrdinaryLinearMap hc C Ξ hΞ hGenerated hNames γ hγ hγ1 p
      (gradedAEVolumeCoordinatePushforward hc C Ξ hΞ hGenerated hNames γ hγ hγ1 E f) =
    gradedAEVolumeIntegralOrdinaryLinearMap hc C Ξ hΞ hGenerated hNames γ hγ hγ1 (p+E.discarded)
      (gradedAEVolumePermutationLinearMap hc C (p+E.discarded) (volumeProjectionFibreOrder E)
        (gradedAEVolumeBaseEquiv hc C (volume_projection_index_eq E) f)) :=
  graded_ae_volume_prefix_linear_fubini hc C Ξ hΞ hGenerated hNames γ hγ hγ1 E.discarded p _
end IntegrationInACVF.Section7
