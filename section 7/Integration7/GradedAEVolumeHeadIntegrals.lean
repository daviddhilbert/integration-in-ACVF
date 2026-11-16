module

public import Integration7.AEVolumeHeadZeros

@[expose] public section

/-! The full finite graded head integral sums the actual homogeneous
head maps, with the coefficient degree raised by one. Zero components
vanish, so this construction is independent of a finite support bound. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open scoped DirectSum
open Classical

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
variable (Ξ : Set (Values.Gamma (M := M))) (hΞ : Cardinal.mk Ξ < C.κ)
variable (hGenerated : VFGammaGeneratedBase (⟨(C.base : Set M),Ξ⟩ : Base (M := M)))
variable (hNames : commonRealNames (⟨(C.base : Set M),Ξ⟩ : Base (M := M)) ⊆ (C.base : Set M))
variable (γ : Values.Gamma (M := M)) (hγ : γ ∈ Ξ) (hγ1 : 1 < γ)

def gradedAEVolumeHeadIntegral (n : ℕ) :
    ZeroHom (GradedAEVolumeFunction hc C (n+1)) (GradedAEVolumeFunction hc C n) :=
  DFinsupp.sumZeroHom (fun j => {
    toFun := fun f => DirectSum.of (AEVolumeFunctionComponent hc C n) (j+1)
      (aeVolumeFunctionComponentHeadIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 n j f)
    map_zero' := by rw [ae_volume_component_head_integral_zero, map_zero] })

theorem graded_ae_volume_head_integral_of (n j : ℕ) (f : AEVolumeFunctionComponent hc C (n+1) j) :
    gradedAEVolumeHeadIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 n
        (DirectSum.of (AEVolumeFunctionComponent hc C (n+1)) j f) =
      DirectSum.of (AEVolumeFunctionComponent hc C n) (j+1)
        (aeVolumeFunctionComponentHeadIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 n j f) :=
  DFinsupp.sumZeroHom_single _ j f

theorem graded_ae_volume_head_integral_sum (n : ℕ) (f : GradedAEVolumeFunction hc C (n+1)) :
    gradedAEVolumeHeadIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 n f =
      ∑ j ∈ f.support, DirectSum.of (AEVolumeFunctionComponent hc C n) (j+1)
        (aeVolumeFunctionComponentHeadIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 n j (f j)) :=
  DFinsupp.sumZeroHom_apply _ f

end IntegrationInACVF.Section7
