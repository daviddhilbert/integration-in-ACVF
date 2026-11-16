module

public import Integration7.NonemptyVolumeCoordinateProjections
public import Integration7.PositiveCoordinateVolumeFubini

@[expose] public section

/-! The nonempty-coordinate-subset formulation of positive homogeneous
Fubini, with the specified global volume-coordinate identification. The
function is the actual almost-everywhere quotient representative. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n k : ℕ}

theorem positive_set_coordinate_volume_fubini
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (Ξ : Set (Values.Gamma (M := M))) (hΞ : Cardinal.mk Ξ < C.κ)
    (hGenerated : VFGammaGeneratedBase (⟨(C.base : Set M),Ξ⟩ : Base (M := M)))
    (hNames : commonRealNames (⟨(C.base : Set M),Ξ⟩ : Base (M := M)) ⊆ (C.base : Set M))
    (γ : Values.Gamma (M := M)) (hγ : γ ∈ Ξ) (hγ1 : 1 < γ)
    (E D : Set (Fin (n+1))) (hE : E.Nonempty) (hD : D.Nonempty)
    (f : AERVVolumeFunction hc C n k) :
    normalizedCoordinateVolumeIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 (nonemptyVolumeCoordinateProjection E hE) f =
      normalizedCoordinateVolumeIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 (nonemptyVolumeCoordinateProjection D hD) f :=
  positive_coordinate_volume_fubini hc C Ξ hΞ hGenerated hNames γ hγ hγ1 _ _ f

end IntegrationInACVF.Section7
