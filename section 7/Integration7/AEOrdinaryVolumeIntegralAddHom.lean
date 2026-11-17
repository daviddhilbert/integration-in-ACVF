module

public import Integration7.AEOrdinaryRVVolumeIntegrals
public import Integration7.AEOrdinaryVolumeFunctionAddition
public import Integration7.OrdinaryVolumeFamilyCoproductRealizations
public import Integration7.PositiveVFVolumeAdditiveStructure

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! Ordinary RV[0]-valued AE integration is additive for the actual
pointwise coproduct operation and sends the empty family to zero. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

def aeOrdinaryRVVolumeFunctionIntegralAddHom
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (Ξ : Set (Values.Gamma (M := M))) (hΞ : Cardinal.mk Ξ < C.κ)
    (hGenerated : VFGammaGeneratedBase (⟨(C.base : Set M),Ξ⟩ : Base (M := M)))
    (hNames : commonRealNames (⟨(C.base : Set M),Ξ⟩ : Base (M := M)) ⊆ (C.base : Set M))
    (γ : Values.Gamma (M := M)) (hγ : γ ∈ Ξ) (hγ1 : 1 < γ) (n : ℕ) :
    AEOrdinaryRVVolumeFunction hc C n →+ PositiveVolumeBlowupClasses hc C n where
  toFun := aeOrdinaryRVVolumeFunctionIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1
  map_zero' := by
    change positiveVolumeIntegrationEquiv hc C Ξ hΞ hGenerated hNames γ hγ hγ1
      (positiveVFVolumeIsoClass hc C (ordinaryZeroVolumeFamily C (n+1)).fullVFObject) = 0
    rw [ordinary_zero_volume_family_full_object]
    exact positive_volume_integration_zero hc C Ξ hΞ hGenerated hNames γ hγ hγ1
  map_add' f g := Quotient.inductionOn₂ f g (fun F G => by
    change positiveVolumeIntegrationEquiv hc C Ξ hΞ hGenerated hNames γ hγ hγ1
      (positiveVFVolumeIsoClass hc C (F.2.coprod G.2).fullVFObject) = _
    rw [ordinary_volume_family_coprod_full_class hc F.2 G.2]
    exact map_add (positiveVolumeIntegrationEquiv hc C Ξ hΞ hGenerated hNames γ hγ hγ1) _ _)

end IntegrationInACVF.Section7
