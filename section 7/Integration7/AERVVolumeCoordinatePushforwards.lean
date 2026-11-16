module

public import Integration7.AERVVolumePermutedFunctions
public import Integration7.AppendedVolumePrefixFubini
public import Integration7.VolumeCoordinateProjectionOrders

@[expose] public section

/-! Arbitrary nonempty coordinate projections have an actual
almost-everywhere function pushforward, obtained by the specified VF
coordinate split and successive head integration. Its total integral is
the total in that split order; comparison with the original coordinate
order requires the explicit final RV reindexing. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

def aeRVVolumeFunctionReindexBase
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M) {p q k : ℕ} (h : p=q)
    (f : AERVVolumeFunction hc C q k) : AERVVolumeFunction hc C p k := by
  cases h
  exact f

theorem ae_rv_volume_function_reindex_base_heq
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M) {p q k : ℕ} (h : p=q)
    (f : AERVVolumeFunction hc C q k) : HEq (aeRVVolumeFunctionReindexBase hc C h f) f := by
  cases h
  rfl

def aeRVVolumeCoordinatePushforward
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (Ξ : Set (Values.Gamma (M := M))) (hΞ : Cardinal.mk Ξ < C.κ)
    (hGenerated : VFGammaGeneratedBase (⟨(C.base : Set M),Ξ⟩ : Base (M := M)))
    (hNames : commonRealNames (⟨(C.base : Set M),Ξ⟩ : Base (M := M)) ⊆ (C.base : Set M))
    (γ : Values.Gamma (M := M)) (hγ : γ ∈ Ξ) (hγ1 : 1 < γ)
    {n p k : ℕ} (E : VFCoordinateProjection (n+1) (p+1))
    (f : AERVVolumeFunction hc C n k) : AERVVolumeFunction hc C p (appendVolumeDegree E.discarded k) :=
  aeRVVolumeFunctionPrefixIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 E.discarded p k
    (aeRVVolumeFunctionPermuteBase hc C (volumeProjectionFibreOrder E)
      (aeRVVolumeFunctionReindexBase hc C (volume_projection_index_eq E) f))

theorem ae_rv_volume_coordinate_pushforward_ordered_integral
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (Ξ : Set (Values.Gamma (M := M))) (hΞ : Cardinal.mk Ξ < C.κ)
    (hGenerated : VFGammaGeneratedBase (⟨(C.base : Set M),Ξ⟩ : Base (M := M)))
    (hNames : commonRealNames (⟨(C.base : Set M),Ξ⟩ : Base (M := M)) ⊆ (C.base : Set M))
    (γ : Values.Gamma (M := M)) (hγ : γ ∈ Ξ) (hγ1 : 1 < γ)
    {n p k : ℕ} (E : VFCoordinateProjection (n+1) (p+1)) (f : AERVVolumeFunction hc C n k) :
    HEq (aeRVVolumeFunctionAppendedIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1
        (aeRVVolumeCoordinatePushforward hc C Ξ hΞ hGenerated hNames γ hγ hγ1 E f))
      (aeRVVolumeFunctionAppendedIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1
        (aeRVVolumeFunctionPermuteBase hc C (volumeProjectionFibreOrder E)
          (aeRVVolumeFunctionReindexBase hc C (volume_projection_index_eq E) f))) :=
  ae_rv_volume_function_appended_prefix_fubini hc C Ξ hΞ hGenerated hNames γ hγ hγ1 E.discarded p k _

end IntegrationInACVF.Section7
