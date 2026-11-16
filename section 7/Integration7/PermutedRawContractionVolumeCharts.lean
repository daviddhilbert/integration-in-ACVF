module

public import Integration7.PermutedNativeContractionVolumeCharts
public import Integration7.RawStandardVolumeObjects
public import IntegrationSection6.PermutationFiniteFibres

@[expose] public section

/-! A raw finite-label contraction on a permuted source has exactly
the corresponding permutation of its original VF volume tuple. The
retained density and actual final RV labels agree literally. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section5
open SpecialTransformations.DefinableGeometry
open IntegrationInACVF.Section5 IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n a : ℕ}

def permutedRawContractionVolumeIso
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (Ξ : Set (Values.Gamma (M := M)))
    (A : DefSet (M := M) (C.base : Set M) (n+1) a)
    (hfin : ∀ x : Fin (n+1) → VF (M := M), {r : Fin a → RV (M := M) | (x,r) ∈ carrier A}.Finite)
    (δ : Fin a) (hδ : ∀ p ∈ carrier A, (p.2 δ).val ≠ iRVZero)
    {σ : Equiv.Perm (Fin (n+1))} (T : StandardContraction A σ) :
    RVVolumeIso ((rawStandardVolumeObject hc C Ξ A hfin δ hδ T).permuteVolume σ)
      (rawStandardVolumeObject hc C Ξ (vfPermutationImage A σ) (vfPermutation_finite_rv_fibres A σ hfin)
        δ (vf_permuted_retained_density_nonzero A σ δ hδ) (identityContractionOnPermutedSource T)) := by
  let U := (rawStandardVolumeObject hc C Ξ A hfin δ hδ T).permuteVolume σ
  let V := rawStandardVolumeObject hc C Ξ (vfPermutationImage A σ) (vfPermutation_finite_rv_fibres A σ hfin)
    δ (vf_permuted_retained_density_nonzero A σ δ hδ) (identityContractionOnPermutedSource T)
  let f : Map U.underlying.obj.domain V.underlying.obj.domain := Map.inclusion (fun _ h => h)
  have hf : Function.Bijective f := by
    constructor
    · intro u v h
      have hv := congrArg Subtype.val h
      exact Subtype.ext hv
    · intro v
      exact ⟨⟨v.val,v.property⟩,rfl⟩
  have hCoord : ∀ u, V.underlying.obj.value (f u) = U.underlying.obj.value u := by
    intro u
    funext i
    change u.val ((identityContractionOnPermutedSource T).volumeIndex i) = u.val (T.volumeIndex (σ i))
    rw [identity_contraction_permuted_source_volume]
  exact RVVolumeIso.of_preserving_coordinates_full hc C
    (rvFiniteIsoOfAmbient (rvIsoOfVolumePreservingBijection f hf hCoord)) hCoord (fun _ => rfl)

end IntegrationInACVF.Section7
