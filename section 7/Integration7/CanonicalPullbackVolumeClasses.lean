module

public import Integration7.CanonicalPullbackContractionVolumes
public import Integration7.PullbackCoordinateGammaObjects

@[expose] public section

/-! A Gamma pullback has an actual canonical standard contraction
in the same volume blowup class, with arbitrary retained density. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section5
open IntegrationInACVF.Section5 IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7
variable {M : Type} [sM : LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {G : Base (M := M)} {k a : ℕ}

theorem pullback_canonical_contraction_volume_exists {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ) (hreal : Cardinal.mk G.real < κ)
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (hGC : G.real ⊆ (C.base : Set M))
    (A : DefSet (M := M) (C.base : Set M) (k+1) a)
    (hA : GammaSetDefinable G (carrier A)) (hPull : IsRVPullback (carrier A))
    (hfin : ∀ x : Fin (k+1) → VF (M := M), {r : Fin a → RV (M := M) | (x,r) ∈ carrier A}.Finite)
    (hAF : @SpecialTransformations.DefinableGeometry.Map.FiniteFibres LRV M
      (@CanonicalStructure.normalize M sM) _ _ (C.base : Set M) _ _ (rvObjectVolume (pullbackObject A)))
    (δ : Fin a) (hδ : ∀ p : A, (p.val.2 δ).val ≠ iRVZero) :
    ∃ T : StandardContraction A (Equiv.refl _), ∃ hT : GammaProgramDefinable G T.program,
    ∃ D : BaseContext M, ∃ hCD : (C.base : Set M) ⊆ (D.base : Set M),
      GammaVolumeBlowupEquivalent G (D.base : Set M) k
        ((pullbackCoordinateGammaObject hc C hGC A hA hAF δ hδ).extend hCD)
        ((retainedDensityContractionGammaObject hκ hs hreal hc C hGC A hA hfin δ hδ T hT).extend hCD) := by
  obtain ⟨T,hT,hVF,hcon⟩ := canonical_standard_contraction_exists A hA hPull
  obtain ⟨D,hCD,e,he⟩ := canonical_pullback_contraction_volume_comparison hκ hs hreal hc C hGC
    A hA hfin hAF δ hδ T hT hVF hcon
  exact ⟨T,hT,D,hCD,GammaVolumeBlowupEquivalent.of_iso D G e he⟩

end IntegrationInACVF.Section7
