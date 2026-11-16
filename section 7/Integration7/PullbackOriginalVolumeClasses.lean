module

public import Integration7.RetainedDensityGraphContractionComparisons
public import Integration7.CanonicalPullbackVolumeClasses
public import Integration7.OriginalVolumeArbitraryContractionOrders
public import Integration7.GeneratedBaseStandardContractions

@[expose] public section

/-! The coordinate-density RV object of an actual pullback agrees with
every standard contraction of its original VF volume object. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section9 SpecialTransformations.Section5
open IntegrationInACVF.Section5 IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7
variable {M : Type} [sM : LRV.Structure M] [M ⊨ Axioms.ACVF] {n a : ℕ}

theorem pullback_original_volume_contraction_comparison
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (Ξ : Set (Values.Gamma (M := M))) (hΞ : Cardinal.mk Ξ < C.κ)
    (hGenerated : VFGammaGeneratedBase (⟨(C.base : Set M),Ξ⟩ : Base (M := M)))
    (hNames : commonRealNames (⟨(C.base : Set M),Ξ⟩ : Base (M := M)) ⊆ (C.base : Set M))
    (γ : Values.Gamma (M := M)) (hγ : γ ∈ Ξ) (hγ1 : 1 < γ)
    (A : DefSet (M := M) (C.base : Set M) (n+1) a) (hPull : IsRVPullback (carrier A))
    (hfin : ∀ x : Fin (n+1) → VF (M := M), {r : Fin a → RV (M := M) | (x,r) ∈ carrier A}.Finite)
    (hAF : @SpecialTransformations.DefinableGeometry.Map.FiniteFibres LRV M
      (@CanonicalStructure.normalize M sM) _ _ (C.base : Set M) _ _ (rvObjectVolume (pullbackObject A)))
    (ω : VolumeForm (rawSpecialSet hc A)) (δ : Fin a) (hω : ∀ p, ω.value p = p.val.2 δ) :
    let G : Base (M := M) := ⟨(C.base : Set M),Ξ⟩
    let U := nativeMixedVFVolumeObject hc A hfin ω
    let hδ : ∀ p : A, (p.val.2 δ).val ≠ iRVZero := fun p =>
      (rv_nonzero_iff_raw _).mp (fun hz => ω.nonzero ⟨p.val,p.property⟩ ((hω ⟨p.val,p.property⟩).trans hz))
    ∀ {υ : Equiv.Perm (Fin (n+1))}
    (E : StandardContraction (nativeMixedVolumeDomain hc U.densityGraph.domain) υ),
    CommonContextVolumeEquivalent G C
      (pullbackCoordinateGammaObject hc C (Set.Subset.refl _) A
        ((gammaLogicInput G).real_set _ (setDefinable A)) hAF δ hδ)
      ⟨U.standardContractionObject hc C Ξ E,U.standardContractionObject_gamma hc C Ξ E⟩ := by
  intro G U hδ υ E
  have hA : GammaSetDefinable G (carrier A) := (gammaLogicInput G).real_set _ (setDefinable A)
  obtain ⟨T,hT,D,hCD,hCanon⟩ := pullback_canonical_contraction_volume_exists (G := G)
    C.uncountable.le C.saturated C.small hc C (Set.Subset.refl _) A hA hPull hfin hAF δ hδ
  let B := nativeMixedVolumeDomain hc U.densityGraph.domain
  have hB : GammaSetDefinable G (carrier B) := (gammaLogicInput G).real_set _ (setDefinable B)
  obtain ⟨F,hF,_,_,_⟩ := generated_base_standard_contraction_exists (B := G) C.saturated C.model00
    C.small hGenerated (Set.Subset.refl _) B hB (Equiv.refl _)
  have hCanonical : CommonContextVolumeEquivalent G C
      (pullbackCoordinateGammaObject hc C (Set.Subset.refl _) A hA hAF δ hδ)
      (retainedDensityContractionGammaObject C.uncountable.le C.saturated C.small hc C
        (Set.Subset.refl _) A hA hfin δ hδ T hT) := ⟨D,hCD,hCanon⟩
  have hGraph := retained_density_graph_contraction_comparison hc C Ξ hΞ γ hγ hγ1 A hfin ω δ hω T F
  have hOrders := standard_volume_contraction_order_independent hc C Ξ hΞ hGenerated hNames γ hγ hγ1 U F E
  exact hCanonical.trans hc (hGraph.trans hc hOrders)

end IntegrationInACVF.Section7
