module

public import Integration7.IntegrationStandardContractionFormula
public import Integration7.RawStandardVolumeNormalization

@[expose] public section

/-! A retained literal density may be integrated by an actual native
standard contraction without first replacing it by a second density graph. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section9
open SpecialTransformations.Section5
open IntegrationInACVF.Section5

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n a : ℕ}

theorem positive_volume_integration_coordinate_density
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (Ξ : Set (Values.Gamma (M := M))) (hΞ : Cardinal.mk Ξ < C.κ)
    (hGenerated : VFGammaGeneratedBase (⟨(C.base : Set M),Ξ⟩ : Base (M := M)))
    (hNames : commonRealNames (⟨(C.base : Set M),Ξ⟩ : Base (M := M)) ⊆ (C.base : Set M))
    (γ : Values.Gamma (M := M)) (hγ : γ ∈ Ξ) (hγ1 : 1 < γ)
    (A : DefSet (M := M) (C.base : Set M) (n+1) a)
    (hfin : ∀ x : Fin (n+1) → VF (M := M), {r : Fin a → RV (M := M) | (x,r) ∈ carrier A}.Finite)
    (ω : VolumeForm (rawSpecialSet hc A)) (δ : Fin a) (hω : ∀ p, ω.value p = p.val.2 δ)
    {σ : Equiv.Perm (Fin (n+1))} (T : StandardContraction A σ) :
    let U := nativeMixedVFVolumeObject hc A hfin ω
    let hδ : ∀ p ∈ carrier A, (p.2 δ).val ≠ iRVZero := fun p hp =>
      (rv_nonzero_iff_raw _).mp (fun hz => ω.nonzero ⟨p,hp⟩ ((hω ⟨p,hp⟩).trans hz))
    positiveVolumeIntegrationEquiv hc C Ξ hΞ hGenerated hNames γ hγ hγ1 (positiveVFVolumeIsoClass hc C U) =
      positiveVolumeBlowupClass hc C (rawStandardVolumeObject hc C Ξ A hfin δ hδ T) := by
  intro U hδ
  let G : Base (M := M) := ⟨(C.base : Set M),Ξ⟩
  let B := nativeMixedVolumeDomain hc U.densityGraph.domain
  have hB : GammaSetDefinable G (carrier B) := (gammaLogicInput G).real_set _ (setDefinable B)
  obtain ⟨E,hE,_,_,_⟩ := generated_base_standard_contraction_exists (B := G)
    C.saturated C.model00 C.small hGenerated (Set.Subset.refl _) B hB σ
  have hIntegral := positive_volume_integration_standard_contraction hc C Ξ hΞ hGenerated hNames γ hγ hγ1 U E
  have hRaw := raw_standard_volume_normalization hc C Ξ A hfin δ hδ T
  have hGraph := retained_density_graph_contraction_comparison hc C Ξ hΞ γ hγ hγ1 A hfin ω δ hω T E
  have hOriginal := ((hRaw.trans hc hGraph).descend hc C hNames).toOrdinary hc C G
  exact hIntegral.trans ((positiveVolumeBlowupClass_eq_iff hc C).mpr hOriginal).symm

end IntegrationInACVF.Section7
