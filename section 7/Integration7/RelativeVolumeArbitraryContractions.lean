module

public import Integration7.OriginalVolumeArbitraryContractionOrders
public import Integration7.Corollary76
public import Integration7.GeneratedBaseStandardContractions

@[expose] public section

/-! A genuine relatively unary volume bijection compares specified
contractions in any two orders. Move both orders to its active coordinate,
apply Corollary 7.6, and use the proved all-order independence. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section5 (GammaSetDefinable gammaLogicInput carrier setDefinable)
open IntegrationInACVF.Section5 IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n : ℕ}

theorem relative_volume_contractions_all_orders
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (Ξ : Set (Values.Gamma (M := M))) (hΞ : Cardinal.mk Ξ < C.κ)
    (hGenerated : VFGammaGeneratedBase (⟨(C.base : Set M),Ξ⟩ : Base (M := M)))
    (hNames : commonRealNames (⟨(C.base : Set M),Ξ⟩ : Base (M := M)) ⊆ (C.base : Set M))
    (γ : Values.Gamma (M := M)) (hγ : γ ∈ Ξ) (hγ1 : 1 < γ)
    (U V : PositiveVFVolumeObject (M := M) (C.base : Set M) n) (f : VFVolumeBijection U V)
    (i : Fin (n+1)) (hi : ∀ p : U.domain, ∀ j, j ≠ i → (f.map p).val.1 j = p.val.1 j)
    {σ υ : Equiv.Perm (Fin (n+1))}
    (T : StandardContraction (nativeMixedVolumeDomain hc U.densityGraph.domain) σ)
    (E : StandardContraction (nativeMixedVolumeDomain hc V.densityGraph.domain) υ) :
    let G : Base (M := M) := ⟨(C.base : Set M),Ξ⟩
    CommonContextVolumeEquivalent G C
      ⟨U.standardContractionObject hc C Ξ T,U.standardContractionObject_gamma hc C Ξ T⟩
      ⟨V.standardContractionObject hc C Ξ E,V.standardContractionObject_gamma hc C Ξ E⟩ := by
  intro G
  let A := nativeMixedVolumeDomain hc U.densityGraph.domain
  let B := nativeMixedVolumeDomain hc V.densityGraph.domain
  let ρ : Equiv.Perm (Fin (n+1)) := Equiv.swap 0 i
  have hA : GammaSetDefinable G (carrier A) := (gammaLogicInput G).real_set _ (setDefinable A)
  have hB : GammaSetDefinable G (carrier B) := (gammaLogicInput G).real_set _ (setDefinable B)
  obtain ⟨D,hD,_,_,_⟩ := generated_base_standard_contraction_exists (B := G) C.saturated C.model00
    C.small hGenerated (Set.Subset.refl _) A hA ρ
  obtain ⟨F,hF,_,_,_⟩ := generated_base_standard_contraction_exists (B := G) C.saturated C.model00
    C.small hGenerated (Set.Subset.refl _) B hB ρ
  have hLeft := standard_volume_contraction_order_independent hc C Ξ hΞ hGenerated hNames γ hγ hγ1 U T D
  have hRight := standard_volume_contraction_order_independent hc C Ξ hΞ hGenerated hNames γ hγ hγ1 V F E
  have hMiddle : CommonContextVolumeEquivalent G C
      ⟨U.standardContractionObject hc C Ξ D,U.standardContractionObject_gamma hc C Ξ D⟩
      ⟨V.standardContractionObject hc C Ξ F,V.standardContractionObject_gamma hc C Ξ F⟩ :=
    corollary_7_6 hc C Ξ hΞ γ hγ hγ1 U V f (by simpa only [ρ,Equiv.swap_apply_left] using hi) D F
  exact hLeft.trans hc (hMiddle.trans hc hRight)

end IntegrationInACVF.Section7
