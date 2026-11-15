import Integration7.RelativeVolumeArbitraryContractions
import Integration7.NativeRVGraphVolumeRefinements
import Integration7.UnaryChainVolumeDensities
import IntegrationSection6.GammaFiniteMixedBijections

/-! Actual unary factor chains preserve standard contraction volume
classes. Every intermediate density and finite-label proof is constructed
from the supplied chain and its genuine volume-preservation data. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section9
open SpecialTransformations.Section5 (VF RV carrier gammaLogicInput GammaSetDefinable setDefinable)
open IntegrationInACVF.Section5 IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n a b : ℕ}

set_option maxHeartbeats 1600000 in
theorem unary_chain_volume_contractions_compare
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (Ξ : Set (Values.Gamma (M := M))) (hΞ : Cardinal.mk Ξ < C.κ)
    (hGenerated : VFGammaGeneratedBase (⟨(C.base : Set M),Ξ⟩ : Base (M := M)))
    (hNames : commonRealNames (⟨(C.base : Set M),Ξ⟩ : Base (M := M)) ⊆ (C.base : Set M))
    (γ : Values.Gamma (M := M)) (hγ : γ ∈ Ξ) (hγ1 : 1 < γ)
    {A : SpecialTransformations.Section5.DefSet (M := M) (C.base : Set M) (n+1) a}
    {B : SpecialTransformations.Section5.DefSet (M := M) (C.base : Set M) (n+1) b}
    (T : UnaryChain (C.base : Set M) (n+1) A B) :
    ∀ (ω : VolumeForm (rawSpecialSet hc A)) (π : VolumeForm (rawSpecialSet hc B)),
    unaryChainVolumeData hc T ω π →
    ∀ (hfinA : ∀ x : Fin (n+1) → VF (M := M), {r : Fin a → RV (M := M) | (x,r) ∈ carrier A}.Finite)
    (hfinB : ∀ x : Fin (n+1) → VF (M := M), {r : Fin b → RV (M := M) | (x,r) ∈ carrier B}.Finite),
    let U := nativeMixedVFVolumeObject hc A hfinA ω
    let V := nativeMixedVFVolumeObject hc B hfinB π
    ∀ {σ υ : Equiv.Perm (Fin (n+1))}
    (D : StandardContraction (nativeMixedVolumeDomain hc U.densityGraph.domain) σ)
    (E : StandardContraction (nativeMixedVolumeDomain hc V.densityGraph.domain) υ),
    CommonContextVolumeEquivalent (⟨(C.base : Set M),Ξ⟩ : Base (M := M)) C
      ⟨U.standardContractionObject hc C Ξ D,U.standardContractionObject_gamma hc C Ξ D⟩
      ⟨V.standardContractionObject hc C Ξ E,V.standardContractionObject_gamma hc C Ξ E⟩ := by
  let G : Base (M := M) := ⟨(C.base : Set M),Ξ⟩
  induction T with
  | nil A =>
    intro ω π hData hfinA hfinB U V σ υ D E
    let f : VFVolumeBijection U V := ⟨rawSpecialMap hc (SpecialTransformations.Section5.Map.id A),
      Function.bijective_id,hData⟩
    exact relative_volume_contractions_all_orders hc C Ξ hΞ hGenerated hNames γ hγ hγ1 U V f 0
      (fun _ _ _ => rfl) D E
  | @cons a c b A W B i f hf hi tail ih =>
    intro ω π hData hfinA hfinB U V σ υ D E
    obtain ⟨η,hfVolume,hTailVolume⟩ := hData
    have hfinW := finite_rv_fibres_of_gamma_bijection (B := G) C.uncountable.le C.saturated C.small
      f hf ((gammaLogicInput G).real_map_graph f) hfinA
    let Q := nativeMixedVFVolumeObject hc W hfinW η
    let fV : VFVolumeBijection U Q := ⟨rawSpecialMap hc f,hf,hfVolume⟩
    let W' := nativeMixedVolumeDomain hc Q.densityGraph.domain
    have hW' : GammaSetDefinable G (carrier W') := (gammaLogicInput G).real_set _ (setDefinable W')
    obtain ⟨F,hF,_,_,_⟩ := generated_base_standard_contraction_exists (B := G) C.saturated C.model00
      C.small hGenerated (Set.Subset.refl _) W' hW' (Equiv.refl _)
    have hLeft := relative_volume_contractions_all_orders hc C Ξ hΞ hGenerated hNames γ hγ hγ1 U Q fV i
      (fun p j hj => hi ⟨p.val,p.property⟩ j hj) D F
    have hRight := ih η π hTailVolume hfinW hfinB F E
    exact hLeft.trans hc hRight

end IntegrationInACVF.Section7
