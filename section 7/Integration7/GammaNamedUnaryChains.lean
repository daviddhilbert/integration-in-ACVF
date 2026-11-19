import Integration7.GammaNamedCorollary76
import Integration7.UnaryChainVolumeContractions
import IntegrationSection5.GammaUnaryChain

/-! Gamma-named unary chains. A Gamma unary chain carries Gamma volume data
when every intermediate density along the chain has a Gamma density graph
over `G`. Such chains preserve Gamma-named standard contraction volume
classes. The Gamma volume data is an explicit hypothesis here; it is supplied
by the Gamma Jacobian of the factors where the chains are constructed. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section9
open SpecialTransformations.Section5 (VF RV carrier gammaLogicInput GammaSetDefinable GammaGraphDefinable
  setDefinable pointMapGraph)
open IntegrationInACVF.Section5 IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {G : Base (M := M)} {S : Set M} {n a b k : ℕ}

theorem VFVolumeObjectGamma.of_density_graph {U : PositiveVFVolumeObject (M := M) S k}
    (h : GammaSetDefinable G (volumeDensityGraph U.form).carrier) : VFVolumeObjectGamma U G := by
  refine ⟨?_,h⟩
  have hI := (gammaLogicInput G).image_graph ((gammaLogicInput G).restrict_graph h gamma_drop_last_rv_graph)
  have he : {p | ∃ q, q ∈ (volumeDensityGraph U.form).carrier ∧ p = (q.1,q.2 ∘ Fin.castAdd 1)} =
      U.domain.carrier := by
    ext p
    constructor
    · rintro ⟨q,hq,rfl⟩
      exact ((mem_volumeDensityGraph_iff U.form q).mp hq).1
    · intro hp
      refine ⟨(appendDensityMap U.form ⟨p,hp⟩).val,⟨⟨p,hp⟩,rfl⟩,?_⟩
      rw [appendDensityMap_value]
      refine Prod.ext rfl ?_
      funext i
      exact (Fin.append_left _ _ i).symm
  exact he ▸ hI

theorem vf_mixed_map_graph_raw_special (hc : CanonicalStructure.IsCanonical (M := M))
    {A : SpecialTransformations.Section5.DefSet (M := M) S n a}
    {B : SpecialTransformations.Section5.DefSet (M := M) S n b}
    (f : SpecialTransformations.Section5.Map A B) (hf : GammaGraphDefinable G (pointMapGraph f)) :
    GammaGraphDefinable G (vfMixedMapGraph (rawSpecialMap hc f)) := by
  apply SpecialTransformations.Section5.GammaGraphDefinable.congr hf
  intro p q
  constructor
  · rintro ⟨u,rfl,rfl⟩
    exact ⟨⟨u.val,u.property⟩,rfl,rfl⟩
  · rintro ⟨u,rfl,rfl⟩
    exact ⟨⟨u.val,u.property⟩,rfl,rfl⟩

/-- Unary chain volume data whose intermediate densities have Gamma density graphs. -/
def gammaUnaryChainVolumeData (hc : CanonicalStructure.IsCanonical (M := M)) (G : Base (M := M))
    {A : SpecialTransformations.Section5.DefSet (M := M) S n a}
    {B : SpecialTransformations.Section5.DefSet (M := M) S n b}
    (T : UnaryChain S n A B) :
    VolumeForm (rawSpecialSet hc A) → VolumeForm (rawSpecialSet hc B) → Prop :=
  by
    induction T with
    | nil A =>
      exact fun ω π => PreservesVFVolume ω π (rawSpecialMap hc (SpecialTransformations.Section5.Map.id A))
    | cons i f hf hi tail ih =>
      exact fun ω π => ∃ η, GammaSetDefinable G (volumeDensityGraph η).carrier ∧
        PreservesVFVolume ω η (rawSpecialMap hc f) ∧ ih η π

namespace GammaNamed

set_option maxHeartbeats 1600000 in
theorem unary_chain_volume_contractions_compare
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (G : Base (M := M)) (hGC : G.real ⊆ (C.base : Set M)) (hΞ : Cardinal.mk G.gamma < C.κ)
    (hGenerated : VFGammaGeneratedBase G) (hNames : commonRealNames G ⊆ (C.base : Set M))
    (hGeneric : ∀ {p : ℕ} (x : Fin p → VF (M := M)), AlgebraicIndependent (vfParameterField G.real) x →
      AlgebraicIndependent (vfParameterField (C.base : Set M)) x)
    (γ : Values.Gamma (M := M)) (hγ : γ ∈ G.gamma) (hγ1 : 1 < γ)
    {A : SpecialTransformations.Section5.DefSet (M := M) (C.base : Set M) (n+1) a}
    {B : SpecialTransformations.Section5.DefSet (M := M) (C.base : Set M) (n+1) b}
    (T : UnaryChain (C.base : Set M) (n+1) A B) (hT : GammaUnaryChainDefinable G T) :
    ∀ (ω : VolumeForm (rawSpecialSet hc A)) (π : VolumeForm (rawSpecialSet hc B)),
    GammaSetDefinable G (volumeDensityGraph ω).carrier →
    GammaSetDefinable G (volumeDensityGraph π).carrier →
    gammaUnaryChainVolumeData hc G T ω π →
    ∀ (hfinA : ∀ x : Fin (n+1) → VF (M := M), {r : Fin a → RV (M := M) | (x,r) ∈ carrier A}.Finite)
    (hfinB : ∀ x : Fin (n+1) → VF (M := M), {r : Fin b → RV (M := M) | (x,r) ∈ carrier B}.Finite),
    let U := nativeMixedVFVolumeObject hc A hfinA ω
    let V := nativeMixedVFVolumeObject hc B hfinB π
    ∀ (hU : VFVolumeObjectGamma U G) (hV : VFVolumeObjectGamma V G)
    {σ υ : Equiv.Perm (Fin (n+1))}
    (D : StandardContraction (nativeMixedVolumeDomain hc U.densityGraph.domain) σ)
    (E : StandardContraction (nativeMixedVolumeDomain hc V.densityGraph.domain) υ)
    (hD : GammaProgramDefinable G D.program) (hE : GammaProgramDefinable G E.program),
    CommonContextVolumeEquivalent G C
      ⟨U.standardContractionObject hc C G.gamma D,standard_contraction_object_gamma hc C G hGC U hU D hD⟩
      ⟨V.standardContractionObject hc C G.gamma E,standard_contraction_object_gamma hc C G hGC V hV E hE⟩ := by
  have hreal : Cardinal.mk G.real < C.κ := (Cardinal.mk_le_mk_of_subset hGC).trans_lt C.small
  induction T with
  | nil A =>
    intro ω π hω hπ hData hfinA hfinB U V hU hV σ υ D E hD hE
    let f : VFVolumeBijection U V := ⟨rawSpecialMap hc (SpecialTransformations.Section5.Map.id A),
      Function.bijective_id,hData⟩
    have hf : GammaGraphDefinable G (vfMixedMapGraph f.map) := by
      apply SpecialTransformations.Section5.GammaGraphDefinable.congr (gamma_vf_identity_graph (B := G) _ hT)
      intro p q
      constructor
      · rintro ⟨hp,rfl⟩
        exact ⟨⟨p,hp⟩,rfl,rfl⟩
      · rintro ⟨u,rfl,rfl⟩
        exact ⟨u.property,rfl⟩
    exact relative_volume_contractions_all_orders hc C G hGC hΞ hGenerated hNames hGeneric γ hγ hγ1
      U V hU hV f hf 0 (fun _ _ _ => rfl) D E hD hE
  | @cons a c b A W B i f hf hi tail ih =>
    intro ω π hω hπ hData hfinA hfinB U V hU hV σ υ D E hD hE
    obtain ⟨η,hη,hfVolume,hTailVolume⟩ := hData
    have hfinW := finite_rv_fibres_of_gamma_bijection (B := G) C.uncountable.le C.saturated hreal
      f hf hT.1 hfinA
    let Q := nativeMixedVFVolumeObject hc W hfinW η
    have hQ : VFVolumeObjectGamma Q G := VFVolumeObjectGamma.of_density_graph hη
    let fV : VFVolumeBijection U Q := ⟨rawSpecialMap hc f,hf,hfVolume⟩
    let W' := nativeMixedVolumeDomain hc Q.densityGraph.domain
    obtain ⟨F,hF,_,_,_⟩ := generated_base_standard_contraction_exists (B := G) C.saturated C.model00
      hreal hGenerated hGC W' hη (Equiv.refl _)
    have hLeft := relative_volume_contractions_all_orders hc C G hGC hΞ hGenerated hNames hGeneric γ hγ hγ1
      U Q hU hQ fV (vf_mixed_map_graph_raw_special hc f hT.1) i
      (fun p j hj => hi ⟨p.val,p.property⟩ j hj) D F hD hF
    have hRight := ih hT.2 η π hη hπ hTailVolume hfinW hfinB hQ hV F E hF hE
    exact hLeft.trans hc hRight

end GammaNamed
end IntegrationInACVF.Section7
