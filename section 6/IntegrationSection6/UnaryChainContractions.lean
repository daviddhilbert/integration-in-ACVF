import IntegrationSection6.ArbitraryFiniteContractions
import IntegrationSection6.GammaFiniteMixedBijections
import IntegrationSection5.GammaUnaryChain

/-! Finite relatively unary chains preserve actual contraction classes
in all orders. Intermediate finite RV fibres are derived from the actual
Gamma bijections, rather than assumed along the chain. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5 SpecialTransformations.Section7
open IntegrationInACVF.Section5
namespace IntegrationInACVF.Section6.FiniteRV
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {n a b : ℕ}

theorem gamma_unary_chain_contractions {κ : Cardinal} (hκ : Cardinal.aleph0 < κ)
    (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (hreal : Cardinal.mk B.real < κ) (hgamma : Cardinal.mk B.gamma < κ)
    (δ : Values.Gamma (M := M)) (hδ : δ ∈ B.gamma) (hδ1 : 1 < δ) (FBase : VFFieldBase B.real)
    (h58 : Section5TwoOrderInputAll hκ.le hs)
    {U : DefSet (M := M) Set.univ (n+1) a} {V : DefSet (M := M) Set.univ (n+1) b}
    (T : UnaryChain Set.univ (n+1) U V) :
    ∀ (hT : GammaUnaryChainDefinable B T)
    (hU : GammaSetDefinable B (carrier U)) (hV : GammaSetDefinable B (carrier V))
    (hfinU : ∀ x : Fin (n+1) → VF (M := M), {r : Fin a → RV (M := M) | (x,r) ∈ carrier U}.Finite)
    (hfinV : ∀ x : Fin (n+1) → VF (M := M), {r : Fin b → RV (M := M) | (x,r) ∈ carrier V}.Finite)
    {σ υ : Equiv.Perm (Fin (n+1))} (C : StandardContraction U σ) (E : StandardContraction V υ)
    (hC : GammaProgramDefinable B C.program) (hE : GammaProgramDefinable B E.program),
    GammaIsp hκ.le hs h00 hreal (gammaFiniteContraction hκ.le hs hreal (Set.subset_univ _) hU hfinU C hC)
      (gammaFiniteContraction hκ.le hs hreal (Set.subset_univ _) hV hfinV E hE) := by
  induction T with
  | nil U =>
    intro hT hU hV hfinU hfinV σ υ C E hC hE
    exact gamma_finite_contractions_all_orders hκ hs h00 hreal hgamma δ hδ hδ1 FBase h58
      (Set.subset_univ _) U hU hfinU C E hC hE
  | @cons a c b U W V i f hf hi tail ih =>
    intro hT hU hV hfinU hfinV σ υ C E hC hE
    let fΓ : GammaIso B (carrier U) (carrier W) := ⟨Equiv.ofBijective f hf,hT.1⟩
    have hW := fΓ.target_definable (gammaLogicInput B)
    have hfinW := finite_rv_fibres_of_gamma_bijection hκ.le hs hreal f hf hT.1 hfinU
    let ρ : Equiv.Perm (Fin (n+1)) := Equiv.swap 0 i
    obtain ⟨D,hD,_,_,_⟩ := standard_contraction_exists_with_natural_graph hs h00 B hreal FBase
      (Set.subset_univ _) U hU ρ
    obtain ⟨F,hF,_,_,_⟩ := standard_contraction_exists_with_natural_graph hs h00 B hreal FBase
      (Set.subset_univ _) W hW ρ
    have H1 := gamma_finite_contractions_all_orders hκ hs h00 hreal hgamma δ hδ hδ1 FBase h58
      (Set.subset_univ _) U hU hfinU C D hC hD
    have hi' : UnaryRelative f (ρ 0) := by simpa only [ρ,Equiv.swap_apply_left] using hi
    have H2 := corollary_6_15_finite hκ hs h00 hreal hgamma δ hδ hδ1 (Set.subset_univ _)
      U W hU hW hfinU hfinW f hf hT.1 hi' D F hD hF
    have H3 := ih hT.2 hW hV hfinW hfinV F E hF hE
    exact H1.trans (H2.trans H3)

end IntegrationInACVF.Section6.FiniteRV
