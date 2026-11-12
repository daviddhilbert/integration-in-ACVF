import IntegrationSection6.GammaRelativeHeadComparison
import IntegrationSection6.OrderedFibrewiseContractions

/-! Corollary6.15 for actual ordered programs starting in the active head
coordinate. The first comparison is unary; Lemma6.14 handles every remaining
VF coordinate with the head RV label retained in the selected volume. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
open IntegrationInACVF.Section5
namespace IntegrationInACVF.Section6.FiniteRV
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {S : Set M} {n a b l r k : ℕ}
variable {U : DefSet (M := M) S (n+1) a} {V : DefSet (M := M) S (n+1) b}

theorem corollary_6_15_ordered {κ : Cardinal} (hκ : Cardinal.aleph0 < κ)
    (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (hreal : Cardinal.mk B.real < κ) (hgamma : Cardinal.mk B.gamma < κ)
    (δ : Values.Gamma (M := M)) (hδ : δ ∈ B.gamma) (hδ1 : 1 < δ)
    (f : Map U V) (hf : Function.Bijective f) (hΓ : GammaGraphDefinable B (pointMapGraph f))
    (hi : UnaryRelative f 0) (ρ : Fin k → Fin a) (τ : Fin k → Fin b)
    (hLabels : ∀ u : U, (f u).val.2 ∘ τ = u.val.2 ∘ ρ)
    (hfinU : ∀ (x : Fin (n+1) → VF (M := M)) (t : Fin k → RV (M := M)),
      {v : Fin a → RV (M := M) | (x,v) ∈ carrier U ∧ v ∘ ρ = t}.Finite)
    (hfinV : ∀ (x : Fin (n+1) → VF (M := M)) (t : Fin k → RV (M := M)),
      {v : Fin b → RV (M := M) | (x,v) ∈ carrier V ∧ v ∘ τ = t}.Finite)
    {U0 : DefSet (M := M) S 0 l} {V0 : DefSet (M := M) S 0 r}
    (T : OrderedContractionProgram S U U0) (E : OrderedContractionProgram S V V0)
    (hT : GammaProgramDefinable B T) (hE : GammaProgramDefinable B E)
    (P : GammaSelectedRVPresentation B U0 (orderedSelectedIndex T ρ))
    (Q : GammaSelectedRVPresentation B V0 (orderedSelectedIndex E τ)) :
    GammaIsp hκ.le hs h00 hreal P.toGamma Q.toGamma := by
  cases T with
  | step T tail =>
    cases E with
    | step E etail =>
      exact lemma_6_14_ordered hκ hs h00 hreal hgamma δ hδ hδ1
        T.contractedSet E.contractedSet
        (gamma_headImage T.target hT.2.1) (gamma_headImage E.target hE.2.1)
        (headVolumeIndex T ρ) (headVolumeIndex E τ)
        (head_selected_fibres_finite hκ.le hs hreal T hT.1 hT.2.1 ρ hfinU)
        (head_selected_fibres_finite hκ.le hs hreal E hE.1 hE.2.1 τ hfinV)
        (fun x LP LQ => gamma_relative_head_comparison hκ hs h00 hreal hgamma δ hδ hδ1
          f hf hΓ hi ρ τ hLabels T E hT.1 hE.1 hT.2.1 hE.2.1 x LP LQ)
        tail etail hT.2.2 hE.2.2 P Q

end IntegrationInACVF.Section6.FiniteRV
