import IntegrationSection6.OrderedRelativeContractions
import IntegrationSection6.GammaPermutedUnaryMaps
import IntegrationSection6.GammaPermutedFibrePresentations
import IntegrationSection6.GammaContractionPresentationIsomorphisms
import IntegrationSection6.SmallVFFieldBases

/-! Corollary6.15 in the finite categories: a relatively unary bijection
preserves common-blowup classes of arbitrary standard contractions that
start in its active VF coordinate and follow the same remaining order. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
open IntegrationInACVF.Section5
namespace IntegrationInACVF.Section6.FiniteRV
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {S : Set M} {n a b k : ℕ}

theorem corollary_6_15_uncountable {κ : Cardinal} (hκ : Cardinal.aleph0 < κ)
    (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (hreal : Cardinal.mk B.real < κ) (hgamma : Cardinal.mk B.gamma < κ)
    (δ : Values.Gamma (M := M)) (hδ : δ ∈ B.gamma) (hδ1 : 1 < δ)
    (hBS : B.real ⊆ S)
    (U : DefSet (M := M) S (n+1) a) (V : DefSet (M := M) S (n+1) b)
    (hU : GammaSetDefinable B (carrier U)) (hV : GammaSetDefinable B (carrier V))
    (ρ : Fin k → Fin a) (τ : Fin k → Fin b)
    (hfinU : ∀ (x : Fin (n+1) → VF (M := M)) (t : Fin k → RV (M := M)),
      {r : Fin a → RV (M := M) | (x,r) ∈ carrier U ∧ r ∘ ρ = t}.Finite)
    (hfinV : ∀ (x : Fin (n+1) → VF (M := M)) (t : Fin k → RV (M := M)),
      {r : Fin b → RV (M := M) | (x,r) ∈ carrier V ∧ r ∘ τ = t}.Finite)
    {σ : Equiv.Perm (Fin (n+1))}
    (f : Map U V) (hf : Function.Bijective f) (hF : GammaGraphDefinable B (pointMapGraph f))
    (hi : UnaryRelative f (σ 0)) (hLabels : ∀ u : U, (f u).val.2 ∘ τ = u.val.2 ∘ ρ)
    (T : StandardContraction U σ) (E : StandardContraction V σ)
    (hT : GammaProgramDefinable B T.program) (hE : GammaProgramDefinable B E.program) :
    GammaIsp hκ.le hs h00 hreal (gammaFiniteSelectedContraction hκ.le hs hreal hBS hU ρ hfinU T hT)
      (gammaFiniteSelectedContraction hκ.le hs hreal hBS hV τ hfinV E hE) := by
  have hFU := vfPermutation_selected_finite U σ ρ hfinU
  have hFV := vfPermutation_selected_finite V σ τ hfinV
  obtain ⟨P⟩ := gammaSelectedRVPresentation_exists T.target (gamma_program_final_set T.program hT)
    (orderedSelectedIndex T.program ρ) (ordered_selected_fibres_finite hκ.le hs hreal T.program hT ρ hFU)
  obtain ⟨Q⟩ := gammaSelectedRVPresentation_exists E.target (gamma_program_final_set E.program hE)
    (orderedSelectedIndex E.program τ) (ordered_selected_fibres_finite hκ.le hs hreal E.program hE τ hFV)
  have h := corollary_6_15_ordered hκ hs h00 hreal hgamma δ hδ hδ1
    (vfPermutedMap f σ) (vfPermutedMap_bijective f hf σ)
    (gamma_vfPermutedMap f hU hV hF σ) (vfPermutedMap_relative f σ hi) ρ τ
    (vfPermutedMap_labels f σ ρ τ hLabels) hFU hFV
    T.program E.program hT hE P Q
  have h' := h.corollary_6_6
    (gammaIsoSymm (gammaContractionPresentationIso hκ.le hs hreal hBS hU ρ hfinU T hT P))
    (gammaIsoSymm (gammaContractionPresentationIso hκ.le hs hreal hBS hV τ hfinV E hE Q))
  have h'' := h'.castDegree (orderedVolumeDegree_eq (n+1) k)
  simpa only [gammaCastDegree_symm] using h''


theorem corollary_6_15 {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (hreal : Cardinal.mk B.real < κ) (hgamma : Cardinal.mk B.gamma < κ)
    (δ : Values.Gamma (M := M)) (hδ : δ ∈ B.gamma) (hδ1 : 1 < δ) (FBase : VFFieldBase B.real)
    (hBS : B.real ⊆ S)
    (U : DefSet (M := M) S (n+1) a) (V : DefSet (M := M) S (n+1) b)
    (hU : GammaSetDefinable B (carrier U)) (hV : GammaSetDefinable B (carrier V))
    (ρ : Fin k → Fin a) (τ : Fin k → Fin b)
    (hfinU : ∀ (x : Fin (n+1) → VF (M := M)) (t : Fin k → RV (M := M)),
      {r : Fin a → RV (M := M) | (x,r) ∈ carrier U ∧ r ∘ ρ = t}.Finite)
    (hfinV : ∀ (x : Fin (n+1) → VF (M := M)) (t : Fin k → RV (M := M)),
      {r : Fin b → RV (M := M) | (x,r) ∈ carrier V ∧ r ∘ τ = t}.Finite)
    {σ : Equiv.Perm (Fin (n+1))}
    (f : Map U V) (hf : Function.Bijective f) (hF : GammaGraphDefinable B (pointMapGraph f))
    (hi : UnaryRelative f (σ 0)) (hLabels : ∀ u : U, (f u).val.2 ∘ τ = u.val.2 ∘ ρ)
    (T : StandardContraction U σ) (E : StandardContraction V σ)
    (hT : GammaProgramDefinable B T.program) (hE : GammaProgramDefinable B E.program) :
    GammaIsp hκ hs h00 hreal (gammaFiniteSelectedContraction hκ hs hreal hBS hU ρ hfinU T hT)
      (gammaFiniteSelectedContraction hκ hs hreal hBS hV τ hfinV E hE) :=
  corollary_6_15_uncountable (aleph0_lt_of_small_vf_field_base h00 FBase hreal) hs h00
    hreal hgamma δ hδ hδ1 hBS U V hU hV ρ τ hfinU hfinV f hf hF hi hLabels T E hT hE

end IntegrationInACVF.Section6.FiniteRV
