module

public import Integration7.LabelDeterminedPullbackDescent
public import Integration7.GammaUnaryPullbackVolumeComparison

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! The full original-Gamma graph of the actual label-determined
volume descent. Its RV map is induced by the same specified VF map. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section5 (pullbackObject rvObjectVolume carrier GammaSetDefinable GammaGraphDefinable pointMapGraph)
open IntegrationInACVF.Section5

namespace IntegrationInACVF.Section7
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
local notation "N" => (@CanonicalStructure.normalize M sM)
variable {G : GammaParameters.Base (M := M)}

set_option maxHeartbeats 1800000 in
theorem pullbackVolumeIsoOfLabelDeterminedMap_gamma
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M) {k a b d : ℕ}
    (A : SpecialTransformations.Section5.DefSet (M := M) (C.base : Set M) (k+1) a)
    (B : SpecialTransformations.Section5.DefSet (M := M) (C.base : Set M) (k+1) b)
    (hA : SpecialTransformations.Section5.IsRVPullback (SpecialTransformations.Section5.carrier A))
    (hB : SpecialTransformations.Section5.IsRVPullback (SpecialTransformations.Section5.carrier B))
    (hAF : @Map.FiniteFibres LRV M N _ _ (C.base : Set M) _ _
      (SpecialTransformations.Section5.rvObjectVolume (SpecialTransformations.Section5.pullbackObject A)))
    (hBF : @Map.FiniteFibres LRV M N _ _ (C.base : Set M) _ _
      (SpecialTransformations.Section5.rvObjectVolume (SpecialTransformations.Section5.pullbackObject B)))
    (δ : Fin a) (ε : Fin b)
    (hδ : ∀ p : A, (p.val.2 δ).val ≠ iRVZero) (hε : ∀ p : B, (p.val.2 ε).val ≠ iRVZero)
    (ρ : Fin d → Fin a) (τ : Fin d → Fin b)
    (hSource : ∀ p q : A, p.val.2 ∘ ρ = q.val.2 ∘ ρ → SpecialTransformations.Section5.SameRV p.val q.val)
    (hTarget : ∀ p q : B, p.val.2 ∘ τ = q.val.2 ∘ τ → SpecialTransformations.Section5.SameRV p.val q.val)
    (hNZSource : ∀ p : A, ∀ i : Fin (k+1),
      (SpecialTransformations.Section5.rv (SpecialTransformations.Section5.vfAt p.val i)).val ≠ iRVZero)
    (hNZTarget : ∀ p : B, ∀ i : Fin (k+1),
      (SpecialTransformations.Section5.rv (SpecialTransformations.Section5.vfAt p.val i)).val ≠ iRVZero)
    (f : SpecialTransformations.Section5.Map A B) (hf : Function.Bijective f)
    (hLabels : ∀ p : A, (f p).val.2 ∘ τ = p.val.2 ∘ ρ)
    (hMeasure : PreservesVFVolume (rawPullbackVolumeForm hc A hA hAF δ hδ)
      (rawPullbackVolumeForm hc B hB hBF ε hε) (rawSpecialMap hc f))
    (hGC : G.real ⊆ (C.base : Set M))
    (hfΓ : GammaGraphDefinable G (pointMapGraph f)) (hAΓ : GammaSetDefinable G (carrier A)) :
    (pullbackVolumeIsoOfLabelDeterminedMap hc C A B hA hB hAF hBF δ ε hδ hε
      ρ τ hSource hTarget hNZSource hNZTarget f hf hLabels hMeasure).GammaDefinable G := by
  let UΓ := Section6.FiniteRV.gammaPullbackAt hGC A hAΓ hAF
  let hcon := shared_labels_contractible f ρ τ hTarget hLabels
  let g := rvContractionMap f hcon
  let F := canonicalRawRVMap hc g
  apply gamma_volume_iso_of_full_map _ F
    (gamma_essential_volume_domain _ (canonical_gamma_object_volume_graph hc UΓ))
  · apply GammaGraphDefinable.congr (gamma_rvContractionMap_graph f hcon hfΓ)
    intro p q
    constructor
    · rintro ⟨u,hu,hq⟩
      exact ⟨⟨u.val,u.property⟩,hu,hq⟩
    · rintro ⟨u,hu,hq⟩
      exact ⟨⟨u.val,u.property⟩,hu,hq⟩
  · intro u
    rfl

end IntegrationInACVF.Section7
