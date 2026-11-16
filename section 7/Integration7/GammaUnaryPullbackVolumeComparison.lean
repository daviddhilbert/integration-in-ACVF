module

public import Integration7.UnaryPullbackVolumeComparison
public import Integration7.GammaVolumeFullChartRestriction
public import Integration7.GammaCoordinateDensityGraphs
public import IntegrationSection6.FiniteGammaObjects
public import IntegrationSection5.UnaryRVCategory

@[expose] public section

/-! The mutually contractible unary volume comparison retains its
full original-Gamma essential graph after actual lift descent. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section5 (pullbackObject rvObjectVolume IsRVPullback carrier
  Contractible pointMapGraph GammaSetDefinable GammaGraphDefinable)

namespace IntegrationInACVF.Section7
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
local notation "N" => (@CanonicalStructure.normalize M sM)

set_option maxHeartbeats 800000 in
theorem unaryPullbackVolumeIso_gamma
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (P : GammaParameters.Base (M := M)) (hPC : P.real ⊆ (C.base : Set M))
    {a b : ℕ}
    (A : SpecialTransformations.Section5.DefSet (M := M) (C.base : Set M) 1 a)
    (B : SpecialTransformations.Section5.DefSet (M := M) (C.base : Set M) 1 b)
    (hA : IsRVPullback (carrier A)) (hB : IsRVPullback (carrier B))
    (hAF : @Map.FiniteFibres LRV M N _ _ (C.base : Set M) _ _ (rvObjectVolume (pullbackObject A)))
    (hBF : @Map.FiniteFibres LRV M N _ _ (C.base : Set M) _ _ (rvObjectVolume (pullbackObject B)))
    (δ : Fin a) (ε : Fin b)
    (hδ : ∀ p : A, (p.val.2 δ).val ≠ iRVZero)
    (hε : ∀ p : B, (p.val.2 ε).val ≠ iRVZero)
    (f : SpecialTransformations.Section5.Map A B) (hf : Function.Bijective f)
    (hcon : Contractible f)
    (hback : Contractible (SpecialTransformations.Section5.Map.inverse f hf))
    (hfΓ : GammaGraphDefinable P (pointMapGraph f))
    (hMeasure : PreservesVFVolume (rawPullbackVolumeForm hc A hA hAF δ hδ)
      (rawPullbackVolumeForm hc B hB hBF ε hε) (rawSpecialMap hc f)) (hAΓ : GammaSetDefinable P (carrier A)) :
    (unaryPullbackVolumeIso hc C P hPC A B hA hB hAF hBF δ ε hδ hε f hf hcon hback hfΓ hMeasure).GammaDefinable P := by
  let UΓ := Section6.FiniteRV.gammaPullbackAt hPC A hAΓ hAF
  have hsmall : Cardinal.mk P.real < C.κ := (Cardinal.mk_le_mk_of_subset hPC).trans_lt C.small
  let e := IntegrationInACVF.Section5.unaryRVIso C.uncountable.le C.saturated hsmall
    f hf hcon hback hA hB hfΓ
  let F := canonicalRawRVMap hc (IntegrationInACVF.Section5.unaryIsoHomMap e)
  apply gamma_volume_iso_of_full_map _ F
    (gamma_essential_volume_domain _ (canonical_gamma_object_volume_graph hc UΓ))
  · apply GammaGraphDefinable.congr
      (IntegrationInACVF.Section5.gamma_rvContractionMap_graph f hcon hfΓ)
    intro p q
    constructor
    · rintro ⟨u,hu,hq⟩
      exact ⟨⟨u.val,u.property⟩,hu,hq⟩
    · rintro ⟨u,hu,hq⟩
      exact ⟨⟨u.val,u.property⟩,hu,hq⟩
  · intro u
    rfl

end IntegrationInACVF.Section7
