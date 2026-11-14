import Integration7.GammaCoordinateDensityGraphs
import Integration7.GammaEssentialVolumeGraphs
import IntegrationSection6.FiniteGammaWeightedIsos

/-! A native original-Gamma finite isomorphism preserving the actual
volume coordinates and density gives an actual volume isomorphism with
its full original-Gamma essential chart. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4
open SpecialTransformations.Section5 (GammaGraphDefinable)
open IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {k : ℕ}

def canonicalGammaVolumeIso
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (U V : FiniteRV.GammaObjectAt B (C.base : Set M) (k+1))
    (ω : VolumeForm (canonicalFiniteRVObject hc U.object).obj.domain)
    (π : VolumeForm (canonicalFiniteRVObject hc V.object).obj.domain)
    (e : FiniteRV.GammaIsoAt U V)
    (hcoord : ∀ u, (canonicalFiniteRVObject hc V.object).obj.value
      (finiteIsoMap (canonicalFiniteRVIso hc e.iso) u) = (canonicalFiniteRVObject hc U.object).obj.value u)
    (hφ : ∀ u, π.value (finiteIsoMap (canonicalFiniteRVIso hc e.iso) u) = ω.value u) :
    RVVolumeIso
      (⟨canonicalFiniteRVObject hc U.object,ω⟩ : PositiveRVVolumeObject (M := M) (C.base : Set M) k)
      (⟨canonicalFiniteRVObject hc V.object,π⟩ : PositiveRVVolumeObject (M := M) (C.base : Set M) k) :=
  RVVolumeIso.of_preserving_coordinates_full hc C (canonicalFiniteRVIso hc e.iso) hcoord hφ

set_option maxHeartbeats 800000 in
theorem canonicalGammaVolumeIso_gamma
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (U V : FiniteRV.GammaObjectAt B (C.base : Set M) (k+1))
    (ω : VolumeForm (canonicalFiniteRVObject hc U.object).obj.domain)
    (π : VolumeForm (canonicalFiniteRVObject hc V.object).obj.domain)
    (e : FiniteRV.GammaIsoAt U V)
    (hcoord : ∀ u, (canonicalFiniteRVObject hc V.object).obj.value
      (finiteIsoMap (canonicalFiniteRVIso hc e.iso) u) = (canonicalFiniteRVObject hc U.object).obj.value u)
    (hφ : ∀ u, π.value (finiteIsoMap (canonicalFiniteRVIso hc e.iso) u) = ω.value u) :
    (canonicalGammaVolumeIso hc C U V ω π e hcoord hφ).GammaDefinable B := by
  apply gamma_volume_iso_of_preserving_coordinates_full hc C
    (U := (⟨canonicalFiniteRVObject hc U.object,ω⟩ : PositiveRVVolumeObject (M := M) (C.base : Set M) k))
    (V := (⟨canonicalFiniteRVObject hc V.object,π⟩ : PositiveRVVolumeObject (M := M) (C.base : Set M) k))
    (canonicalFiniteRVIso hc e.iso) hcoord hφ
    (gamma_essential_volume_domain _ (canonical_gamma_object_volume_graph hc U))
  apply GammaGraphDefinable.congr e.graph
  intro p q
  constructor
  · rintro ⟨u,hu,hq⟩
    exact ⟨⟨u.val,u.property⟩,hu,hq⟩
  · rintro ⟨u,hu,hq⟩
    exact ⟨⟨u.val,u.property⟩,hu,hq⟩

end IntegrationInACVF.Section7
