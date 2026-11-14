import Integration7.CanonicalGammaCoproducts
import Integration7.GammaVolumeFullChartRestriction
import Integration7.VolumePartition
import IntegrationSection6.FiniteGammaPartitionCharts

/-! The actual volume coproduct partition has its full original-Gamma
chart whenever the cut does. The density and all coordinate equations
remain those of the checked volume partition isomorphism. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section5 (Point GammaSetDefinable GammaGraphDefinable rvObjectArity rvObjectDomain)
open IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {k : ℕ}
local notation "N" => (@CanonicalStructure.normalize M sM)

set_option maxHeartbeats 800000 in
theorem gamma_volume_complement_partition
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (U : FiniteRV.GammaObjectAt B (C.base : Set M) (k+1))
    (ω : VolumeForm (canonicalFiniteRVObject hc U.object).obj.domain)
    (A : @DefSet LRV M N (@rawRVSpace M N (rvObjectArity U.object.obj)) (C.base : Set M))
    (hA : (@DefSet.carrier LRV M N _ (C.base : Set M) A) ⊆
      (@DefSet.carrier LRV M N _ (C.base : Set M) (rvObjectDomain U.object.obj)))
    (hΓ : GammaSetDefinable B {p : Point (M := M) 0 (rvObjectArity U.object.obj) |
      p.2 ∈ (@DefSet.carrier LRV M N _ (C.base : Set M) A)}) :
    (volumeComplementPartitionIso hc C
      (⟨canonicalFiniteRVObject hc U.object,ω⟩ : PositiveRVVolumeObject (M := M) (C.base : Set M) k)
      (canonicalRawRVDomain hc A) hA).GammaDefinable B := by
  let L := FiniteRV.gammaRestrictAt U A hA hΓ
  let R := FiniteRV.gammaComplementAt U A hΓ
  let e := FiniteRV.gammaPartitionIsoAt U A hA hΓ
  let F := canonicalRawRVMap hc (FiniteRV.isoAtMap e.iso)
  apply gamma_volume_iso_of_full_map _ F
    (gamma_essential_volume_domain _ (canonical_gamma_object_volume_graph hc (FiniteRV.gammaCoprodAt L R)))
  · apply GammaGraphDefinable.congr e.graph
    intro p q
    constructor
    · rintro ⟨u,hu,hq⟩
      exact ⟨⟨u.val,u.property⟩,hu,hq⟩
    · rintro ⟨u,hu,hq⟩
      exact ⟨⟨u.val,u.property⟩,hu,hq⟩
  · intro u
    rfl

end IntegrationInACVF.Section7
