module

public import Integration7.GammaVolumeLabelIdentities
public import Integration7.GammaVolumeFullChartRestriction
public import Integration7.GammaCoordinateDensityGraphs
public import Integration7.CanonicalVolumeFamilySteps
public import Integration7.VolumePullbackPresentations
public import IntegrationSection6.FiniteGammaLiteralCharts
public import IntegrationSection6.FiniteGammaPartitionCharts

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! The zero-cost steps in special volume chains retain their full
original-Gamma charts: literal presentations, canonical keys and identity. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section5
open IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {k : ℕ}
local notation "N" => (@CanonicalStructure.normalize M sM)
local notation "hN" => (@CanonicalStructure.normalized_model M sM hM)

theorem gamma_volume_refl (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (U : PositiveRVVolumeObject (M := M) (C.base : Set M) k)
    (hV : GammaGraphDefinable B (fun (p : Point (M := M) 0 U.underlying.obj.arity)
      (q : Point (M := M) 0 (k+1)) => U.underlying.obj.volume.graph p.2 q.2)) :
    (RVVolumeIso.refl hc C U).GammaDefinable B := by
  apply gamma_volume_iso_label_identity B _ (gamma_essential_volume_domain U hV)
  intro u
  rfl

set_option maxHeartbeats 800000 in
theorem gamma_volume_literal_presentation
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (U : FiniteRV.GammaObjectAt B (C.base : Set M) (k+1))
    (ω : VolumeForm (canonicalFiniteRVObject hc U.object).obj.domain)
    {A : SpecialTransformations.Section5.DefSet (M := M) (C.base : Set M) (k+1) (rvObjectArity U.object.obj)}
    (h : @PresentsLift M N hN (C.base : Set M) (k+1) U.object.obj (normalizedPointSet A))
    (hA : GammaSetDefinable B (carrier A))
    (δ : Fin (rvObjectArity U.object.obj)) (hDensity : ∀ u, ω.value u = u.val δ) :
    (pullbackVolumePresentationIso hc C U.object ω h δ hDensity).GammaDefinable B := by
  let T := FiniteRV.gammaPresentationAt U h hA
  let f := FiniteRV.gammaPresentationIsoAt U h hA
  let F := canonicalRawRVMap hc (FiniteRV.isoAtMap f.iso)
  apply gamma_volume_iso_of_full_map _ F
    (gamma_essential_volume_domain _ (canonical_gamma_object_volume_graph hc T))
  · apply GammaGraphDefinable.congr f.graph
    intro p q
    constructor
    · rintro ⟨u,hu,hq⟩
      exact ⟨⟨u.val,u.property⟩,hu,hq⟩
    · rintro ⟨u,hu,hq⟩
      exact ⟨⟨u.val,u.property⟩,hu,hq⟩
  · intro u
    rfl

set_option maxHeartbeats 800000 in
theorem gamma_volume_canonical_family
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (U : FiniteRV.GammaObjectAt B (C.base : Set M) (k+1))
    (ω : VolumeForm (canonicalFiniteRVObject hc U.object).obj.domain)
    {A : SpecialTransformations.Section5.DefSet (M := M) (C.base : Set M) (k+1) (rvObjectArity U.object.obj)}
    (h : @PresentsLift M N hN (C.base : Set M) (k+1) U.object.obj (normalizedPointSet A))
    (hA : GammaSetDefinable B (carrier A)) :
    (canonicalVolumeFamilyIso hc C U.object ω).GammaDefinable B := by
  let f := (FiniteRV.gammaCanonicalIsoAt U h hA).symm
  let F := canonicalRawRVMap hc (FiniteRV.isoAtMap f.iso)
  apply gamma_volume_iso_of_full_map _ F
    (gamma_essential_volume_domain _ (canonical_gamma_object_volume_graph hc U))
  · apply GammaGraphDefinable.congr f.graph
    intro p q
    constructor
    · rintro ⟨u,hu,hq⟩
      exact ⟨⟨u.val,u.property⟩,hu,hq⟩
    · rintro ⟨u,hu,hq⟩
      exact ⟨⟨u.val,u.property⟩,hu,hq⟩
  · intro u
    rfl

end IntegrationInACVF.Section7
