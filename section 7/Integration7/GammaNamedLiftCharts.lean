import Integration7.GammaNamedPullbackKernel
import Integration7.CoordinateRVVolumeLiftKernel
import IntegrationSection6.GammaElementaryFocus
import IntegrationSection6.PresentationCoordinates

/-! Gamma certificates for the actual lift presentation of a Gamma RV volume
object: the presentation is Gamma-definable, the literal lift chart has an
identity Gamma graph, and the pullback presentation isomorphism (a coordinate
projection) has a Gamma graph. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section5 (Point carrier GammaSetDefinable GammaGraphDefinable gammaLogicInput
  pullbackObject rvObjectDomain rvObjectVolume GammaRVObject pullbackObject_finiteVolume)
open IntegrationInACVF.Section5 IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7
variable {M : Type} [sM : LRV.Structure M] [M ⊨ Axioms.ACVF] {G : Base (M := M)} {k : ℕ}

/-- The Section 5 Gamma RV object underlying a Gamma volume object. -/
def gammaRVObjectOfVolume (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (hGC : G.real ⊆ (C.base : Set M)) (U : PositiveRVVolumeObject (M := M) (C.base : Set M) k)
    (hU : VolumeObjectGamma U G) : GammaRVObject G (k+1) where
  codes := C.base
  real_contains := hGC
  object := normalizedActualRVObject hc U.underlying.obj
  domain_graph := hU.domain_graph
  volume_graph := hU.coordinates

theorem gamma_actual_lift_presentation (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (hGC : G.real ⊆ (C.base : Set M)) (U : PositiveRVVolumeObject (M := M) (C.base : Set M) k)
    (hU : VolumeObjectGamma U G) :
    GammaSetDefinable G (carrier (actualRVVolumeLiftPresentation hc U.underlying.obj)) :=
  gamma_typedLift_definable (gammaRVObjectOfVolume hc C hGC U hU)

theorem gamma_rv_lift_carrier (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (hGC : G.real ⊆ (C.base : Set M)) (U : PositiveRVVolumeObject (M := M) (C.base : Set M) k)
    (hU : VolumeObjectGamma U G) :
    GammaSetDefinable G (rvLift U.underlying.obj).carrier := by
  have h := gamma_actual_lift_presentation hc C hGC U hU
  rw [show carrier (actualRVVolumeLiftPresentation hc U.underlying.obj) = (rvLift U.underlying.obj).carrier from
    literalLift_carrier_eq hc U.underlying.obj _ (actual_rv_volume_lift_presents hc U.underlying.obj)] at h
  exact h

theorem actual_rv_volume_lift_chart_gamma (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (hGC : G.real ⊆ (C.base : Set M)) (U : PositiveRVVolumeObject (M := M) (C.base : Set M) k)
    (hU : VolumeObjectGamma U G) :
    (VFVolumeIso.of_bijection (actualRVVolumeLiftChart hc C U)).GammaDefinable G := by
  have hA := gamma_actual_lift_presentation hc C hGC U hU
  refine ⟨hA,gamma_rv_lift_carrier hc C hGC U hU,?_⟩
  apply SpecialTransformations.Section5.GammaGraphDefinable.congr (gamma_vf_identity_graph (B := G) _ hA)
  intro p q
  constructor
  · rintro ⟨hp,rfl⟩
    exact ⟨⟨p,hp⟩,rfl,rfl⟩
  · rintro ⟨u,rfl,rfl⟩
    exact ⟨u.property,rfl⟩

theorem eqToIso_rv_map_val {S : Set M} {n : ℕ} {U V : RVObject (M := M) S n} (h : U = V)
    (u : U.domain) : HEq ((eqToIso h).hom.map u).val u.val := by
  subst h
  rfl

theorem actual_rv_volume_pullback_iso_gamma (hc : CanonicalStructure.IsCanonical (M := M))
    (C : BaseContext M) (hGC : G.real ⊆ (C.base : Set M))
    (U : PositiveRVVolumeObject (M := M) (C.base : Set M) k) (hU : VolumeObjectGamma U G)
    (δ : Fin U.underlying.obj.arity) (hUδ : ∀ u, U.form.value u = u.val δ)
    (hδ : ∀ p : actualRVVolumeLiftPresentation hc U.underlying.obj, (p.val.2 δ).val ≠ iRVZero) :
    (actualRVVolumePullbackIso hc C U δ hUδ hδ).GammaDefinable G := by
  let A := actualRVVolumeLiftPresentation hc U.underlying.obj
  let hfin := pullbackObject_finiteVolume A (typedLift_pullback _) (actual_rv_volume_lift_finite_labels hc U)
  let P := pullbackCoordinateGammaObject hc C hGC A (gamma_actual_lift_presentation hc C hGC U hU) hfin δ hδ
  have hP : VolumeObjectGamma P.val G := P.property
  have h := normalizedTypedLift_presents (normalizedActualRVObject hc U.underlying.obj)
  have heU : canonicalRVObject hc (normalizedActualRVObject hc U.underlying.obj) = U.underlying.obj :=
    canonical_normalized_actual_rv_object hc U.underlying.obj
  let eA : (canonicalFiniteRVObject hc ⟨pullbackObject A,hfin⟩) ≅ U.underlying :=
    rvFiniteIsoOfAmbient ((canonicalRVIso hc (pullbackPresentationIso h)).trans (eqToIso heU))
  let e := actualRVVolumePullbackIso hc C U δ hUδ hδ
  have hval : ∀ u : P.val.underlying.obj.domain,
      (finiteIsoMap eA u).val = (rvCoordinateSelectMap G.real (Fin.natAdd (k+1)) ⟨u.val,Set.mem_univ _⟩).val := by
    intro u
    exact (eq_of_heq (eqToIso_rv_map_val heU _)).trans (pullbackPresentationIso_labels h ⟨u.val,u.property⟩)
  have hF : RVMapGamma (finiteIsoMap eA) G :=
    gamma_real_rv_map_graph hc G _ (rvCoordinateSelectMap G.real (Fin.natAdd (k+1))) hP.domain_graph hval
  exact gamma_volume_iso_of_full_map e (finiteIsoMap eA) (gamma_essential_volume_domain _ hP.coordinates)
    hF (fun _ => rfl)

end IntegrationInACVF.Section7
