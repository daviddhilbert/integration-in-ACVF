import Integration7.GammaNamedDensityLifts
import Integration7.RVCoordinateDensityPresentations
import Integration7.GammaNamedKernelObjects
import Integration7.GammaVolumeIsoGraphOperations
import Integration7.GammaVolumeRestrictionIdentities
import IntegrationSection6.KeyInverseCoordinates

/-! **Gamma native presentations of coefficients.** The canonical labelled presentation of a Gamma
RV volume object, its density graph and its native coordinate-density object are Gamma, and the
identification of a coefficient with its native coordinate-density object is Gamma-definable. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
open SpecialTransformations.DefinableGeometry
open IntegrationInACVF.Section5 IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {G : Base (M := M)} {S : Set M} {k : ℕ}

theorem gamma_canonical_rv_key_map (hc : CanonicalStructure.IsCanonical (M := M))
    {U : PositiveRVVolumeObject (M := M) S k} (hU : VolumeObjectGamma U G) :
    RVMapGamma (Section6.canonicalRVKeyMap U.underlying.obj) G := by
  have hid : RVMapGamma (Map.id U.underlying.obj.domain).toUniv G :=
    (RVMapGamma.identity hc hU.domain_graph).congr (fun _ => rfl)
  exact (hU.coordinates.append hid).congr (fun _ => rfl)

theorem gamma_canonical_rv_key_image (hc : CanonicalStructure.IsCanonical (M := M))
    {U : PositiveRVVolumeObject (M := M) S k} (hU : VolumeObjectGamma U G) :
    GammaSetDefinable G {p : Point (M := M) 0 (k+1+U.underlying.obj.arity) |
      p.2 ∈ (Section6.canonicalRVKeyMap U.underlying.obj).image.carrier} := by
  have h := (gammaLogicInput G).image_graph (gamma_canonical_rv_key_map hc hU)
  convert h using 1
  ext q
  constructor
  · rintro ⟨u,hu⟩
    exact ⟨(Fin.elim0,u.val),⟨u,rfl,hu⟩⟩
  · rintro ⟨p,⟨u,_,hu⟩⟩
    exact ⟨u,hu⟩

/-- The canonical labelled presentation of a Gamma object is Gamma. -/
theorem VolumeObjectGamma.canonicalVolumeLabels (hc : CanonicalStructure.IsCanonical (M := M))
    {U : PositiveRVVolumeObject (M := M) S k} (hU : VolumeObjectGamma U G) :
    VolumeObjectGamma (canonicalVolumeLabels U) G := by
  have hI := gamma_canonical_rv_key_image hc hU
  have hInv : RVMapGamma (Section6.canonicalRVKeyIso U.underlying.obj).inv.map G :=
    gamma_real_rv_map_graph hc G _ (rvCoordinateSelectMap G.real (Fin.natAdd (k+1))) hI
      (fun a => Section6.canonicalRVKeyIso_inv_labels U.underlying.obj a)
  constructor
  · exact gamma_real_rv_map_graph hc G _ (rvCoordinateSelectMap G.real (Fin.castAdd U.underlying.obj.arity)) hI
      (fun _ => rfl)
  · exact (hInv.comp hU.density).congr (fun _ => rfl)

/-- The canonical relabelling of a Gamma object is Gamma-definable. -/
theorem canonical_volume_labels_iso_gamma (hc : CanonicalStructure.IsCanonical (M := M))
    (C : BaseContext M) {U : PositiveRVVolumeObject (M := M) (C.base : Set M) k} (hU : VolumeObjectGamma U G) :
    (canonicalVolumeLabelsIso hc C U).GammaDefinable G :=
  gamma_volume_iso_of_full_map _ (Section6.canonicalRVKeyMap U.underlying.obj).toImage
    (gamma_essential_volume_domain _ hU.coordinates)
    ((gamma_canonical_rv_key_map hc hU).congr (fun _ => rfl)) (fun _ => rfl)

/-- The native coordinate-density domain of a Gamma coefficient is Gamma. -/
theorem gamma_rv_coordinate_density_native_domain (hc : CanonicalStructure.IsCanonical (M := M))
    (C : BaseContext M) {U : PositiveRVVolumeObject (M := M) (C.base : Set M) k} (hU : VolumeObjectGamma U G) :
    GammaSetDefinable G (carrier (rvCoordinateDensityNativeDomain hc C U)) := by
  have h := (hU.densityGraph hc).canonicalVolumeLabels hc |>.domain_graph
  have he : carrier (rvCoordinateDensityNativeDomain hc C U) =
      {p : Point (M := M) 0 ((k+1)+(U.underlying.obj.arity+1)) |
        p.2 ∈ (rvCoordinateDensityPresentation C U).underlying.obj.domain.carrier} := by
    ext p
    change (p.1 ∈ Set.univ ∧ p.2 ∈ (rvCoordinateDensityPresentation C U).underlying.obj.domain.carrier) ↔ _
    simp only [Set.mem_univ,true_and]
    rfl
  rw [he]
  exact h

theorem VolumeObjectGamma.rvCoordinateDensityNative (hc : CanonicalStructure.IsCanonical (M := M))
    (C : BaseContext M) {U : PositiveRVVolumeObject (M := M) (C.base : Set M) k} (hU : VolumeObjectGamma U G) :
    VolumeObjectGamma (rvCoordinateDensityNativeObject hc C U) G :=
  GammaNamed.native_coordinate_density_volume_object_gamma hc C G _ (gamma_rv_coordinate_density_native_domain hc C hU)
    _ _ _ _

/-- A Gamma coefficient is Gamma-isomorphic to its native coordinate-density object. -/
theorem rv_coordinate_density_native_iso_gamma (hc : CanonicalStructure.IsCanonical (M := M))
    (C : BaseContext M) {U : PositiveRVVolumeObject (M := M) (C.base : Set M) k} (hU : VolumeObjectGamma U G) :
    (rvCoordinateDensityNativeIso hc C U).GammaDefinable G := by
  have h1 : (rvCoordinateDensityPresentationIso hc C U).GammaDefinable G :=
    (rv_volume_density_graph_iso_gamma hc C hU).trans hc C G
      (canonical_volume_labels_iso_gamma hc C (hU.densityGraph hc))
  have hP : VolumeObjectGamma (rvCoordinateDensityPresentation C U) G := (hU.densityGraph hc).canonicalVolumeLabels hc
  exact h1.trans hc C G (gamma_volume_iso_of_label_identity hc _ hP rfl (fun _ => rfl))

end IntegrationInACVF.Section7
