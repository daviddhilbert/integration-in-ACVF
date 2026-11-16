import Integration7.OrdinaryIndexedUnitVolumeObjects
import Integration7.GammaVolumeSliceAssemblyGeometry
import Integration7.GammaEssentialIndexDomains

/-! Discarding zero base-volume indices retains an arbitrary nonzero
coordinate density and the full original-Gamma isomorphism graph. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.Section5
open SpecialTransformations.DefinableGeometry
open IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7.HK
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {p a : ℕ}
variable {T E : Set (Fin p → RV (M := M))}
variable {R S : (Fin p → RV (M := M)) → (Fin 1 → RV (M := M)) → Prop}

set_option maxHeartbeats 1600000 in
theorem weighted_indexed_essential_restriction_iso
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (F : GammaFiniteRVSchema B p a 0 (fun _ => .rv))
    (BP : GammaFiniteGraphPresentation B p 1 T R) (BQ : GammaFiniteGraphPresentation B p 1 E S)
    (hET : E ⊆ T) (hVolume : ∀ t ∈ E, BQ.totalVolume t = BP.totalVolume t)
    (hContains : ∀ t ∈ T, (∀ i, (BP.totalVolume t i).val ≠ iRVZero) → t ∈ E)
    (P : F.IndexedPresentation BP) (Q : F.IndexedPresentation BQ)
    (hPC : P.codes ⊆ (C.base : Set M)) (hQC : Q.codes ⊆ (C.base : Set M))
    (δ : Fin a)
    (hδP : ∀ u : P.domain, (u.val (Fin.natAdd p δ)).val ≠ iRVZero)
    (hδQ : ∀ u : Q.domain, (u.val (Fin.natAdd p δ)).val ≠ iRVZero) :
    ∃ e : RVVolumeIso (gammaCoordinateDensityObject (e := 0) (k := 0) hc C Q.toGamma hQC (Fin.natAdd p δ) hδQ)
      (gammaCoordinateDensityObject (e := 0) (k := 0) hc C P.toGamma hPC (Fin.natAdd p δ) hδP), e.GammaDefinable B := by
  let U := gammaCoordinateDensityObject (e := 0) (k := 0) hc C P.toGamma hPC (Fin.natAdd p δ) hδP
  let V := gammaCoordinateDensityObject (e := 0) (k := 0) hc C Q.toGamma hQC (Fin.natAdd p δ) hδQ
  let A := V.underlying.obj.domain
  have hAU : A.carrier ⊆ U.underlying.obj.domain.carrier := by
    intro w hw
    have h := (ordinary_indexed_unit_domain hc C BQ F Q hQC w).mp hw
    exact (ordinary_indexed_unit_domain hc C BP F P hPC w).mpr ⟨hET h.1,h.2⟩
  have hEss : U.essential.obj.domain.carrier ⊆ A.carrier := by
    intro w hw
    let u : U.essential.obj.domain := ⟨w,hw⟩
    have hIndex := ordinary_indexed_unit_essential_index hc C BP F P hPC u
    have h := (ordinary_indexed_unit_domain hc C BP F P hPC w).mp
      ((rvEssentialLabels_subset U.underlying.obj) hw)
    exact (ordinary_indexed_unit_domain hc C BQ F Q hQC w).mpr
      ⟨hContains _ h.1 hIndex.2,h.2⟩
  let W := U.restrict A hAU
  let f : Map V.underlying.obj.domain W.underlying.obj.domain := Map.id _
  have hf : Function.Bijective f := Function.bijective_id
  have hCoord : ∀ u, W.underlying.obj.value (f u) = V.underlying.obj.value u := by
    intro u
    funext i
    apply Subtype.ext
    have hP := ordinary_indexed_unit_coordinate hc C BP F P hPC ⟨u.val,hAU u.property⟩ i
    have hQ := ordinary_indexed_unit_coordinate hc C BQ F Q hQC u i
    have hIndex := (ordinary_indexed_unit_domain hc C BQ F Q hQC u.val).mp u.property
    exact hP.trans ((congrArg (fun t : Fin 1 → RV (M := M) => (t i).val)
      (hVolume (indexedLeft u.val) hIndex.1)).symm.trans hQ.symm)
  let g : RVVolumeIso V W := RVVolumeIso.of_preserving_coordinates_full hc C
    (rvFiniteIsoOfAmbient (rvIsoOfVolumePreservingBijection f hf hCoord)) hCoord (fun _ => rfl)
  have hg : g.GammaDefinable B := gamma_volume_iso_of_label_identity hc g
    (gamma_coordinate_density_object_graphs (e := 0) (k := 0) hc C Q.toGamma hQC (Fin.natAdd p δ) hδQ) rfl (fun _ => rfl)
  let e := volumeIsoOfContainingEssentialRestriction hc C U A hAU hEss
  have he : e.GammaDefinable B := gamma_volume_containing_essential_restriction_iso hc C U
    (gamma_coordinate_density_object_graphs (e := 0) (k := 0) hc C P.toGamma hPC (Fin.natAdd p δ) hδP) A hAU hEss
    (gamma_coordinate_density_object_graphs (e := 0) (k := 0) hc C Q.toGamma hQC (Fin.natAdd p δ) hδQ).domain_graph
  exact ⟨g.trans hc C e,hg.trans hc C B he⟩

end IntegrationInACVF.Section7.HK
