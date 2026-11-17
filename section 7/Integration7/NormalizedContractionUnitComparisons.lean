module

public import Integration7.FullContractionNormalizationVolumes
public import Integration7.RVVolumeInverse
public import Integration7.RVVolumeComposition

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! An exact-coordinate original-Gamma comparison of an actual raw
contraction with a finite RV object promotes to its normalized volume
object at any common nonzero constant density. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section5 (GammaSetDefinable)
open IntegrationInACVF.Section5 IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {P : Base (M := M)} {k a : ℕ}

theorem normalized_contraction_finite_unit_volume_comparison
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    {A : SpecialTransformations.Section5.DefSet (M := M) (C.base : Set M) (k+1) a}
    {σ : Equiv.Perm (Fin (k+1))} (T : StandardContraction A σ)
    (hT : GammaSetDefinable P (SpecialTransformations.Section5.carrier T.target))
    (V : RVFiniteObject (M := M) (C.base : Set M) (k+1))
    (e : canonicalRVObject hc T.contractionObject ≅ V.obj)
    (hcoord : ∀ u, V.obj.value (e.hom.map u) = (canonicalRVObject hc T.contractionObject).value u)
    (heΓ : RVMapGamma e.hom.map P)
    (η : CanonicalRV.RVSort M) (hη : η.val ∈ C.base) (hη0 : η ≠ 0) :
    let hF := (finite_volume_iso e).mpr V.property
    ∃ i : RVVolumeIso ((normalizedUnitVolumeContraction hc T hF).rescale η hη hη0)
      ((⟨V,VolumeForm.one _⟩ : PositiveRVVolumeObject (M := M) (C.base : Set M) k).rescale η hη hη0),
      i.GammaDefinable P := by
  intro hF
  let U := rawUnitVolumeContraction hc T hF
  let V' : PositiveRVVolumeObject (M := M) (C.base : Set M) k := ⟨V,VolumeForm.one _⟩
  let f := RVVolumeIso.of_preserving_coordinates_full hc C (U := U) (V := V') (rvFiniteIsoOfAmbient e) hcoord (fun _ => rfl)
  have hSource := gamma_raw_contraction_domain T hT
  have hCoord : RVMapGamma U.underlying.obj.volume P :=
    gamma_real_rv_map_graph hc P _ (rvCoordinateSelectMap P.real T.volumeIndex) hSource (fun _ => rfl)
  have hEssential := gamma_essential_volume_domain U hCoord
  have hf : f.GammaDefinable P := gamma_volume_iso_of_preserving_coordinates_full hc C
    (U := U) (V := V') (rvFiniteIsoOfAmbient e) hcoord (fun _ => rfl) hEssential heΓ
  let g := fullContractionNormalizationVolumeIso hc C T hF
  have hg := full_contraction_normalization_volume_iso_gamma hc C T hF hT
  exact ⟨((g.symm hc C).trans hc C f).rescale η hη hη0,
    ((hg.symm hc C P).trans hc C P hf).rescale η hη hη0⟩

end IntegrationInACVF.Section7
