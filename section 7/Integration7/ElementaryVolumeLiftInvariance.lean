module

public import Integration7.CanonicalElementaryDensityIdentifications
public import Integration7.ActualVolumeCanonicalPresentations
public import Integration7.NormalizedActualVolumeGraphs
public import Integration7.RealVolumeGammaCertificates
public import Integration7.EssentialVolumeLiftIsomorphisms
public import Integration7.ElementaryBlowupComparisonTheorem

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! Every actual elementary volume blowup has a volume-isomorphic VF
lift. The focus and its determinant-one map are constructed internally;
arbitrary densities are retained, including nonconstant ones. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4
open IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {k : ℕ}

theorem canonical_elementary_volume_lift_iso
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (Ξ : Set (Values.Gamma (M := M)))
    (hGenerated : VFGammaGeneratedBase (⟨(C.base : Set M),Ξ⟩ : Base (M := M)))
    (U : FiniteRV.GammaObjectAt (⟨(C.base : Set M),Ξ⟩ : Base (M := M)) (C.base : Set M) (k+1))
    (ω : VolumeForm (canonicalFiniteRVObject hc U.object).obj.domain)
    (hAd : GammaAdmissible U.toGamma.toGammaRVObject (Fin.last k)) :
    Nonempty (VFVolumeIso
      (rvVolumeLift (⟨canonicalFiniteRVObject hc U.object,ω⟩ : PositiveRVVolumeObject (M := M) (C.base : Set M) k))
      (rvVolumeLift (elementaryVolumeObject C
        (⟨canonicalFiniteRVObject hc U.object,ω⟩ : PositiveRVVolumeObject (M := M) (C.base : Set M) k)
        (canonicalGammaElementaryAdmissible hc C U ω hAd)))) := by
  obtain ⟨f⟩ := canonical_gamma_elementary_lift_volume_bijection hc C hGenerated U ω hAd
  obtain ⟨e⟩ := canonical_elementary_density_identification hc C U ω hAd
  obtain ⟨g⟩ := e.nonempty_full_lift_iso hc C Ξ hGenerated
  exact ⟨(VFVolumeIso.of_bijection f).trans hc C g⟩

theorem elementary_volume_lift_iso
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (Ξ : Set (Values.Gamma (M := M)))
    (hGenerated : VFGammaGeneratedBase (⟨(C.base : Set M),Ξ⟩ : Base (M := M)))
    (U : PositiveRVVolumeObject (M := M) (C.base : Set M) k) (hAd : BlowupAdmissible U) :
    Nonempty (VFVolumeIso (rvVolumeLift U) (rvVolumeLift (elementaryVolumeObject C U hAd))) := by
  let hU := volume_object_gamma_over_real_base hc C Ξ U
  let P := normalizedActualVolumeGammaObject hc U hU (Set.Subset.refl _)
  let hCenter := blowup_center_gamma_over_real_base C Ξ U hAd
  let hPA := normalized_actual_volume_gamma_admissible hc U hU (Set.Subset.refl _) hAd hCenter
  let V := canonicalActualVolumeObject hc U
  let hAdV := canonicalGammaElementaryAdmissible hc C P V.form hPA
  obtain ⟨f⟩ := canonical_elementary_volume_lift_iso hc C Ξ hGenerated P V.form hPA
  obtain ⟨e⟩ := actual_volume_canonical_presentation_iso hc C U
  obtain ⟨e'⟩ := lemma_7_2 hc C (elementaryVolumeBlowup C U hAd)
    (elementaryVolumeBlowup C V hAdV) ⟨e⟩
  obtain ⟨g⟩ := e.nonempty_full_lift_iso hc C Ξ hGenerated
  obtain ⟨g'⟩ := e'.nonempty_full_lift_iso hc C Ξ hGenerated
  exact ⟨g.trans hc C (f.trans hc C (g'.symm hc C))⟩

theorem ElementaryBlowup.nonempty_volume_lift_iso
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (Ξ : Set (Values.Gamma (M := M)))
    (hGenerated : VFGammaGeneratedBase (⟨(C.base : Set M),Ξ⟩ : Base (M := M)))
    {U W : PositiveRVVolumeObject (M := M) (C.base : Set M) k} (b : ElementaryBlowup U W) :
    Nonempty (VFVolumeIso (rvVolumeLift U) (rvVolumeLift W)) := by
  obtain ⟨f⟩ := elementary_volume_lift_iso hc C Ξ hGenerated U b.admissible
  obtain ⟨e⟩ := lemma_7_2 hc C (elementaryVolumeBlowup C U b.admissible) b ⟨RVVolumeIso.refl hc C U⟩
  obtain ⟨g⟩ := e.nonempty_full_lift_iso hc C Ξ hGenerated
  exact ⟨f.trans hc C g⟩

end IntegrationInACVF.Section7
