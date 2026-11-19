import Integration7.GammaNamedPositiveClassification
import Integration7.RVVolumeLiftIsomorphism
import Integration7.EssentialVolumeLiftIsomorphisms
import Integration7.VolumeLiftBijections
import Integration7.GammaRVScalarMapGraphs
import Integration7.EssentialFiniteVolumeSchemata
import IntegrationSection6.GammaRawRVFormulas
import Section9.GammaPrescribedVolumeLift

/-! Gamma RV volume isomorphisms have Gamma VF lifts. For Gamma volume
objects coded over a base context `C` containing the real part of a
VF-Gamma-generated base `G`, a Gamma RV volume isomorphism lifts to an
almost-everywhere VF volume isomorphism with a Gamma graph over `G`. The
lift comes from the provider's Gamma Theorem 9.16
(`GammaLift.gamma_theorem_9_16_finite_volume`). -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section5 (Point GammaSetDefinable GammaGraphDefinable gammaLogicInput)
open IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {G : Base (M := M)} {S : Set M} {k : ℕ}

theorem RVMapGamma.restrict_domain {a b : ℕ}
    {A : DefSet (rawRVSpace (M := M) a) S} {D : DefSet (rawRVSpace (M := M) b) S}
    {f : Map A D} (hf : RVMapGamma f G) {A' : DefSet (rawRVSpace (M := M) a) S}
    (h : A'.carrier ⊆ A.carrier) (hA' : GammaSetDefinable G {p : Point (M := M) 0 a | p.2 ∈ A'.carrier}) :
    RVMapGamma (f.restrict h) G := by
  apply SpecialTransformations.Section5.GammaGraphDefinable.congr ((gammaLogicInput G).restrict_graph hA' hf)
  intro p q
  constructor
  · rintro ⟨hp, u, hu, hq⟩
    exact ⟨⟨p.2, hp⟩, rfl, by rw [← hq]; exact congrArg (fun x => (f x).val) (Subtype.ext hu.symm)⟩
  · rintro ⟨u, hu, hq⟩
    refine ⟨?_, ⟨u.val, h u.property⟩, hu, hq⟩
    change p.2 ∈ A'.carrier
    rw [← hu]
    exact u.property

theorem essential_domain_gamma {U : PositiveRVVolumeObject (M := M) S k}
    (hU : RVMapGamma U.underlying.obj.volume G) :
    GammaSetDefinable G {p : Point (M := M) 0 U.underlying.obj.arity | p.2 ∈ U.essential.obj.domain.carrier} := by
  have hNZ : GammaSetDefinable G {q : Point (M := M) 0 (k+1) | ∀ i, (q.2 i).val ≠ iRVZero} := by
    have h := gamma_rv_set_from_tuple_formula (nonzeroRVTuples_definable G (k+1))
    convert h using 1
    ext q
    change (∀ i, (q.2 i).val ≠ iRVZero) ↔ Proper (rvValues q.2)
    exact ⟨fun h i => ⟨(q.2 i).property, h i⟩, fun h i => (h i).2⟩
  have h := (gammaLogicInput G).image_graph ((gammaLogicInput G).restrict_graph hNZ
    ((gammaLogicInput G).swap_graph hU))
  convert h using 1
  ext p
  constructor
  · intro hp
    let u : U.underlying.obj.domain := ⟨p.2, rvEssentialLabels_subset U.underlying.obj hp⟩
    refine ⟨(Fin.elim0, U.underlying.obj.value u), ?_, u, rfl, rfl⟩
    exact (mem_rvEssentialLabels U.underlying.obj u).mp hp
  · rintro ⟨q, hq, u, hu, hv⟩
    change p.2 ∈ (rvEssentialLabels U.underlying.obj).carrier
    rw [← hu]
    refine (mem_rvEssentialLabels U.underlying.obj u).mpr (fun i => ?_)
    have := hq i
    rw [← hv] at this
    exact this

theorem essential_volume_gamma {U : PositiveRVVolumeObject (M := M) S k}
    (hU : RVMapGamma U.underlying.obj.volume G) : RVMapGamma U.essential.obj.volume G :=
  RVMapGamma.restrict_domain hU (rvEssentialLabels_subset U.underlying.obj) (essential_domain_gamma hU)

theorem essential_form_gamma {U : PositiveRVVolumeObject (M := M) S k}
    (hU : RVMapGamma U.underlying.obj.volume G) (hD : RVMapGamma U.form.map G) :
    RVMapGamma U.essentialForm.map G := by
  have h := RVMapGamma.restrict_domain hD (rvEssentialLabels_subset U.underlying.obj) (essential_domain_gamma hU)
  apply RVMapGamma.congr h
  intro u
  rfl

theorem rv_volume_lift_essential_iso_gamma (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (hGC : G.real ⊆ (C.base : Set M)) {U : PositiveRVVolumeObject (M := M) (C.base : Set M) k}
    (hU : VolumeObjectGamma U G) : (rvVolumeLiftEssentialIso hc C U).GammaDefinable G := by
  have hcore : VolumeObjectGamma U.essentialCore G :=
    hU.restrict U.essential.obj.domain (rvEssentialLabels_subset U.underlying.obj)
      (essential_domain_gamma hU.coordinates)
  have hA := gamma_rv_lift_carrier hc C hGC U.essentialCore hcore
  refine ⟨hA, hA, ?_⟩
  apply SpecialTransformations.Section5.GammaGraphDefinable.congr (gamma_vf_identity_graph _ hA)
  intro p q
  constructor
  · rintro ⟨hp, rfl⟩
    exact ⟨⟨p, hp⟩, rfl, rfl⟩
  · rintro ⟨u, rfl, rfl⟩
    exact ⟨u.property, rfl⟩

namespace GammaNamed

/-- A Gamma RV volume isomorphism has a Gamma VF lift. -/
theorem rv_volume_iso_lift_gamma (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (hGC : G.real ⊆ (C.base : Set M)) (hGenerated : VFGammaGeneratedBase G)
    {U V : PositiveRVVolumeObject (M := M) (C.base : Set M) k}
    (hU : VolumeObjectGamma U G) (hV : VolumeObjectGamma V G)
    (e : RVVolumeIso U V) (he : e.GammaDefinable G) :
    ∃ f : VFVolumeIso (rvVolumeLift U) (rvVolumeLift V), f.GammaDefinable G := by
  letI : CharZero (VFType (M := M)) := Section6.vfCharZero_of_model00 C.model00
  have heΓ : RVMapGamma (finiteIsoMap e.iso) G := he
  have hωΓ : RVMapGamma (volumeRatioMap e.iso) G :=
    RVMapGamma.scalarMul hc (essential_form_gamma hU.coordinates hU.density)
      (RVMapGamma.inverseScalar hc (heΓ.comp (essential_form_gamma hV.coordinates hV.density)))
  have hΓ : ∀ u : U.essential.obj.domain, Values.vrv ((volumeRatioMap e.iso u).val 0) =
      (rvGammaJacobian (U.essential.obj.value u)
        (V.essential.obj.value (finiteIsoMap e.iso u))
        (U.essential_nonzero u) (V.essential_nonzero (finiteIsoMap e.iso u))).val := by
    intro u
    rw [volumeRatioMap_value]
    exact e.gamma_volumeRatio u
  obtain ⟨D, _, hd, hD⟩ := e.rv
  have hRV : ∃ X : DefSet (rawRVSpace (M := M) U.essential.obj.arity) (C.base : Set M),
      rvDim X < k + 1 ∧ ∀ u : U.essential.obj.domain, u.val ∉ X.carrier →
        IsRVJacobianAt (volumeCorrespondence (finiteIsoMap e.iso)).carrier
          (U.essential.obj.value u) (V.essential.obj.value (finiteIsoMap e.iso u))
          ((volumeRatioMap e.iso u).val 0) :=
    ⟨D, hd, fun u hu => by rw [volumeRatioMap_value]; exact hD u hu⟩
  obtain ⟨Gm, hG, hGΓ, hlabel, Z, _, hz, hJ⟩ :=
    GammaLift.gamma_theorem_9_16_finite_volume hc C G hGenerated hGC e.iso
      U.essential_nonzero V.essential_nonzero (essential_volume_gamma hU.coordinates)
      (essential_volume_gamma hV.coordinates) heΓ (volumeRatioMap e.iso) hωΓ hΓ hRV
      Section2.ConstructedGaussGraph.acvf_graph_input
  have hPres : Section2.ConcreteVolumeForms.PreservesOff
      U.essentialForm.toSection2 V.essentialForm.toSection2 Gm := by
    refine ⟨Z, hz, ?_⟩
    intro p hp
    obtain ⟨J, hJ, hratio⟩ := hJ p hp
    have hlabels : liftLabelMap V.essential.obj (Gm p) =
        finiteIsoMap e.iso (liftLabelMap U.essential.obj p) := by
      obtain ⟨u, hu, hv⟩ := hlabel p
      have hsource : u = liftLabelMap U.essential.obj p := Subtype.ext hu
      apply Subtype.ext
      exact hv.symm.trans (congrArg (fun u => (finiteIsoMap e.iso u).val) hsource)
    refine ⟨J, hJ, ?_⟩
    change U.essentialForm.value (liftLabelMap U.essential.obj p) =
      V.essentialForm.value (liftLabelMap V.essential.obj (Gm p)) * CanonicalRV.encodedRv J
    rw [hlabels, hratio, volumeRatioMap_value, volumeRatio]
    exact (mul_div_cancel₀ _ (V.essentialForm_nonzero _)).symm
  obtain ⟨Z', hz', hJ'⟩ := hPres
  let b : VFVolumeBijection (rvVolumeLift U.essentialCore) (rvVolumeLift V.essentialCore) :=
    ⟨Gm, hG, VFAlmostEverywhere.of_exception Z' hz' hJ'⟩
  have hUcore : VolumeObjectGamma U.essentialCore G :=
    hU.restrict U.essential.obj.domain (rvEssentialLabels_subset U.underlying.obj)
      (essential_domain_gamma hU.coordinates)
  have hVcore : VolumeObjectGamma V.essentialCore G :=
    hV.restrict V.essential.obj.domain (rvEssentialLabels_subset V.underlying.obj)
      (essential_domain_gamma hV.coordinates)
  have hb : (VFVolumeIso.of_bijection b).GammaDefinable G :=
    ⟨gamma_rv_lift_carrier hc C hGC U.essentialCore hUcore,
      gamma_rv_lift_carrier hc C hGC V.essentialCore hVcore, hGΓ⟩
  exact ⟨((rvVolumeLiftEssentialIso hc C U).symm hc C).trans hc C
      ((VFVolumeIso.of_bijection b).trans hc C (rvVolumeLiftEssentialIso hc C V)),
    ((rv_volume_lift_essential_iso_gamma hc C hGC hU).symm hc C).trans hc C
      (hb.trans hc C (rv_volume_lift_essential_iso_gamma hc C hGC hV))⟩

end GammaNamed
end IntegrationInACVF.Section7
