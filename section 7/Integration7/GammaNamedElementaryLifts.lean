import Integration7.GammaNamedRVIsoLifts
import Integration7.CanonicalGammaElementaryLiftVolumes
import Integration7.ElementaryVolumeLiftInvariance

/-! Gamma lifts of elementary blowups. The volume-preserving lift of a
canonical elementary blowup is built from the generated-base focus diagram;
its special bijection and relabelling have Gamma graphs (Section 6), so the
lift has a Gamma graph. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section9 SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section5 (Point GammaSetDefinable GammaGraphDefinable gammaLogicInput
  GammaChainDefinable pointMapGraph)
open IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {k : ℕ}

theorem gamma_elementary_focus_full_lift_graph
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (U : FiniteRV.GammaObjectAt B (C.base : Set M) (k+1))
    (D : ElementaryLiftDiagram U.toGamma.toGammaRVObject (Fin.last k)) :
    GammaGraphDefinable B (vfMixedMapGraph (elementaryFocusFullLiftMap hc C
      (normalizedTypedLift_presents U.object.obj) D.focus D.full.ge D.admissible)) := by
  have L := gammaLogicInput B
  have hS := GammaChainDefinable.graph L _ D.special.invariant_graphs
  have hR := D.up_graph
  have hX : GammaGraphDefinable B (pointMapGraph (canonicalFocusLiftMap
      (normalizedTypedLift_presents U.object.obj) D.focus D.full.ge D.admissible)) := by
    apply SpecialTransformations.Section5.GammaGraphDefinable.congr (L.comp_graph hS hR)
    intro p q
    constructor
    · rintro ⟨z, ⟨a, rfl, rfl⟩, b, hb, rfl⟩
      have : b = (canonicalFocusSpecial (typedLift U.object.obj) D.focus).toMap a := Subtype.ext hb
      subst this
      exact ⟨a, rfl, rfl⟩
    · rintro ⟨a, rfl, rfl⟩
      exact ⟨_, ⟨a, rfl, rfl⟩, _, rfl, rfl⟩
  have hY := vf_mixed_map_graph_raw_special hc _ hX
  apply SpecialTransformations.Section5.GammaGraphDefinable.congr hY
  intro p q
  let Lm := literalVolumeLiftMap hc (canonicalRVObject hc U.object.obj) (typedLift U.object.obj)
    (canonicalRVObject_presentsLift hc (normalizedTypedLift_presents U.object.obj))
  have hL := literalVolumeLiftMap_bijective hc (canonicalRVObject hc U.object.obj) (typedLift U.object.obj)
    (canonicalRVObject_presentsLift hc (normalizedTypedLift_presents U.object.obj))
  constructor
  · rintro ⟨y, rfl, rfl⟩
    refine ⟨Lm y, rfl, ?_⟩
    unfold elementaryFocusFullLiftMap
    simp only [Map.comp_apply]
    rw [Map.inverse_apply]
    rfl
  · rintro ⟨x, rfl, rfl⟩
    refine ⟨Lm.inverse hL x, congrArg Subtype.val (Map.apply_inverse Lm hL x), ?_⟩
    unfold elementaryFocusFullLiftMap
    simp only [Map.comp_apply]
    rfl

/-- The canonical presentation isomorphism of an actual volume object (identity on labels). -/
def actualVolumeCanonicalPresentationIso (hc : CanonicalStructure.IsCanonical (M := M))
    (C : BaseContext M) (U : PositiveRVVolumeObject (M := M) (C.base : Set M) k) :
    RVVolumeIso U (canonicalActualVolumeObject hc U) :=
  let V := canonicalActualVolumeObject hc U
  let f : Map U.underlying.obj.domain V.underlying.obj.domain := Map.inclusion (fun _ h => h)
  have hf : Function.Bijective f := by
    constructor
    · intro u v h
      have hv := congrArg (fun w : V.underlying.obj.domain => w.val) h
      exact Subtype.ext hv
    · intro v
      exact ⟨⟨v.val,v.property⟩,rfl⟩
  RVVolumeIso.of_preserving_coordinates_full hc C
    (rvFiniteIsoOfAmbient (rvIsoOfVolumePreservingBijection f hf (fun _ => rfl))) (fun _ => rfl) (fun _ => rfl)

theorem actual_volume_canonical_presentation_iso_gamma (hc : CanonicalStructure.IsCanonical (M := M))
    (C : BaseContext M) {U : PositiveRVVolumeObject (M := M) (C.base : Set M) k}
    (hU : VolumeObjectGamma U B) : (actualVolumeCanonicalPresentationIso hc C U).GammaDefinable B := by
  have hE := essential_domain_gamma hU.coordinates
  apply SpecialTransformations.Section5.GammaGraphDefinable.congr (gamma_vf_identity_graph _ hE)
  intro x y
  constructor
  · rintro ⟨hx, rfl⟩
    exact ⟨⟨x.2, hx⟩, rfl, rfl⟩
  · rintro ⟨u, hu, hv⟩
    refine ⟨?_, ?_⟩
    · change x.2 ∈ U.essential.obj.domain.carrier
      rw [← hu]
      exact u.property
    · refine Prod.ext (funext (fun i => Fin.elim0 i)) ?_
      rw [← hu]
      exact hv

/-- The density identification of a canonical elementary blowup (identity on labels). -/
def canonicalElementaryDensityIdentificationIso
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (U : FiniteRV.GammaObjectAt B (C.base : Set M) (k+1))
    (ω : VolumeForm (canonicalFiniteRVObject hc U.object).obj.domain)
    (hAd : GammaAdmissible U.toGamma.toGammaRVObject (Fin.last k)) :
    RVVolumeIso (canonicalGammaElementaryDensityObject hc C U ω hAd)
      (elementaryVolumeObject C
        (⟨canonicalFiniteRVObject hc U.object,ω⟩ : PositiveRVVolumeObject (M := M) (C.base : Set M) k)
        (canonicalGammaElementaryAdmissible hc C U ω hAd)) := by
  let X := canonicalGammaElementaryDensityObject hc C U ω hAd
  let Y := elementaryVolumeObject C
    (⟨canonicalFiniteRVObject hc U.object,ω⟩ : PositiveRVVolumeObject (M := M) (C.base : Set M) k)
    (canonicalGammaElementaryAdmissible hc C U ω hAd)
  have hDomain := canonical_gamma_elementary_domain hc C U ω hAd
  let f : Map X.underlying.obj.domain Y.underlying.obj.domain := Map.inclusion hDomain.le
  have hf : Function.Bijective f := by
    constructor
    · intro u v h
      have hv := congrArg (fun w : Y.underlying.obj.domain => w.val) h
      exact Subtype.ext hv
    · intro v
      exact ⟨⟨v.val,hDomain.ge v.property⟩,rfl⟩
  have hcoord (u : X.underlying.obj.domain) : Y.underlying.obj.value (f u) = X.underlying.obj.value u :=
    (canonical_elementary_coordinates hc U.object.obj (Fin.last k) u).symm
  let e := rvFiniteIsoOfAmbient (rvIsoOfVolumePreservingBijection f hf hcoord)
  exact RVVolumeIso.of_preserving_coordinates_full hc C e hcoord (fun u => by
    change ω.value (Section6.elementaryProjection (canonicalRVObject hc U.object.obj) (Fin.last k) (f u)) =
      ω.value (canonicalRawRVMap hc (@Section6.elementaryProjection M (@CanonicalStructure.normalize M sM)
        (@CanonicalStructure.normalized_model M sM hM) (C.base : Set M) (k+1) U.object.obj (Fin.last k)) u)
    apply congrArg ω.value
    apply Subtype.ext
    exact (Section6.elementaryProjection_labels (canonicalRVObject hc U.object.obj) (Fin.last k) (f u)).trans
      (@Section6.elementaryProjection_labels M (@CanonicalStructure.normalize M sM)
        (@CanonicalStructure.normalized_model M sM hM) (C.base : Set M) (k+1) U.object.obj (Fin.last k)
        ⟨u.val,u.property⟩).symm)

theorem canonical_elementary_density_object_gamma
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (U : FiniteRV.GammaObjectAt B (C.base : Set M) (k+1))
    (ω : VolumeForm (canonicalFiniteRVObject hc U.object).obj.domain) (hω : RVMapGamma ω.map B)
    (hAd : GammaAdmissible U.toGamma.toGammaRVObject (Fin.last k)) :
    VolumeObjectGamma (canonicalGammaElementaryDensityObject hc C U ω hAd) B := by
  let X := canonicalGammaElementaryDensityObject hc C U ω hAd
  let Y := elementaryVolumeObject C
    (⟨canonicalFiniteRVObject hc U.object,ω⟩ : PositiveRVVolumeObject (M := M) (C.base : Set M) k)
    (canonicalGammaElementaryAdmissible hc C U ω hAd)
  have hY : VolumeObjectGamma Y B := VolumeObjectGamma.elementary_canonical hc C _
    (VolumeObjectGamma.canonical hc U ω hω) (canonicalGammaElementaryAdmissible hc C U ω hAd)
  let e := canonicalElementaryDensityIdentificationIso hc C U ω hAd
  have hDomain := canonical_gamma_elementary_domain hc C U ω hAd
  have hval (x : X.underlying.obj.domain) :
      Y.underlying.obj.value ⟨x.val, hDomain.le x.property⟩ = X.underlying.obj.value x :=
    (canonical_elementary_coordinates hc U.object.obj (Fin.last k) x).symm
  have hdens (x : X.underlying.obj.domain) :
      Y.form.value ⟨x.val, hDomain.le x.property⟩ = X.form.value x := by
    change ω.value (Section6.elementaryProjection (canonicalRVObject hc U.object.obj) (Fin.last k)
        ⟨x.val, hDomain.le x.property⟩) =
      ω.value (canonicalRawRVMap hc (@Section6.elementaryProjection M (@CanonicalStructure.normalize M sM)
        (@CanonicalStructure.normalized_model M sM hM) (C.base : Set M) (k+1) U.object.obj (Fin.last k)) x)
    apply congrArg ω.value
    apply Subtype.ext
    exact (Section6.elementaryProjection_labels (canonicalRVObject hc U.object.obj) (Fin.last k) _).trans
      (@Section6.elementaryProjection_labels M (@CanonicalStructure.normalize M sM)
        (@CanonicalStructure.normalized_model M sM hM) (C.base : Set M) (k+1) U.object.obj (Fin.last k)
        ⟨x.val,x.property⟩).symm
  refine ⟨?_, ?_⟩
  · apply SpecialTransformations.Section5.GammaGraphDefinable.congr hY.coordinates
    intro p q
    constructor
    · rintro ⟨y, hy, hq⟩
      refine ⟨⟨y.val, hDomain.ge y.property⟩, hy, ?_⟩
      rw [← hq]
      exact (hval ⟨y.val, hDomain.ge y.property⟩).symm
    · rintro ⟨x, hx, hq⟩
      refine ⟨⟨x.val, hDomain.le x.property⟩, hx, ?_⟩
      rw [← hq]
      exact hval x
  · apply SpecialTransformations.Section5.GammaGraphDefinable.congr hY.density
    intro p q
    constructor
    · rintro ⟨y, hy, hq⟩
      refine ⟨⟨y.val, hDomain.ge y.property⟩, hy, ?_⟩
      rw [← hq]
      funext i
      fin_cases i
      exact (hdens ⟨y.val, hDomain.ge y.property⟩).symm
    · rintro ⟨x, hx, hq⟩
      refine ⟨⟨x.val, hDomain.le x.property⟩, hx, ?_⟩
      rw [← hq]
      funext i
      fin_cases i
      exact hdens x

theorem canonical_elementary_density_identification_gamma
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (U : FiniteRV.GammaObjectAt B (C.base : Set M) (k+1))
    (ω : VolumeForm (canonicalFiniteRVObject hc U.object).obj.domain) (hω : RVMapGamma ω.map B)
    (hAd : GammaAdmissible U.toGamma.toGammaRVObject (Fin.last k)) :
    (canonicalElementaryDensityIdentificationIso hc C U ω hAd).GammaDefinable B := by
  have hE := essential_domain_gamma (canonical_elementary_density_object_gamma hc C U ω hω hAd).coordinates
  apply SpecialTransformations.Section5.GammaGraphDefinable.congr (gamma_vf_identity_graph _ hE)
  intro x y
  constructor
  · rintro ⟨hx, rfl⟩
    exact ⟨⟨x.2, hx⟩, rfl, rfl⟩
  · rintro ⟨u, hu, hv⟩
    refine ⟨?_, ?_⟩
    · change x.2 ∈ (canonicalGammaElementaryDensityObject hc C U ω hAd).essential.obj.domain.carrier
      rw [← hu]
      exact u.property
    · refine Prod.ext (funext (fun i => Fin.elim0 i)) ?_
      rw [← hu]
      exact hv

namespace GammaNamed

theorem canonical_elementary_volume_lift_iso_gamma
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (hGenerated : VFGammaGeneratedBase B)
    (U : FiniteRV.GammaObjectAt B (C.base : Set M) (k+1))
    (ω : VolumeForm (canonicalFiniteRVObject hc U.object).obj.domain) (hω : RVMapGamma ω.map B)
    (hAd : GammaAdmissible U.toGamma.toGammaRVObject (Fin.last k)) :
    ∃ f : VFVolumeIso
      (rvVolumeLift (⟨canonicalFiniteRVObject hc U.object,ω⟩ : PositiveRVVolumeObject (M := M) (C.base : Set M) k))
      (rvVolumeLift (elementaryVolumeObject C
        (⟨canonicalFiniteRVObject hc U.object,ω⟩ : PositiveRVVolumeObject (M := M) (C.base : Set M) k)
        (canonicalGammaElementaryAdmissible hc C U ω hAd))), f.GammaDefinable B := by
  obtain ⟨D⟩ := lemma_6_12 C.uncountable.le C.saturated C.model00
    ((Cardinal.mk_le_mk_of_subset U.real_contains).trans_lt C.small) hGenerated hAd
  let h := normalizedTypedLift_presents U.object.obj
  let hFull := D.full.ge
  let b : VFVolumeBijection
      (rvVolumeLift (⟨canonicalFiniteRVObject hc U.object,ω⟩ : PositiveRVVolumeObject (M := M) (C.base : Set M) k))
      (rvVolumeLift (canonicalGammaElementaryDensityObject hc C U ω hAd)) :=
    ⟨elementaryFocusFullLiftMap hc C h D.focus hFull D.admissible,
      elementary_focus_full_lift_map_bijective hc C h D.focus hFull D.admissible
        (typedLift_pullback U.object.obj),
      elementary_focus_full_lift_preserves_volume hc C (Nat.zero_lt_succ k) h D.focus hFull
        D.admissible (typedLift_pullback U.object.obj) ω⟩
  have hX := canonical_elementary_density_object_gamma hc C U ω hω hAd
  have hW : VolumeObjectGamma
      (⟨canonicalFiniteRVObject hc U.object,ω⟩ : PositiveRVVolumeObject (M := M) (C.base : Set M) k) B :=
    VolumeObjectGamma.canonical hc U ω hω
  have hb : (VFVolumeIso.of_bijection b).GammaDefinable B :=
    ⟨gamma_rv_lift_carrier hc C U.real_contains _ hW, gamma_rv_lift_carrier hc C U.real_contains _ hX,
      gamma_elementary_focus_full_lift_graph hc C U D⟩
  have hY := VolumeObjectGamma.elementary_canonical hc C _ hW (canonicalGammaElementaryAdmissible hc C U ω hAd)
  obtain ⟨g, hg⟩ := rv_volume_iso_lift_gamma hc C U.real_contains hGenerated hX hY
    (canonicalElementaryDensityIdentificationIso hc C U ω hAd)
    (canonical_elementary_density_identification_gamma hc C U ω hω hAd)
  exact ⟨(VFVolumeIso.of_bijection b).trans hc C g, hb.trans hc C hg⟩

theorem elementary_volume_lift_iso_gamma
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (hBC : B.real ⊆ (C.base : Set M)) (hGenerated : VFGammaGeneratedBase B)
    (U : PositiveRVVolumeObject (M := M) (C.base : Set M) k) (hU : VolumeObjectGamma U B)
    (hAd : BlowupAdmissible U) (hCenter : GammaBlowupCenter U B) :
    ∃ f : VFVolumeIso (rvVolumeLift U) (rvVolumeLift (elementaryVolumeObject C U hAd)), f.GammaDefinable B := by
  let P := normalizedActualVolumeGammaObject hc U hU hBC
  let hPA := normalized_actual_volume_gamma_admissible hc U hU hBC hAd hCenter
  let V := canonicalActualVolumeObject hc U
  let hAdV := canonicalGammaElementaryAdmissible hc C P V.form hPA
  have hVform : RVMapGamma V.form.map B := by
    apply RVMapGamma.congr hU.density
    intro u
    rfl
  obtain ⟨f, hf⟩ := canonical_elementary_volume_lift_iso_gamma hc C hGenerated P V.form hVform hPA
  let e := actualVolumeCanonicalPresentationIso hc C U
  have he := actual_volume_canonical_presentation_iso_gamma hc C hU
  have hV : VolumeObjectGamma V B := VolumeObjectGamma.canonical hc P V.form hVform
  obtain ⟨g, hg⟩ := rv_volume_iso_lift_gamma hc C hBC hGenerated hU hV e he
  obtain ⟨e', he'⟩ := VolumeObjectGamma.elementary_comparison hc C hU hV hAd hAdV e he
  obtain ⟨g', hg'⟩ := rv_volume_iso_lift_gamma hc C hBC hGenerated
    (VolumeObjectGamma.elementary_canonical hc C U hU hAd)
    (VolumeObjectGamma.elementary_canonical hc C V hV hAdV) e' he'
  exact ⟨g.trans hc C (f.trans hc C (g'.symm hc C)), hg.trans hc C (hf.trans hc C (hg'.symm hc C))⟩

end GammaNamed
end IntegrationInACVF.Section7
