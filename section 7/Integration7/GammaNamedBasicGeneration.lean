import Integration7.GammaNamedRVIsoSemiring
import Integration7.HKBasicGeneration
import Integration7.HKDegreeOnePrincipalFactors
import Integration7.GammaElementaryBlowupIsomorphisms
import Integration7.GammaElementaryVolumeGraphs
import IntegrationSection6.GammaBasicAdmissibility

/-! Basic generation for Gamma-named classes. The degree-one point and cone
are Gamma objects related by a Gamma blowup. Every elementary Gamma blowup
factors, up to Gamma isomorphisms, as a Gamma head factor times the point
(source) and times the cone (target); the comparison isomorphism after the
blowup is the existing Gamma corrected isomorphism. Hence a ring map from
Gamma isomorphism classes identifying point and cone identifies Gamma
blowup-equivalent objects. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry SpecialTransformations.Section9
open SpecialTransformations.Section5 (Point GammaSetDefinable GammaGraphDefinable gammaLogicInput)
open IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {B : Base (M := M)} {k : ℕ}

theorem VolumeObjectGamma.degreeOnePoint (hc : CanonicalStructure.IsCanonical (M := M)) (S : Set M) :
    VolumeObjectGamma (degreeOnePointVolumeObject (M := M) S) B := by
  have hD := gamma_rv_univ_set B 0 S
  refine ⟨gamma_real_rv_map_graph hc B _
    (FiniteRV.constantOneVolumeMap B.real (DefSet.univ (rawRVSpace (M := M) 0) B.real)) hD (fun _ => rfl),?_⟩
  exact RVMapGamma.scalarOne hc _ hD

theorem VolumeObjectGamma.degreeOneCone (hc : CanonicalStructure.IsCanonical (M := M)) (S : Set M) :
    VolumeObjectGamma (degreeOneConeVolumeObject (M := M) S) B := by
  have hD : GammaSetDefinable B {p : Point (M := M) 0 1 |
      p.2 ∈ (degreeOneConeVolumeObject (M := M) S).underlying.obj.domain.carrier} :=
    gamma_actual_blowup_cone hc
  refine ⟨gamma_rv_coordinate_map hc _ id hD (fun _ => rfl),?_⟩
  exact RVMapGamma.scalarOne hc _ hD

theorem GammaBlowupCenter.degreeOnePoint (S : Set M) :
    GammaBlowupCenter (degreeOnePointVolumeObject (M := M) S) B := by
  intro u
  change AlgebraicAtBase _ .rv (1 : CanonicalRV.RVSort M).val
  rw [RVOperations.one_val]
  exact gamma_rv_one_algebraic _

theorem gamma_degree_one_basic_elementary_iso (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M) :
    (degreeOneBasicElementaryIso hc C).GammaDefinable B := by
  let P := degreeOnePointVolumeObject (M := M) (C.base : Set M)
  have hP : VolumeObjectGamma P B := VolumeObjectGamma.degreeOnePoint hc _
  have hW := VolumeObjectGamma.elementary_canonical hc C P hP (degreeOnePointAdmissible hc (C.base : Set M))
  exact gamma_volume_iso_of_full_map _ _ (gamma_essential_volume_domain _ hW.coordinates)
    (gamma_rv_unpack_snd hc P.underlying.obj.domain (blowupConeSet (C.base : Set M)) hW.domain_graph)
    (fun _ => rfl)

theorem VolumeBlowup.GammaDefinable.ofElementary (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (U : PositiveRVVolumeObject (M := M) (C.base : Set M) k) (hU : VolumeObjectGamma U B)
    (hAd : BlowupAdmissible U) (hCenter : GammaBlowupCenter U B) :
    (VolumeBlowup.ofElementary hc C (elementaryVolumeBlowup C U hAd)).GammaDefinable B := by
  have hW := VolumeObjectGamma.elementary_canonical hc C U hU hAd
  exact ⟨hU,VolumeObjectGamma.empty _ k,hW,gamma_canonical_full_packed_chart hc C U hAd hU,hCenter,
    (gamma_volume_coprod_right_unit hc C hU).symm hc C B,
    (gamma_volume_coprod_right_unit hc C hW).symm hc C B⟩

/-- The Gamma basic relation: the degree-one point and cone are Gamma blowup equivalent. -/
theorem gamma_degree_one_basic_volume_relation (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M) :
    GammaVolumeBlowupEquivalent B (C.base : Set M) 0
      ⟨degreeOnePointVolumeObject (C.base : Set M),VolumeObjectGamma.degreeOnePoint hc _⟩
      ⟨degreeOneConeVolumeObject (C.base : Set M),VolumeObjectGamma.degreeOneCone hc _⟩ := by
  let P := degreeOnePointVolumeObject (M := M) (C.base : Set M)
  have hP : VolumeObjectGamma P B := VolumeObjectGamma.degreeOnePoint hc _
  have hAd := degreeOnePointAdmissible hc (C.base : Set M)
  have hW := VolumeObjectGamma.elementary_canonical hc C P hP hAd
  have h1 := GammaVolumeBlowupEquivalent.of_blowup hc C B (U := ⟨P,hP⟩)
    (V := ⟨elementaryVolumeObject C P hAd,hW⟩) (VolumeBlowup.ofElementary hc C (elementaryVolumeBlowup C P hAd))
    (VolumeBlowup.GammaDefinable.ofElementary hc C P hP hAd (GammaBlowupCenter.degreeOnePoint _))
  exact h1.trans hc C B (GammaVolumeBlowupEquivalent.of_iso C B (degreeOneBasicElementaryIso hc C)
    (gamma_degree_one_basic_elementary_iso hc C))

/-! ### Elementary factorization, positive heads -/

theorem VolumeObjectGamma.admissibleHead (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    {U : PositiveRVVolumeObject (M := M) (C.base : Set M) (k+1)} (hU : VolumeObjectGamma U B)
    (h : BlowupAdmissible U) : VolumeObjectGamma (admissibleHeadVolumeFactor C U h) B :=
  ⟨hU.coordinates.select hc _,(RVMapGamma.scalarMul hc hU.density (hU.coordinates.select hc _)).congr
    (fun _ => rfl)⟩

theorem admissible_head_point_map_raw (C : BaseContext M)
    (U : PositiveRVVolumeObject (M := M) (C.base : Set M) (k+1)) (h : BlowupAdmissible U)
    (u : U.underlying.obj.domain) :
    (admissibleHeadPointMap C U h u).val = u.val ∘ Fin.cast (Nat.add_zero _) := by
  change Fin.append u.val _ = _
  exact Fin.append_right_nil _ _ rfl

theorem gamma_admissible_head_point_iso (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    {U : PositiveRVVolumeObject (M := M) (C.base : Set M) (k+1)} (hU : VolumeObjectGamma U B)
    (h : BlowupAdmissible U) : (admissibleHeadPointVolumeIso C U h).GammaDefinable B :=
  gamma_volume_iso_of_full_map _ (admissibleHeadPointMap C U h)
    (gamma_essential_volume_domain _ hU.coordinates)
    (gamma_rv_coordinate_map hc _ _ hU.domain_graph (admissible_head_point_map_raw C U h)) (fun _ => rfl)

theorem gamma_elementary_head_cone_iso (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    {U W : PositiveRVVolumeObject (M := M) (C.base : Set M) (k+1)} (b : ElementaryBlowup U W)
    (hU : VolumeObjectGamma U B) (hW : VolumeObjectGamma W B) (hb : RVMapGamma b.packedChartMap B) :
    ∃ e : RVVolumeIso W ((admissibleHeadVolumeFactor C U b.admissible).prod
      (degreeOneConeVolumeObject (C.base : Set M))), e.GammaDefinable B := by
  let H := admissibleHeadVolumeFactor C U b.admissible
  let P := degreeOnePointVolumeObject (M := M) (C.base : Set M)
  have hAd := degreeOnePointAdmissible hc (C.base : Set M)
  let e := elementaryVolumeBlowup C P hAd
  have hH : VolumeObjectGamma H B := hU.admissibleHead hc C b.admissible
  have hP : VolumeObjectGamma P B := VolumeObjectGamma.degreeOnePoint hc _
  have hHP : VolumeObjectGamma (H.prod P) B := hH.prod hc hP
  have hEP := VolumeObjectGamma.elementary_canonical hc C P hP hAd
  have hHE : VolumeObjectGamma (H.prod (elementaryVolumeObject C P hAd)) B := hH.prod hc hEP
  obtain ⟨f,hf⟩ := exists_gamma_elementaryBlowupIso hc C B (admissibleHeadPointVolumeIso C U b.admissible)
    b (e.product_left H) hU.coordinates hHP.coordinates hU.density hHP.density
    (gamma_admissible_head_point_iso hc C hU b.admissible)
    (b.gamma_essential_packed_chart hW hb)
    ((e.product_left H).gamma_essential_packed_chart hHE
      (gamma_product_left_packed_chart hc e H hH (gamma_canonical_full_packed_chart hc C P hAd hP)))
  exact ⟨f.trans hc C ((RVVolumeIso.refl hc C H).prod hc C (degreeOneBasicElementaryIso hc C)),
    hf.trans hc C B ((hH.identity_iso hc C).prod hc C (gamma_degree_one_basic_elementary_iso hc C))⟩

end IntegrationInACVF.Section7
