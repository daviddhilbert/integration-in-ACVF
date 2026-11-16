module

public import Integration7.CanonicalGammaElementaryObjects
public import Integration7.GammaVolumeFullChartRestriction
public import Integration7.PullbackCoordinateVolumeObjects
public import IntegrationSection6.FiniteGammaFocusCharts

@[expose] public section

/-! An original-Gamma full focus gives an actual volume isomorphism to
the canonical elementary volume object, with unchanged old-label density. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section5 (Point Focus carrier GammaSetDefinable GammaFocusDefinable GammaGraphDefinable rvObjectArity rvObjectDomain)
open IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {k : ℕ}
local notation "N" => (@CanonicalStructure.normalize M sM)
local notation "hN" => (@CanonicalStructure.normalized_model M sM hM)

set_option maxHeartbeats 800000 in
theorem gamma_full_focus_volume_comparison
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (U : FiniteRV.GammaObjectAt B (C.base : Set M) (k+1))
    (ω : VolumeForm (canonicalFiniteRVObject hc U.object).obj.domain)
    {A : SpecialTransformations.Section5.DefSet (M := M) (C.base : Set M) (k+1) (rvObjectArity U.object.obj)}
    (h : @PresentsLift M N hN (C.base : Set M) (k+1) U.object.obj (normalizedPointSet A))
    {j : Fin (rvObjectArity U.object.obj)} (D : Focus A (Fin.last k) j)
    (hfull : carrier A ⊆ D.locus)
    (hAd : GammaAdmissible U.toGamma.toGammaRVObject (Fin.last k))
    (hA : GammaSetDefinable B (carrier A)) (hD : GammaFocusDefinable B D)
    (δ : Fin (rvObjectArity U.object.obj)) (hDensity : ∀ u, ω.value u = u.val δ) :
    let hsmall := (Cardinal.mk_le_mk_of_subset U.real_contains).trans_lt C.small
    let T := FiniteRV.gammaFullFocusImageAt C.uncountable.le C.saturated C.model00 hsmall
      U h D hfull hAd hA hD
    ∀ (π : VolumeForm (canonicalFiniteRVObject hc T.object).obj.domain),
      (∀ u, π.value u = u.val (Fin.natAdd (k+1) δ)) →
      ∃ e : RVVolumeIso
        (⟨canonicalFiniteRVObject hc T.object,π⟩ : PositiveRVVolumeObject (M := M) (C.base : Set M) k)
        (elementaryVolumeObject C
          (⟨canonicalFiniteRVObject hc U.object,ω⟩ : PositiveRVVolumeObject (M := M) (C.base : Set M) k)
          (canonicalGammaElementaryAdmissible hc C U ω hAd)), e.GammaDefinable B := by
  intro hsmall T π hπ
  let W := FiniteRV.gammaElementaryAt C.uncountable.le C.saturated C.model00 hsmall U (Fin.last k) hAd
  let f := FiniteRV.gammaFullFocusIsoAt C.uncountable.le C.saturated C.model00 hsmall U h D hfull hAd hA hD
  let V : PositiveRVVolumeObject (M := M) (C.base : Set M) k := ⟨canonicalFiniteRVObject hc U.object,ω⟩
  let E := elementaryVolumeObject C V (canonicalGammaElementaryAdmissible hc C U ω hAd)
  let P : PositiveRVVolumeObject (M := M) (C.base : Set M) k := ⟨canonicalFiniteRVObject hc T.object,π⟩
  have hDom := canonical_gamma_elementary_domain hc C U ω hAd
  let g : (canonicalFiniteRVObject hc W.object).obj ≅ E.underlying.obj :=
    rvIsoOfCarrierEq _ _ _ _ hDom
      (fun u => (canonical_elementary_coordinates hc U.object.obj (Fin.last k) u).symm)
  let e : P.underlying ≅ E.underlying :=
    (canonicalFiniteRVIso hc f.iso).trans (rvFiniteIsoOfAmbient g)
  have hcoord : ∀ u, E.underlying.obj.value (finiteIsoMap e u) = P.underlying.obj.value u := by
    intro u
    have hg := canonical_elementary_coordinates hc U.object.obj (Fin.last k)
      (finiteIsoMap (canonicalFiniteRVIso hc f.iso) u)
    exact hg.symm.trans (originalAdmissibleFocusBlowup_volume h D hfull
      (hAd.ordinary C.uncountable.le C.saturated C.model00 hsmall) ⟨u.val,u.property⟩)
  have hφ : ∀ u, E.form.value (finiteIsoMap e u) = P.form.value u := by
    intro u
    let a : rvObjectDomain (originalFocusObject D) := ⟨u.val,u.property⟩
    have hk := originalAdmissibleFocusBlowup_key h D hfull
      (hAd.ordinary C.uncountable.le C.saturated C.model00 hsmall) a
    have hl := congrFun hk (Fin.natAdd (k+1) δ)
    simp only [rvAppend,Fin.append_right] at hl
    have hp := Section6.elementaryProjection_labels (canonicalFiniteRVObject hc U.object).obj
      (Fin.last k) (finiteIsoMap e u)
    change ω.value (Section6.elementaryProjection (canonicalFiniteRVObject hc U.object).obj
      (Fin.last k) (finiteIsoMap e u)) = π.value u
    rw [hDensity,hπ]
    exact (congrFun hp δ).trans
      ((congrFun (@Section6.elementaryProjection_labels M N hN (C.base : Set M) (k+1)
        U.object.obj (Fin.last k)
        (FiniteRV.isoAtMap f.iso a)) δ).symm.trans hl)
  refine ⟨RVVolumeIso.of_preserving_coordinates_full hc C e hcoord hφ,?_⟩
  apply gamma_volume_iso_of_preserving_coordinates_full hc C e hcoord hφ
    (gamma_essential_volume_domain P (canonical_gamma_object_volume_graph hc T))
  apply GammaGraphDefinable.congr f.graph
  intro p q
  constructor
  · rintro ⟨u,hu,hq⟩
    exact ⟨⟨u.val,u.property⟩,hu,hq⟩
  · rintro ⟨u,hu,hq⟩
    exact ⟨⟨u.val,u.property⟩,hu,hq⟩

end IntegrationInACVF.Section7
