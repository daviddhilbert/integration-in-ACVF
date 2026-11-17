module

public import Integration7.GammaPartialFocusVolumeSplits
public import Integration7.GammaCanonicalAdmissibilityRows
public import Integration7.GammaVolumeBlowupRowPromotion

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! Zero-cost original-Gamma volume isomorphisms before a focus are
absorbed into its source chart, preserving the number of blowups. -/

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
variable {B : Base (M := M)} {p k : ℕ} {sp : Fin p → SortTag}
local notation "N" => (@CanonicalStructure.normalize M sM)
local notation "hN" => (@CanonicalStructure.normalized_model M sM hM)

set_option maxHeartbeats 1200000 in
theorem gamma_partial_focus_volume_schema_precomposed {κ : Cardinal}
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (hreal : Cardinal.mk B.real < κ) (hgamma : Cardinal.mk B.gamma < κ)
    (z : Fin p → M) (hz : ∀ i, sortEval (sp i) (z i))
    (U : FiniteRV.GammaObjectAt ⟨B.real ∪ Set.range z,B.gamma⟩ (C.base : Set M) (k+1))
    (ω : VolumeForm (canonicalFiniteRVObject hc U.object).obj.domain)
    {A : SpecialTransformations.Section5.DefSet (M := M) (C.base : Set M) (k+1) (rvObjectArity U.object.obj)}
    (h : @PresentsLift M N hN (C.base : Set M) (k+1) U.object.obj (normalizedPointSet A))
    {j : Fin (rvObjectArity U.object.obj)} (D : Focus A (Fin.last k) j)
    (hA : GammaSetDefinable ⟨B.real ∪ Set.range z,B.gamma⟩ (carrier A))
    (hD : GammaFocusDefinable ⟨B.real ∪ Set.range z,B.gamma⟩ D)
    (δ : Fin (rvObjectArity U.object.obj)) (hDensity : ∀ u, ω.value u = u.val δ)
    (Ω₀ : PositiveRVVolumeObject (M := M) (C.base : Set M) k)
    (e : RVVolumeIso Ω₀
      (⟨canonicalFiniteRVObject hc U.object,ω⟩ : PositiveRVVolumeObject (M := M) (C.base : Set M) k))
    (he : e.GammaDefinable ⟨B.real ∪ Set.range z,B.gamma⟩)
    (F : GammaRVVolumeSchema B p Ω₀.underlying.obj.arity k sp)
    (G : GammaRVVolumeSchema B p ((k+1)+rvObjectArity U.object.obj) k sp)
    (hF : F.valid z) (hG : G.valid z)
    (PU : RVVolumeSchemaRow Ω₀ F z)
    (PV : RVVolumeSchemaRow (partialFocusVolumeImage hc C U.object ω h D δ hDensity) G z) :
    ∃ H : GammaRVVolumeBlowupSchema F G, H.valid z := by
  let L := focusActiveSet D
  let LD := liftLabelLocus L
  have hLD := liftLabelLocus_subset h (focusActiveSet_subset D)
  have hLΓ := (gammaActiveRVObject h D U.real_contains hA hD).domain_graph
  let V := FiniteRV.gammaRestrictAt U LD hLD hLΓ
  let R := FiniteRV.gammaComplementAt U LD hLΓ
  let Ω : PositiveRVVolumeObject (M := M) (C.base : Set M) k := ⟨canonicalFiniteRVObject hc U.object,ω⟩
  let LV := Ω.restrict (canonicalRawRVDomain hc LD) hLD
  let RV := Ω.restrict (Ω.underlying.obj.domain.sdiff (canonicalRawRVDomain hc LD)) Set.sdiff_subset
  have hDensityL : ∀ u, LV.form.value u = u.val δ := fun u => hDensity ⟨u.val,hLD u.property⟩
  have hDensityR : ∀ u, RV.form.value u = u.val δ := fun u => hDensity ⟨u.val,u.property.1⟩
  obtain ⟨hAd,eS,eT,hS,hT⟩ := gamma_partial_focus_volume_split hc C U ω h D hA hD δ hDensity
  obtain ⟨LF,hLF,PL⟩ := gamma_canonical_label_object_promotion hc C hκ hs hreal hgamma z hz V LV.form δ hDensityL
  obtain ⟨RF,hRF,PR⟩ := gamma_canonical_label_object_promotion hc C hκ hs hreal hgamma z hz R RV.form δ hDensityR
  obtain ⟨AP⟩ := LF.object.realize z hLF.1
  have hAdΓ := canonical_gamma_admissible_schema_row hc z V LV.form LF PL AP hAd
  exact gamma_volume_blowup_row_promotion hc C hκ hs C.model00 hreal hgamma z hz F G LF RF hF hG hLF hRF
    PU PV PL PR AP (canonicalGammaElementaryAdmissible hc C V LV.form hAd) hAdΓ (e.trans hc C eS) eT (he.trans hc C _ hS) hT

end IntegrationInACVF.Section7
