import Integration7.GammaDensityObjects
import Integration7.NonzeroDensityFormulas
import Integration7.GammaRVVolumeSchemata
import IntegrationSection6.GammaTupleRelationPromotion

/-! Actual original-Gamma coordinate-and-density presentations promote
to uniform volume schemata. The density graph has no finite-fibre premise;
its global nonvanishing guard leaves the given row exactly unchanged. -/

set_option backward.isDefEq.respectTransparency false
noncomputable section
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
open IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {p a k : ℕ}

theorem gamma_sorted_volume_object_promotion {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (hreal : Cardinal.mk B.real < κ) (hgamma : Cardinal.mk B.gamma < κ)
    (sp : Fin p → SortTag) (z : Fin p → M) (hz : ∀ i, sortEval (sp i) (z i))
    {D : Set (Fin a → RV (M := M))}
    {R : (Fin a → RV (M := M)) → (Fin (k+1) → RV (M := M)) → Prop}
    {W : (Fin a → RV (M := M)) → (Fin 1 → RV (M := M)) → Prop}
    (P : GammaVolumeGraphPresentation ⟨B.real ∪ Set.range z,B.gamma⟩ a (k+1) D R W) :
    ∃ F : GammaRVVolumeSchema B p a k sp, F.valid z ∧
      (∀ x, Fin.append z x ∈ F.object.domain ↔ x ∈ gammaRawObjectDomain P.finite.toGamma.toGammaRVObject) ∧
      (∀ x t, Fin.append (Fin.append z x) t ∈ F.object.volume ↔
        Fin.append x t ∈ gammaRawObjectVolume P.finite.toGamma.toGammaRVObject) ∧
      (∀ x ω, Fin.append (Fin.append z x) ω ∈ F.density ↔
        Fin.append x ω ∈ gammaRawObjectVolume P.densityObject) := by
  obtain ⟨A,hA,hAD,hAV⟩ := gamma_sorted_finite_object_promotion hκ hs hreal hgamma sp z hz P.finite.toGamma
  obtain ⟨H,hH,hHz⟩ := gamma_rv_tuple_relation_promotion B sp z hz
    (gammaRawObjectVolume P.densityObject) (gammaRawObjectVolume_definable P.densityObject)
  let F : GammaRVVolumeSchema B p a k sp := {
    object := A
    density := nonzeroDensityFormula H
    density_definable := nonzeroDensityFormula_definable hH
    density_nonzero := fun _ h => h.2 }
  have hFrow (x : Fin a → M) (ω : Fin 1 → M) :
      Fin.append (Fin.append z x) ω ∈ F.density ↔ Fin.append x ω ∈ gammaRawObjectVolume P.densityObject := by
    change Fin.append (Fin.append z x) ω ∈ nonzeroDensityFormula H ↔ _
    rw [nonzeroDensityFormula_append,hHz]
    exact ⟨And.left,fun h => ⟨h,P.rawDensity_nonzero x ω h⟩⟩
  refine ⟨F,⟨hA,hz,?_,?_⟩,hAD,hAV,hFrow⟩
  · intro x hx
    have hx' : x ∈ gammaRawObjectDomain P.densityObject := (hAD x).mp hx
    obtain ⟨ω,hω,hu⟩ := gammaRawObjectVolume_unique P.densityObject x hx'
    exact ⟨ω,(hFrow x ω).mpr hω,fun ω' hω' => hu ω' ((hFrow x ω').mp hω')⟩
  · intro x ω hxω
    obtain ⟨u,hx,_⟩ := (gammaRawObjectVolume_append_iff P.densityObject x ω).mp ((hFrow x ω).mp hxω)
    exact (hAD x).mpr ⟨u,hx⟩

end IntegrationInACVF.Section7
