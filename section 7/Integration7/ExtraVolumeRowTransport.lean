import Integration7.VolumeIsoSchemaRowTransport
import Integration7.ExtraVolumeRVValidity

/-! Auxiliary exceptional-set parameters can change independently of the
geometric parameter block, provided the actual exceptional row is retained. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section9
open IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {p q e f a b k j : ℕ}
variable {sp : Fin p → SortTag} {sq : Fin q → SortTag}
variable {se : Fin e → SortTag} {sf : Fin f → SortTag}

theorem extraVolumeChartRVRowValid_of_rowAgreement
    {F : GammaRVVolumeSchema B p a k sp} {F' : GammaRVVolumeSchema B q a k sq}
    {G : GammaRVVolumeSchema B p b k sp} {G' : GammaRVVolumeSchema B q b k sq}
    {H : Set (Fin ((p+a)+b) → M)} {H' : Set (Fin ((q+a)+b) → M)}
    {E : GammaFiniteRVSchema B (p+e) ((k+1)+1) j (Fin.append sp se)}
    {E' : GammaFiniteRVSchema B (q+f) ((k+1)+1) j (Fin.append sq sf)}
    {z : Fin p → M} {t : Fin q → M} {y : Fin e → M} {v : Fin f → M}
    (hz : ∀ i, sortEval (sp i) (z i)) (ht : ∀ i, sortEval (sq i) (t i))
    (hF : GammaVolumeRowAgreement F z F' t) (hG : GammaVolumeRowAgreement G z G' t)
    (hH : ∀ x w, Fin.append (Fin.append z x) w ∈ H ↔ Fin.append (Fin.append t x) w ∈ H')
    (hE : GammaSchemaRowAgreement E (Fin.append z y) E' (Fin.append t v))
    (hParams : ∀ i, sortEval (Fin.append sq sf i) (Fin.append t v i))
    (A : Finset (VolumeChartSupport (k+1)))
    (h : extraVolumeChartRVRowValid F G H A E (Fin.append z y)) :
    extraVolumeChartRVRowValid F' G' H' A E' (Fin.append t v) := by
  refine ⟨hParams,?_⟩
  intro r hr
  have hNewC := hr.1.1
  rw [append_dropExtraVolumeParameters] at hNewC
  have hOldC := (schemaVolumeCorrespondence_rowAgreement hz ht hF.weighted hG.weighted hH r).mpr hNewC
  have hExc : (Fin.append (Fin.append z y) r ∘ weightedPairSourceIndices (p+e) (k+1)) ∈ E.domain ↔
      (Fin.append (Fin.append t v) r ∘ weightedPairSourceIndices (q+f) (k+1)) ∈ E'.domain := by
    rw [weightedPairSourceIndices_append,weightedPairSourceIndices_append]
    exact hE.1 _
  have hRsort := ((sortedUniverse_append_iff (Fin.append sq sf)
    (fun _ : Fin (((k+1)+1)+((k+1)+1)) => .rv) (Fin.append t v) r).mp hr.2).2
  have hOld : Fin.append (Fin.append z y) r ∈ extraWeightedPairsOutsideException F G H E := by
    refine ⟨⟨?_,fun hx => hr.1.2 (hExc.mp hx)⟩,?_⟩
    · rw [append_dropExtraVolumeParameters]
      exact hOldC
    · exact (sortedUniverse_append_iff _ _ _ _).mpr ⟨h.1,hRsort⟩
  have hJ := (h.2 r hOld).1
  rw [append_dropExtraVolumeParameters] at hJ
  refine ⟨?_,hr.2⟩
  rw [append_dropExtraVolumeParameters]
  exact (supportedSchemaJacobianFormula_rowAgreement hz ht hF hG hH A r).mp hJ

end IntegrationInACVF.Section7
