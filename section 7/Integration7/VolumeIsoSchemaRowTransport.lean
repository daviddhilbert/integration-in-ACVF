import Integration7.VolumeFormulaRowTransport
import Integration7.GammaVolumeIsomorphismSchemata

/-! Both volume clauses transport across exact primitive rows. The
supported Jacobian graph and the exceptional set are preserved separately. -/

set_option backward.isDefEq.respectTransparency false
noncomputable section
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section9
open IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {p q a b k j : ℕ} {sp : Fin p → SortTag} {sq : Fin q → SortTag}
variable {F : GammaRVVolumeSchema B p a k sp} {F' : GammaRVVolumeSchema B q a k sq}
variable {G : GammaRVVolumeSchema B p b k sp} {G' : GammaRVVolumeSchema B q b k sq}
variable {H : Set (Fin ((p+a)+b) → M)} {H' : Set (Fin ((q+a)+b) → M)}
variable {z : Fin p → M} {t : Fin q → M}

theorem volumeChartGammaRowValid_of_rowAgreement
    (hz : ∀ i, sortEval (sp i) (z i)) (ht : ∀ i, sortEval (sq i) (t i))
    (hF : GammaVolumeRowAgreement F z F' t) (hG : GammaVolumeRowAgreement G z G' t)
    (hH : ∀ x y, Fin.append (Fin.append z x) y ∈ H ↔ Fin.append (Fin.append t x) y ∈ H')
    (h : volumeChartGammaRowValid F G H z) : volumeChartGammaRowValid F' G' H' t :=
  ⟨ht,fun r hr => h.2 r ((schemaVolumeCorrespondence_rowAgreement hz ht hF.weighted hG.weighted hH r).mpr hr)⟩

theorem supportedSchemaJacobianFormula_rowAgreement
    (hz : ∀ i, sortEval (sp i) (z i)) (ht : ∀ i, sortEval (sq i) (t i))
    (hF : GammaVolumeRowAgreement F z F' t) (hG : GammaVolumeRowAgreement G z G' t)
    (hH : ∀ x y, Fin.append (Fin.append z x) y ∈ H ↔ Fin.append (Fin.append t x) y ∈ H')
    (A : Finset (VolumeChartSupport (k+1))) (r : Fin (((k+1)+1)+((k+1)+1)) → M) :
    Fin.append z r ∈ supportedSchemaJacobianFormula F G H A ↔
      Fin.append t r ∈ supportedSchemaJacobianFormula F' G' H' A := by
  apply weightedJacobianFormula_rowAgreement hz ht
  intro u ω
  change (∃ σ ∈ A, Fin.append (Fin.append z u) ω ∈ tupleVolumeChartGraph σ _) ↔
    (∃ σ ∈ A, Fin.append (Fin.append t u) ω ∈ tupleVolumeChartGraph σ _)
  exact exists_congr (fun σ => and_congr Iff.rfl
    (tupleVolumeChartGraph_rowAgreement σ (schemaVolumeCorrespondence_rowAgreement hz ht hF.1 hG.1 hH) u ω))

theorem volumeChartRVRowValid_of_rowAgreement
    {E : GammaFiniteRVSchema B p ((k+1)+1) j sp} {E' : GammaFiniteRVSchema B q ((k+1)+1) j sq}
    (hz : ∀ i, sortEval (sp i) (z i)) (ht : ∀ i, sortEval (sq i) (t i))
    (hF : GammaVolumeRowAgreement F z F' t) (hG : GammaVolumeRowAgreement G z G' t)
    (hH : ∀ x y, Fin.append (Fin.append z x) y ∈ H ↔ Fin.append (Fin.append t x) y ∈ H')
    (hE : GammaSchemaRowAgreement E z E' t) (A : Finset (VolumeChartSupport (k+1)))
    (h : volumeChartRVRowValid F G H A E z) : volumeChartRVRowValid F' G' H' A E' t := by
  refine ⟨ht,?_⟩
  intro r hr
  have hX : (Fin.append z r ∘ weightedPairSourceIndices p (k+1)) ∈ E.domain ↔
      (Fin.append t r ∘ weightedPairSourceIndices q (k+1)) ∈ E'.domain := by
    rw [weightedPairSourceIndices_append,weightedPairSourceIndices_append]
    exact hE.1 _
  have hOld : Fin.append z r ∈ weightedPairsOutsideException F G H E :=
    ⟨(schemaVolumeCorrespondence_rowAgreement hz ht hF.weighted hG.weighted hH r).mpr hr.1,
      fun hx => hr.2 (hX.mp hx)⟩
  exact (supportedSchemaJacobianFormula_rowAgreement hz ht hF hG hH A r).mp (h.2 r hOld)

end IntegrationInACVF.Section7
