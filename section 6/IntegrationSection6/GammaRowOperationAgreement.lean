import IntegrationSection6.GammaSchemaRowAgreement
import IntegrationSection6.GammaRawElementaryRows
import IntegrationSection6.GammaRawCoproductSchemata

/-! Literal row agreement commutes with the actual elementary and
coproduct formula constructions, across different parameter sorts/arities. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
namespace IntegrationInACVF.Section6
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {p q a b k : ℕ} {sp : Fin p → SortTag} {sq : Fin q → SortTag}

theorem GammaSchemaRowAgreement.elementary
    {F : GammaFiniteRVSchema B p a k sp} {G : GammaFiniteRVSchema B q a k sq}
    {z : Fin p → M} {t : Fin q → M} (h : GammaSchemaRowAgreement F z G t)
    (hz : ∀ j, sortEval (sp j) (z j)) (ht : ∀ j, sortEval (sq j) (t j)) (i : Fin k) :
    GammaSchemaRowAgreement (F.elementaryFormula i) z (G.elementaryFormula i) t := by
  have hD (x : Fin (a+1) → RV (M := M)) :
      x ∈ (F.elementaryFormula i).rowDomain z ↔ x ∈ (G.elementaryFormula i).rowDomain t := by
    rw [F.elementary_row_domain_formula i z hz x B.real,G.elementary_row_domain_formula i t ht x B.real]
    exact and_congr (h.1 (fun j => (x (Fin.castAdd 1 j)).val)) Iff.rfl
  apply gammaSchemaRowAgreement_of_typed _ z _ t hD
  intro x y
  rw [F.elementary_row_volume_formula i z hz x y,G.elementary_row_volume_formula i t ht x y]
  exact and_congr (hD x) (exists_congr (fun v =>
    and_congr (h.2 (fun j => (x (Fin.castAdd 1 j)).val) (fun j => (v j).val)) Iff.rfl))

theorem GammaSchemaRowAgreement.coprod
    {F : GammaFiniteRVSchema B p a k sp} {G : GammaFiniteRVSchema B q a k sq}
    {H : GammaFiniteRVSchema B p b k sp} {K : GammaFiniteRVSchema B q b k sq}
    {z : Fin p → M} {t : Fin q → M} (hF : GammaSchemaRowAgreement F z G t) (hH : GammaSchemaRowAgreement H z K t)
    (hz : ∀ j, sortEval (sp j) (z j)) (ht : ∀ j, sortEval (sq j) (t j)) :
    GammaSchemaRowAgreement (F.coprodFormula H) z (G.coprodFormula K) t := by
  apply gammaSchemaRowAgreement_of_typed _ z _ t
  · intro w
    rw [F.coprod_row_domain_formula H z hz w,G.coprod_row_domain_formula K t ht w]
    exact or_congr
      (exists_congr (fun x => and_congr (hF.1 (fun j => (x j).val)) Iff.rfl))
      (exists_congr (fun x => and_congr (hH.1 (fun j => (x j).val)) Iff.rfl))
  · intro w v
    rw [F.coprod_row_volume_formula H z hz w v,G.coprod_row_volume_formula K t ht w v]
    exact or_congr
      (exists_congr (fun x => and_congr (hF.2 (fun j => (x j).val) (fun j => (v j).val)) Iff.rfl))
      (exists_congr (fun x => and_congr (hH.2 (fun j => (x j).val) (fun j => (v j).val)) Iff.rfl))

end IntegrationInACVF.Section6
