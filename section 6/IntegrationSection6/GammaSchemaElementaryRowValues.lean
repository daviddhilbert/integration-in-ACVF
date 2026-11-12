import IntegrationSection6.GammaSchemaFiniteRowPresentations
import IntegrationSection6.ElementaryValuePrograms

/-! Actual elementary row values are the native blowup of the old volume
value and the new parameter. No uniform cardinality bound is required. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
namespace IntegrationInACVF.Section6
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {p a k : ℕ} {sp : Fin p → SortTag}
local notation "N" => (@CanonicalStructure.normalize M sM)
local notation "hN" => (@CanonicalStructure.normalized_model M sM hM)

theorem GammaFiniteRVSchema.rowValue_elementary (F : GammaFiniteRVSchema B p a k sp)
    (z : Fin p → M) (hz : ∀ j, sortEval (sp j) (z j)) (i : Fin k)
    (hF : F.finiteRow z) (hE : (F.elementaryFormula i).finiteRow z)
    (x : Fin (a+1) → RV (M := M)) (hx : x ∈ (F.elementaryFormula i).rowDomain z) :
    (F.elementaryFormula i).rowValue z x =
      @blowupValue M N hN k i (F.rowValue z (x ∘ Fin.castAdd 1)) (x (Fin.natAdd a 0)) := by
  have hOld := ((F.elementary_row_domain_formula i z hz x B.real).mp hx).1
  apply ((F.elementaryFormula i).rowValue_graph_of_finiteRow z hE x hx _).mp
  apply (F.elementary_row_volume_formula i z hz x _).mpr
  refine ⟨hx,F.rowValue z (x ∘ Fin.castAdd 1),
    (F.rowValue_graph_of_finiteRow z hF _ hOld _).mpr rfl,?_⟩
  exact @oldVolumeParameterBlowupMap_append M N hN k B.real i _ (x ∘ Fin.natAdd a)

end IntegrationInACVF.Section6
