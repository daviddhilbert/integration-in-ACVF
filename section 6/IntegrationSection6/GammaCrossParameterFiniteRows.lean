import IntegrationSection6.GammaSchemaFiniteRows
import IntegrationSection6.GammaSchemaRowAgreement

/-! Actual finite row semantics depend only on the complete raw rows,
including when the parameter block changes its arity or sort. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
namespace IntegrationInACVF.Section6
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {p q a k : ℕ} {sp : Fin p → SortTag} {sq : Fin q → SortTag}

theorem GammaSchemaRowAgreement.finiteRows
    {F : GammaFiniteRVSchema B p a k sp} {G : GammaFiniteRVSchema B q a k sq}
    {z : Fin p → M} {t : Fin q → M} (h : GammaSchemaRowAgreement F z G t) :
    F.finiteRow z ↔ G.finiteRow t := by
  unfold GammaFiniteRVSchema.finiteRow
  rw [h.domains,h.volumes]

end IntegrationInACVF.Section6
