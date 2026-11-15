import Integration7.NormalizedActualRVObjects
import Integration7.NormalizedElementaryGeometry

/-! Canonical transport of the literal normalized presentation returns
the original actual object, including its complete coordinate map. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {S : Set M} {n : ℕ}

theorem canonical_normalized_actual_rv_object (hc : CanonicalStructure.IsCanonical (M := M))
    (U : RVObject (M := M) S n) : canonicalRVObject hc (normalizedActualRVObject hc U) = U := by
  exact rvObject_eq_of_carrier_coordinates _ _ _ _ rfl (fun _ => rfl)

theorem canonical_normalized_actual_finite_rv_object (hc : CanonicalStructure.IsCanonical (M := M))
    (U : RVFiniteObject (M := M) S n) : canonicalFiniteRVObject hc (normalizedActualFiniteRVObject hc U) = U := by
  apply CategoryTheory.ObjectProperty.FullSubcategory.ext
  exact canonical_normalized_actual_rv_object hc U.obj

end IntegrationInACVF.Section7
