import Integration7.NativeRectangleFactorizations
import IntegrationSection4.CellRectangles

/-! The checked nonbalanced-cell rectangle theorem supplies the actual
native product presentation, including its singleton first-projection
boundary, without requiring a separately named position function. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section5
open IntegrationInACVF.Section4 IntegrationInACVF.Section4.Cells

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M}

theorem nonbalanced_cell_native_rectangle_factorization
    (Z : DefSet (M := M) S 2 0) (δ : Values.Gamma (M := M)) (hδ : 1 < δ)
    {f : VF (M := M) → VF (M := M)} {t : RV (M := M)}
    (hCell : CellData (nativeVFPairDomain Z) f t) (ht : t ≠ rv (0 : VF (M := M)))
    (hNot : ¬ ∃ u, IsBalanced (nativeVFPairDomain Z) f u t) :
    Z = nativeUnaryProductDomain (nativeVFCoordinateDomain Z 0) (nativeVFCoordinateDomain Z 1) := by
  obtain ⟨Y,hY,hRect⟩ := CellRectangles.rectangle δ hδ hCell ht hNot
  exact native_rectangle_factorization_of_pair_product Z (first (nativeVFPairDomain Z)) Y hRect

end IntegrationInACVF.Section7
