import IntegrationSection3ACVF.FullGammaControllers
import IntegrationSection3ACVF.FiniteOrderBounds

/-! Definable completeness and the finite/interval dichotomy on the
actual Gamma quotient over the full original interpreted parameter base. -/

open Set Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer SpecialTransformations.Section3
open IntegrationInACVF.Section3

namespace IntegrationInACVF.Section3ACVF.FullGammaBounds

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

theorem exists_isLUB (h00 : M ⊨ Axioms.ACVF00) (B : FullBaseAtomicity.Base (M := M))
    {D : Set (Values.Gamma (M := M))} (hD : FullGammaSyntax.Scalar B D)
    (hne : D.Nonempty) (hBound : BddAbove D) : ∃ r, IsLUB D r :=
  FiniteOrderBounds.exists_isLUB hne hBound (FullGammaControllers.finite_controller h00 B D hD)

theorem exists_isGLB (h00 : M ⊨ Axioms.ACVF00) (B : FullBaseAtomicity.Base (M := M))
    {D : Set (Values.Gamma (M := M))} (hD : FullGammaSyntax.Scalar B D)
    (hne : D.Nonempty) (hBound : BddBelow D) : ∃ r, IsGLB D r :=
  FiniteOrderBounds.exists_isGLB hne hBound (FullGammaControllers.finite_controller h00 B D hD)

theorem finite_or_contains_interval (h00 : M ⊨ Axioms.ACVF00) (B : FullBaseAtomicity.Base (M := M))
    {D : Set (Values.Gamma (M := M))} (hD : FullGammaSyntax.Scalar B D) :
    D.Finite ∨ ∃ l u, l < u ∧ Set.Ioo l u ⊆ D :=
  FiniteOrderBounds.finite_or_contains_interval (FullGammaControllers.finite_controller h00 B D hD)

theorem exists_isLeast_of_closed_upper (h00 : M ⊨ Axioms.ACVF00) (B : FullBaseAtomicity.Base (M := M))
    {D : Set (Values.Gamma (M := M))} (hD : FullGammaSyntax.Scalar B D)
    (hne : D.Nonempty) (hBound : BddBelow D)
    (hUpper : ∀ x ∈ D, ∀ y, x ≤ y → y ∈ D)
    (hClosed : ∀ r, (∀ t, r < t → t ∈ D) → r ∈ D) : ∃ r, IsLeast D r :=
  FiniteOrderBounds.exists_isLeast_of_closed_upper hne hBound
    (FullGammaControllers.finite_controller h00 B D hD) hUpper hClosed

end IntegrationInACVF.Section3ACVF.FullGammaBounds
