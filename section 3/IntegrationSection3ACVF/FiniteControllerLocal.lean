import IntegrationSection3ACVF.GammaCosetGeometry
import Section4.CanonicalOrderController

/-! A locally constant subset above a Gamma threshold with a finite
order controller is constant on that tail. Finite controllers exclude
nonprincipal cuts; no completeness or Archimedean hypothesis is assumed. -/

open Set Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4

namespace IntegrationInACVF.Section3ACVF.FiniteControllerLocal

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

theorem constant_on_tail (D : Set (Values.Gamma (M := M))) (a : Values.Gamma (M := M))
    (hController : ∃ F, FiniteOrder.Controls F D)
    (hLocal : ∀ p, a < p → ∃ l u, l < p ∧ p < u ∧
      ∀ z, l < z → z < u → (z ∈ D ↔ p ∈ D)) :
    ∀ x y, a < x → a < y → (x ∈ D ↔ y ∈ D) := by
  letI : DecidableEq (Values.Gamma (M := M)) := Classical.decEq _
  obtain ⟨F,hF,hmin⟩ := FiniteOrder.exists_minimal_controller hController
  have hBelow : ∀ p ∈ F, p ≤ a := by
    intro p hp
    by_contra h
    obtain ⟨l,u,hl,hu,hLoc⟩ := hLocal p (lt_of_not_ge h)
    have hErase := FiniteOrder.erase_controls_of_local hF hl hu hLoc
    exact not_le_of_gt (Finset.card_erase_lt_of_mem hp) (hmin (F.erase p) hErase)
  intro x y hx hy
  apply hF x y
  intro p hp
  have hpx : p < x := lt_of_le_of_lt (hBelow p hp) hx
  have hpy : p < y := lt_of_le_of_lt (hBelow p hp) hy
  exact ⟨iff_of_false (not_lt_of_ge hpx.le) (not_lt_of_ge hpy.le),iff_of_true hpx hpy⟩

end IntegrationInACVF.Section3ACVF.FiniteControllerLocal
