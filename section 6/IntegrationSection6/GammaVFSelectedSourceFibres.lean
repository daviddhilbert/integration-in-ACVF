import IntegrationSection6.GammaVFSchemaSources
import IntegrationSection6.GammaSchemaFiniteRows

/-! Exact finite RV fibres of the mixed source when the family volume
is the chosen tuple of old RV labels. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
namespace IntegrationInACVF.Section6
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {p a k : ℕ}

theorem vfSchemaSource_selected_fibres (A : Set (Point (M := M) p 0))
    (F : GammaFiniteRVSchema B p a k) (ρ : Fin k → Fin a)
    (hF : ∀ b : A, F.finiteRow (rawVFParameter b.val))
    (hLabels : ∀ b : A, ∀ r y, F.rowVolume (rawVFParameter b.val) r y ↔
      r ∈ F.rowDomain (rawVFParameter b.val) ∧ r ∘ ρ = y) :
    ∀ (x : Fin p → VF (M := M)) (t : Fin k → RV (M := M)),
      {r : Fin a → RV (M := M) | (x,r) ∈ vfSchemaSource A F ∧ r ∘ ρ = t}.Finite := by
  intro x t
  by_cases hx : (x,Fin.elim0) ∈ A
  · apply ((hF ⟨(x,Fin.elim0),hx⟩).2.2 t).subset
    intro r hr
    exact (hLabels ⟨(x,Fin.elim0),hx⟩ r t).mpr ⟨hr.1.2,hr.2⟩
  · apply Set.finite_empty.subset
    intro r hr
    exact False.elim (hx hr.1.1)

end IntegrationInACVF.Section6
