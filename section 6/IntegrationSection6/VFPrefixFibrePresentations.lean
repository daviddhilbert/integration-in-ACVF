import IntegrationSection6.VFPrefixProgramRestriction
import IntegrationSection6.GammaSelectedLabelFibrePresentations
import IntegrationSection6.GammaSelectedRVPresentations

/-! Actual RV fibres of a partial contraction are the finite presentations
of the frozen-prefix ordered contraction, with the same labels and volume. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
open IntegrationInACVF.Section5
namespace IntegrationInACVF.Section6
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {S : Set M} {n p a l k : ℕ}

theorem vfPrefixTuple_zero (x : Fin n → VF (M := M)) (y : Fin 0 → VF (M := M)) :
    vfPrefixTuple x y = x := by
  funext j
  simp [vfPrefixTuple]

theorem vfPrefixFibre_selected_finite (U : DefSet (M := M) S (n+p) a)
    (x : Fin n → VF (M := M)) (ρ : Fin k → Fin a)
    (hfin : ∀ (z : Fin (n+p) → VF (M := M)) (t : Fin k → RV (M := M)),
      {r : Fin a → RV (M := M) | (z,r) ∈ carrier U ∧ r ∘ ρ = t}.Finite) :
    ∀ (y : Fin p → VF (M := M)) (t : Fin k → RV (M := M)),
      {r : Fin a → RV (M := M) | (y,r) ∈ carrier (vfPrefixFibre U x) ∧ r ∘ ρ = t}.Finite :=
  fun y t => hfin (vfPrefixTuple x y) t

def prefixPartialPresentation {U : DefSet (M := M) S (n+p) a} {V : DefSet (M := M) S n l}
    (T : PartialContractionProgram S n (n := p) U V) (ρ : Fin k → Fin a)
    (x : Fin n → VF (M := M))
    (P : SelectedLabelFibrePresentation B V (partialSelectedIndex T ρ) x) :
    GammaSelectedRVPresentation ⟨B.real ∪ Set.range (fun j => (x j).val),B.gamma⟩
      (vfPrefixFibre (p := 0) V x) (orderedSelectedIndex (restrictPartialToPrefix T x) ρ) := by
  have hD : {r : Fin l → RV (M := M) | (x,r) ∈ carrier V} =
      {r | (Fin.elim0,r) ∈ carrier (vfPrefixFibre (p := 0) V x)} := by
    ext r
    change ((x,r) ∈ carrier V) ↔ ((vfPrefixTuple x Fin.elim0,r) ∈ carrier V)
    rw [vfPrefixTuple_zero]
  exact P.congrFormula hD (fun r y => and_congr (Set.ext_iff.mp hD r)
    (Iff.of_eq (congrArg (fun θ => r ∘ θ = y) (restrictPartialToPrefix_selectedIndex T x ρ).symm)))

theorem prefixPartialPresentation_toGamma {U : DefSet (M := M) S (n+p) a} {V : DefSet (M := M) S n l}
    (T : PartialContractionProgram S n (n := p) U V) (ρ : Fin k → Fin a)
    (x : Fin n → VF (M := M)) (P : SelectedLabelFibrePresentation B V (partialSelectedIndex T ρ) x) :
    (prefixPartialPresentation T ρ x P).toGamma = P.toGamma := by
  simp only [prefixPartialPresentation,GammaFiniteGraphPresentation.congrFormula_toGamma]

end IntegrationInACVF.Section6
