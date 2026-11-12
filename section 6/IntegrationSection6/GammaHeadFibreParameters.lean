import IntegrationSection6.GammaHeadFibreCoordinates
import IntegrationSection6.GammaPresentationBaseEquality
import IntegrationSection6.GammaSelectedLabelFibrePresentations

/-! Exact parameter and selected-volume rows after freezing the VF tail. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.DefinableGeometry.Space.prod
  SpecialTransformations.Section4.realSpace SpecialTransformations.Milestone0.sortEval
  SpecialTransformations.Section4.vfSpace SpecialTransformations.Section4.rvSpace
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
open IntegrationInACVF.Section5
namespace IntegrationInACVF.Section6
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {S : Set M} {n m k : ℕ}

theorem headFibre_selected_finite (A : DefSet (M := M) S (n+1) m) (ρ : Fin k → Fin m)
    (hfin : ∀ (x : Fin (n+1) → VF (M := M)) (t : Fin k → RV (M := M)),
      {r : Fin m → RV (M := M) | (x,r) ∈ carrier A ∧ r ∘ ρ = t}.Finite)
    (x : Fin n → VF (M := M)) :
    ∀ (z : Fin 1 → VF (M := M)) (t : Fin k → RV (M := M)),
      {r : Fin m → RV (M := M) |
        (z,r) ∈ carrier (coordinateFibre A 0 (headFrozenTuple x)) ∧ r ∘ ρ = t}.Finite := by
  intro z t
  convert hfin (Fin.cons (z 0) x) t using 1
  ext r
  change (coordinateInsert 0 (headFrozenTuple x) (z,r) ∈ carrier A ∧ r ∘ ρ = t) ↔
    ((Fin.cons (z 0) x,r) ∈ carrier A ∧ r ∘ ρ = t)
  rw [coordinateInsert_head]
  rfl

theorem gamma_head_fibre (A : DefSet (M := M) S (n+1) m)
    (hA : GammaSetDefinable B (carrier A)) (x : Fin n → VF (M := M)) :
    GammaSetDefinable ⟨B.real ∪ Set.range (fun j => (x j).val),B.gamma⟩
      (carrier (coordinateFibre A 0 (headFrozenTuple x))) := by
  have h := gamma_coordinateFibre A hA 0 (headFrozenTuple x)
  rw [coordinateGammaBase_head] at h
  exact h

theorem headVFParameterBase (x : Fin n → VF (M := M)) (z : Fin 1 → VF (M := M)) :
    (⟨(B.real ∪ Set.range (fun j => (x j).val)) ∪ Set.range (fun j => (z j).val),B.gamma⟩ : Base (M := M)) =
      ⟨B.real ∪ Set.range (fun j : Fin (n+1) => ((Fin.cons (z 0) x : Fin (n+1) → VF (M := M)) j).val),B.gamma⟩ := by
  apply congrArg (fun R => (⟨R,B.gamma⟩ : Base (M := M)))
  ext c
  constructor
  · rintro ((hc | ⟨j,rfl⟩) | ⟨j,rfl⟩)
    · exact Or.inl hc
    · exact Or.inr ⟨j.succ,by simp⟩
    · have hj : j = 0 := Subsingleton.elim _ _
      subst j
      exact Or.inr ⟨0,by simp⟩
  · rintro (hc | ⟨j,rfl⟩)
    · exact Or.inl (Or.inl hc)
    · cases j using Fin.cases with
      | zero => exact Or.inr ⟨0,by simp⟩
      | succ j => exact Or.inl (Or.inr ⟨j,by simp⟩)

def headFibrePresentation (A : DefSet (M := M) S (n+1) m) (ρ : Fin k → Fin m)
    (x : Fin n → VF (M := M)) (z : Fin 1 → VF (M := M))
    (P : SelectedLabelFibrePresentation ⟨B.real ∪ Set.range (fun j => (x j).val),B.gamma⟩
      (coordinateFibre A 0 (headFrozenTuple x)) ρ z) :
    SelectedLabelFibrePresentation B A ρ (Fin.cons (z 0) x) := by
  let hD : {r | (z,r) ∈ carrier (coordinateFibre A 0 (headFrozenTuple x))} =
      {r | (Fin.cons (z 0) x,r) ∈ carrier A} := by
    ext r
    change (coordinateInsert 0 (headFrozenTuple x) (z,r) ∈ carrier A) ↔ _
    rw [coordinateInsert_head]
    rfl
  exact (P.congrFormula hD (fun r y => and_congr (Set.ext_iff.mp hD r) Iff.rfl)).rebase (headVFParameterBase x z)

end IntegrationInACVF.Section6
