import IntegrationSection6.GammaSelectedLabelFibrePresentations
import IntegrationSection6.GammaPresentationBaseEquality

/-! Actual pure-RV sets with a selected-coordinate volume have finite
presentations over the unchanged mathematical base. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
namespace IntegrationInACVF.Section6
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {S : Set M} {a k : ℕ}

theorem emptyVFParameterBase (B : Base (M := M)) :
    (⟨B.real ∪ Set.range (fun j : Fin 0 => ((Fin.elim0 j : VF (M := M))).val),B.gamma⟩ : Base (M := M)) = B := by
  have he : B.real ∪ Set.range (fun j : Fin 0 => ((Fin.elim0 j : VF (M := M))).val) = B.real := by
    simp
  cases B
  congr 1

abbrev GammaSelectedRVPresentation (B : Base (M := M)) (U : DefSet (M := M) S 0 a) (ρ : Fin k → Fin a) :=
  GammaFiniteGraphPresentation B a k {r | (Fin.elim0,r) ∈ carrier U}
    (fun r y => (Fin.elim0,r) ∈ carrier U ∧ r ∘ ρ = y)

theorem gammaSelectedRVPresentation_exists (U : DefSet (M := M) S 0 a)
    (hU : GammaSetDefinable B (carrier U)) (ρ : Fin k → Fin a)
    (hfin : ∀ t : Fin k → RV (M := M),
      {r : Fin a → RV (M := M) | (Fin.elim0,r) ∈ carrier U ∧ r ∘ ρ = t}.Finite) :
    Nonempty (GammaSelectedRVPresentation B U ρ) := by
  obtain ⟨P⟩ := selectedLabelFibrePresentation_exists U hU ρ (by
    intro x t
    have hx : x = Fin.elim0 := Subsingleton.elim _ _
    subst x
    exact hfin t) Fin.elim0
  exact ⟨P.rebase (emptyVFParameterBase B)⟩

theorem gamma_pure_rv_pointwise_comparison {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00) (hreal : Cardinal.mk B.real < κ)
    {b : ℕ} (U : DefSet (M := M) S 0 a) (V : DefSet (M := M) S 0 b)
    (ρ : Fin k → Fin a) (τ : Fin k → Fin b)
    (hCommon : ∀ x : Fin 0 → VF (M := M),
      ∀ P : SelectedLabelFibrePresentation B U ρ x, ∀ Q : SelectedLabelFibrePresentation B V τ x,
      FiniteRV.GammaIsp hκ hs h00 (small_union_range hκ B.real hreal (fun j => (x j).val)) P.toGamma Q.toGamma)
    (P : GammaSelectedRVPresentation B U ρ) (Q : GammaSelectedRVPresentation B V τ) :
    FiniteRV.GammaIsp hκ hs h00 hreal P.toGamma Q.toGamma := by
  exact (gammaIsp_rebase_iff hκ hs h00 hreal
    (small_union_range hκ B.real hreal (fun j : Fin 0 => ((Fin.elim0 j : VF (M := M))).val))
    (emptyVFParameterBase B).symm P Q).mpr
      (hCommon Fin.elim0 (P.rebase (emptyVFParameterBase B).symm) (Q.rebase (emptyVFParameterBase B).symm))

end IntegrationInACVF.Section6
