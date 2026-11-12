import IntegrationSection6.GammaSelectedLabelFamilies
import IntegrationSection6.GammaGraphFormulaCongruence
import IntegrationSection6.GammaSchemaFiniteRowPresentations

/-! Actual finite RV[k] fibre presentations with the selected-label volume,
and their exact identification with the uniform family schema rows. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
namespace IntegrationInACVF.Section6
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {R : Set M} {p a k : ℕ}

abbrev SelectedLabelFibrePresentation (B : Base (M := M)) (U : DefSet (M := M) R p a)
    (ρ : Fin k → Fin a) (x : Fin p → VF (M := M)) :=
  GammaFiniteGraphPresentation ⟨B.real ∪ Set.range (fun j => (x j).val),B.gamma⟩ a k
    {r | (x,r) ∈ carrier U} (fun r y => (x,r) ∈ carrier U ∧ r ∘ ρ = y)

def selectedLabelFibreOfSchema (U : DefSet (M := M) R p a)
    (hU : GammaSetDefinable B (carrier U)) (ρ : Fin k → Fin a) (x : Fin p → VF (M := M))
    (P : GammaFiniteGraphPresentation ⟨B.real ∪ Set.range (fun j => (x j).val),B.gamma⟩ a k
      ((gammaSelectedLabelSchema U hU ρ).rowDomain (fun j => (x j).val))
      ((gammaSelectedLabelSchema U hU ρ).rowVolume (fun j => (x j).val))) :
    SelectedLabelFibrePresentation B U ρ x :=
  P.congrFormula (gammaSelectedLabelSchema_domain U hU ρ x) (gammaSelectedLabelSchema_volume U hU ρ x)

theorem selectedLabelFibreOfSchema_toGamma (U : DefSet (M := M) R p a)
    (hU : GammaSetDefinable B (carrier U)) (ρ : Fin k → Fin a) (x : Fin p → VF (M := M))
    (P : GammaFiniteGraphPresentation ⟨B.real ∪ Set.range (fun j => (x j).val),B.gamma⟩ a k
      ((gammaSelectedLabelSchema U hU ρ).rowDomain (fun j => (x j).val))
      ((gammaSelectedLabelSchema U hU ρ).rowVolume (fun j => (x j).val))) :
    (selectedLabelFibreOfSchema U hU ρ x P).toGamma = P.toGamma :=
  P.congrFormula_toGamma _ _

theorem selectedLabelFibrePresentation_exists (U : DefSet (M := M) R p a)
    (hU : GammaSetDefinable B (carrier U)) (ρ : Fin k → Fin a)
    (hfin : ∀ (x : Fin p → VF (M := M)) (t : Fin k → RV (M := M)),
      {r : Fin a → RV (M := M) | (x,r) ∈ carrier U ∧ r ∘ ρ = t}.Finite)
    (x : Fin p → VF (M := M)) : Nonempty (SelectedLabelFibrePresentation B U ρ x) := by
  obtain ⟨P⟩ := (gammaSelectedLabelSchema U hU ρ).realize_finiteRow (fun j => (x j).val)
    (fun j => (x j).property) (gammaSelectedLabelSchema_finiteRows U hU ρ hfin x)
  exact ⟨selectedLabelFibreOfSchema U hU ρ x P⟩

end IntegrationInACVF.Section6
