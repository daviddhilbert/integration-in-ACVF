import IntegrationSection6.GammaIsoRestrictions
import IntegrationSection6.GammaNamedRVFibres

/-! An isomorphism preserving chosen old RV labels restricts over their
precisely named values, keeping its complete original-Gamma graph. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
namespace IntegrationInACVF.Section6
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {n m k l e : ℕ}

def gammaIsoNamedRVLabels
    {A : Set (Point (M := M) n m)} {D : Set (Point (M := M) k l)} (f : GammaIso B A D)
    (ρ : Fin e → Fin m) (τ : Fin e → Fin l)
    (hLabels : ∀ a : A, (f.equiv a).val.2 ∘ τ = a.val.2 ∘ ρ) (t : Fin e → RV (M := M)) :
    GammaIso ⟨B.real ∪ Set.range (fun j => (t j).val),B.gamma⟩
      (A ∩ {p | p.2 ∘ ρ = t}) (D ∩ {p | p.2 ∘ τ = t}) := by
  let Bt : Base (M := M) := ⟨B.real ∪ Set.range (fun j => (t j).val),B.gamma⟩
  let ft : GammaIso Bt A D := ⟨f.equiv,f.graph.mono Set.subset_union_left (Set.Subset.refl _)⟩
  have hAΓ : GammaSetDefinable Bt A := (ft.symm (gammaLogicInput Bt)).target_definable (gammaLogicInput Bt)
  have hAt := (gammaLogicInput Bt).inter hAΓ (gamma_named_rv_label_fibre ρ t)
  apply gammaIsoRestrict ft (fun _ h => h.1) (fun _ h => h.1) ?_ hAt
  intro a
  change (_ ∧ a.val.2 ∘ ρ = t) ↔ (_ ∧ (f.equiv a).val.2 ∘ τ = t)
  rw [hLabels a]
  exact ⟨fun h => ⟨(f.equiv a).property,h.2⟩,fun h => ⟨a.property,h.2⟩⟩

end IntegrationInACVF.Section6
