import IntegrationSection6.GammaHeadFibreParameters
import IntegrationSection6.GammaNamedIsoRestrictions

/-! A relatively unary bijection restricts to a complete original-Gamma
bijection of the frozen coordinate fibres, retaining selected old labels. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
open IntegrationInACVF.Section5
namespace IntegrationInACVF.Section6
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {S : Set M} {n a b k : ℕ}
variable {U : DefSet (M := M) S (n+1) a} {V : DefSet (M := M) S (n+1) b}

def gammaRelativeHeadFibreIso (f : Map U V) (hf : Function.Bijective f)
    (hΓ : GammaGraphDefinable B (pointMapGraph f)) (hi : UnaryRelative f 0)
    (x : Fin n → VF (M := M)) :
    GammaIso ⟨B.real ∪ Set.range (fun j => (x j).val),B.gamma⟩
      (carrier (coordinateFibre U 0 (headFrozenTuple x))) (carrier (coordinateFibre V 0 (headFrozenTuple x))) where
  equiv := Equiv.ofBijective (coordinateFibreMap f 0 hi (headFrozenTuple x))
    (coordinateFibreMap_bijective f hf 0 hi _)
  graph := by
    have h := gamma_coordinateFibreMap f hΓ 0 hi (headFrozenTuple x)
    rw [coordinateGammaBase_head] at h
    exact h

theorem gammaRelativeHeadFibreIso_labels (f : Map U V) (hf : Function.Bijective f)
    (hΓ : GammaGraphDefinable B (pointMapGraph f)) (hi : UnaryRelative f 0)
    (ρ : Fin k → Fin a) (τ : Fin k → Fin b)
    (hLabels : ∀ u : U, (f u).val.2 ∘ τ = u.val.2 ∘ ρ)
    (x : Fin n → VF (M := M)) (u : coordinateFibre U 0 (headFrozenTuple x)) :
    ((gammaRelativeHeadFibreIso f hf hΓ hi x).equiv u).val.2 ∘ τ = u.val.2 ∘ ρ := by
  exact hLabels ⟨coordinateInsert 0 (headFrozenTuple x) u.val,u.property⟩

end IntegrationInACVF.Section6
