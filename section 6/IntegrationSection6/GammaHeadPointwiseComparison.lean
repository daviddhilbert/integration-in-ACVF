import IntegrationSection6.GammaHeadFibreParameters
import IntegrationSection6.FiniteGammaEquivalence

/-! The original pointwise hypothesis specializes to unary coordinate
fibres over exactly the frozen VF parameter base. -/
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
open FiniteRV

theorem gamma_head_pointwise_comparison {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00) (hreal : Cardinal.mk B.real < κ)
    (U : DefSet (M := M) S (n+1) a) (V : DefSet (M := M) S (n+1) b)
    (ρ : Fin k → Fin a) (τ : Fin k → Fin b)
    (hCommon : ∀ x : Fin (n+1) → VF (M := M),
      ∀ P : SelectedLabelFibrePresentation B U ρ x, ∀ Q : SelectedLabelFibrePresentation B V τ x,
      GammaIsp hκ hs h00 (small_union_range hκ B.real hreal (fun j => (x j).val)) P.toGamma Q.toGamma)
    (x : Fin n → VF (M := M)) (z : Fin 1 → VF (M := M))
    (P : SelectedLabelFibrePresentation ⟨B.real ∪ Set.range (fun j => (x j).val),B.gamma⟩
      (coordinateFibre U 0 (headFrozenTuple x)) ρ z)
    (Q : SelectedLabelFibrePresentation ⟨B.real ∪ Set.range (fun j => (x j).val),B.gamma⟩
      (coordinateFibre V 0 (headFrozenTuple x)) τ z) :
    GammaIsp hκ hs h00
      (small_union_range hκ (B.real ∪ Set.range (fun j => (x j).val))
        (small_union_range hκ B.real hreal (fun j => (x j).val)) (fun j => (z j).val)) P.toGamma Q.toGamma := by
  have h := hCommon (Fin.cons (z 0) x) (headFibrePresentation U ρ x z P) (headFibrePresentation V τ x z Q)
  unfold headFibrePresentation at h
  dsimp only at h
  have h' := (gammaIsp_rebase_iff hκ hs h00
    (small_union_range hκ (B.real ∪ Set.range (fun j => (x j).val))
      (small_union_range hκ B.real hreal (fun j => (x j).val)) (fun j => (z j).val))
    (small_union_range hκ B.real hreal (fun j : Fin (n+1) => ((Fin.cons (z 0) x : Fin (n+1) → VF (M := M)) j).val))
    (headVFParameterBase (B := B) x z) _ _).mpr h
  simpa only [GammaFiniteGraphPresentation.congrFormula_toGamma] using h'

end IntegrationInACVF.Section6
