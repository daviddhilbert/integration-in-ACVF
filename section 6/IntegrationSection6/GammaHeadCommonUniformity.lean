import IntegrationSection6.GammaHeadPointwiseComparison
import IntegrationSection6.GammaHeadFibreSliceMaps
import IntegrationSection6.GammaUnaryActualLiftUniformity
import IntegrationSection6.GammaSwappedCommonBlowups

/-! A single head preparation on each side preserves fibrewise Isp, with
its new RV head coordinate added to the selected volume. This is the
induction step on families in Lemma6.14. -/
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

theorem gamma_head_common_uniformity {κ : Cardinal} (hκ : Cardinal.aleph0 < κ)
    (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (hreal : Cardinal.mk B.real < κ) (hgamma : Cardinal.mk B.gamma < κ)
    (δ : Values.Gamma (M := M)) (hδ : δ ∈ B.gamma) (hδ1 : 1 < δ)
    (U : DefSet (M := M) S (n+1) a) (V : DefSet (M := M) S (n+1) b)
    (hU : GammaSetDefinable B (carrier U)) (hV : GammaSetDefinable B (carrier V))
    (ρ : Fin k → Fin a) (τ : Fin k → Fin b)
    (hfinU : ∀ (x : Fin (n+1) → VF (M := M)) (t : Fin k → RV (M := M)),
      {r : Fin a → RV (M := M) | (x,r) ∈ carrier U ∧ r ∘ ρ = t}.Finite)
    (hfinV : ∀ (x : Fin (n+1) → VF (M := M)) (t : Fin k → RV (M := M)),
      {r : Fin b → RV (M := M) | (x,r) ∈ carrier V ∧ r ∘ τ = t}.Finite)
    (hCommon : ∀ x : Fin (n+1) → VF (M := M),
      ∀ P : SelectedLabelFibrePresentation B U ρ x, ∀ Q : SelectedLabelFibrePresentation B V τ x,
      GammaIsp hκ.le hs h00 (small_union_range hκ.le B.real hreal (fun j => (x j).val)) P.toGamma Q.toGamma)
    (T : HeadPreparation U) (E : HeadPreparation V)
    (hT : GammaGraphDefinable B (pointMapGraph T.map)) (hE : GammaGraphDefinable B (pointMapGraph E.map))
    (hTarget : GammaSetDefinable B (carrier T.target)) (hETarget : GammaSetDefinable B (carrier E.target))
    (x : Fin n → VF (M := M))
    (P : SelectedLabelFibrePresentation B T.contractedSet (headVolumeIndex T ρ) x)
    (Q : SelectedLabelFibrePresentation B E.contractedSet (headVolumeIndex E τ) x) :
    GammaIsp hκ.le hs h00 (small_union_range hκ.le B.real hreal (fun j => (x j).val)) P.toGamma Q.toGamma := by
  let C : Base (M := M) := ⟨B.real ∪ Set.range (fun j => (x j).val),B.gamma⟩
  have h := gamma_unary_actual_lift_uniformity (B := C) hκ hs h00
    (small_union_range hκ.le B.real hreal (fun j => (x j).val)) hgamma δ hδ hδ1
    (coordinateFibre U 0 (headFrozenTuple x)) (coordinateFibre V 0 (headFrozenTuple x))
    (gamma_head_fibre U hU x) (gamma_head_fibre V hV x) ρ τ
    (headFibre_selected_finite U ρ hfinU x) (headFibre_selected_finite V τ hfinV x)
    (fun z LP LQ => gamma_head_pointwise_comparison hκ.le hs h00 hreal U V ρ τ hCommon x z LP LQ)
    (gammaSwapVolumeBlocks P.toGamma) (gammaSwapVolumeBlocks Q.toGamma)
    (fun t LP => ⟨gammaHeadFibreSliceLiftIso T hT hTarget ρ x P t LP⟩)
    (fun t LQ => ⟨gammaHeadFibreSliceLiftIso E hE hETarget τ x Q t LQ⟩)
  exact GammaIsp.of_swapVolumeBlocks h

end IntegrationInACVF.Section6
