import IntegrationSection6.GammaRelativeHeadFibres
import IntegrationSection6.GammaHeadFibreSliceMaps
import IntegrationSection6.GammaUnarySliceUniformityWithoutField
import IntegrationSection6.GammaSwappedCommonBlowups

/-! Relatively unary bijections compare the actual RV[1+k] head fibres of
arbitrary head preparations. Only the frozen VF and selected RV tuples
become parameters in the unary lift comparison. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
open IntegrationInACVF.Section5
namespace IntegrationInACVF.Section6.FiniteRV
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {S : Set M} {n a b k : ℕ}
variable {U : DefSet (M := M) S (n+1) a} {V : DefSet (M := M) S (n+1) b}

theorem gamma_relative_head_comparison {κ : Cardinal} (hκ : Cardinal.aleph0 < κ)
    (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (hreal : Cardinal.mk B.real < κ) (hgamma : Cardinal.mk B.gamma < κ)
    (δ : Values.Gamma (M := M)) (hδ : δ ∈ B.gamma) (hδ1 : 1 < δ)
    (f : Map U V) (hf : Function.Bijective f) (hΓ : GammaGraphDefinable B (pointMapGraph f))
    (hi : UnaryRelative f 0) (ρ : Fin k → Fin a) (τ : Fin k → Fin b)
    (hLabels : ∀ u : U, (f u).val.2 ∘ τ = u.val.2 ∘ ρ)
    (T : HeadPreparation U) (E : HeadPreparation V)
    (hT : GammaGraphDefinable B (pointMapGraph T.map)) (hE : GammaGraphDefinable B (pointMapGraph E.map))
    (hTarget : GammaSetDefinable B (carrier T.target)) (hETarget : GammaSetDefinable B (carrier E.target))
    (x : Fin n → VF (M := M))
    (P : SelectedLabelFibrePresentation B T.contractedSet (headVolumeIndex T ρ) x)
    (Q : SelectedLabelFibrePresentation B E.contractedSet (headVolumeIndex E τ) x) :
    GammaIsp hκ.le hs h00 (small_union_range hκ.le B.real hreal (fun j => (x j).val)) P.toGamma Q.toGamma := by
  let C : Base (M := M) := ⟨B.real ∪ Set.range (fun j => (x j).val),B.gamma⟩
  have h : GammaIsp hκ.le hs h00 (small_union_range hκ.le B.real hreal (fun j => (x j).val))
      (gammaSwapVolumeBlocks P.toGamma) (gammaSwapVolumeBlocks Q.toGamma) := by
    apply gamma_volume_slice_unary_lift_uniformity_uncountable (B := C) hκ hs h00
      (small_union_range hκ.le B.real hreal (fun j => (x j).val)) hgamma δ hδ hδ1
    intro t LP LQ
    let c := gammaHeadFibreSliceLiftIso T hT hTarget ρ x P t LP
    let d := gammaHeadFibreSliceLiftIso E hE hETarget τ x Q t LQ
    let e := gammaRelativeHeadFibreIso f hf hΓ hi x
    let e' := gammaIsoNamedRVLabels e ρ τ (gammaRelativeHeadFibreIso_labels f hf hΓ hi ρ τ hLabels x) t
    exact ⟨((c.symm (gammaLogicInput _)).trans (gammaLogicInput _) e').trans (gammaLogicInput _) d⟩
  exact GammaIsp.of_swapVolumeBlocks h

end IntegrationInACVF.Section6.FiniteRV
