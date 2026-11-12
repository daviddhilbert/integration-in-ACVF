import IntegrationSection6.GammaPermutedHeadSliceMaps
import IntegrationSection6.HeadTailFibreGeometry
import IntegrationSection6.GammaUnarySliceUniformityWithoutField
import IntegrationSection6.GammaSwappedCommonBlowups

/-! After a common first coordinate, reordering the frozen tail changes
head-contracted selected-volume fibres only by Isp. This uses the unary
lift comparison, with the full frozen parameter base retained. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5 SpecialTransformations.Section7
open IntegrationInACVF.Section5
namespace IntegrationInACVF.Section6
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {S : Set M} {n a k : ℕ}
open FiniteRV

theorem gamma_head_permutation_uniformity {κ : Cardinal} (hκ : Cardinal.aleph0 < κ)
    (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (hreal : Cardinal.mk B.real < κ) (hgamma : Cardinal.mk B.gamma < κ)
    (δ : Values.Gamma (M := M)) (hδ : δ ∈ B.gamma) (hδ1 : 1 < δ)
    {U V : DefSet (M := M) S (n+1) a} (T : HeadPreparation U) (E : HeadPreparation V)
    (hT : GammaGraphDefinable B (pointMapGraph T.map)) (hE : GammaGraphDefinable B (pointMapGraph E.map))
    (hTarget : GammaSetDefinable B (carrier T.target)) (hETarget : GammaSetDefinable B (carrier E.target))
    (ρ : Fin k → Fin a) (τ : Equiv.Perm (Fin n))
    (hSource : ∀ x : Fin n → VF (M := M),
      carrier (coordinateFibre V 0 (headFrozenTuple x)) =
        carrier (coordinateFibre U 0 (headFrozenTuple (x ∘ τ.symm))))
    (x : Fin n → VF (M := M))
    (P : SelectedLabelFibrePresentation B (vfPermutationImage T.contractedSet τ) (headVolumeIndex T ρ) x)
    (Q : SelectedLabelFibrePresentation B E.contractedSet (headVolumeIndex E ρ) x) :
    GammaIsp hκ.le hs h00 (small_union_range hκ.le B.real hreal (fun j => (x j).val)) P.toGamma Q.toGamma := by
  have H : GammaIsp hκ.le hs h00 (small_union_range hκ.le B.real hreal (fun j => (x j).val))
      (gammaSwapVolumeBlocks P.toGamma) (gammaSwapVolumeBlocks Q.toGamma) := by
    apply gamma_volume_slice_unary_lift_uniformity_uncountable
      (B := ⟨B.real ∪ Set.range (fun j => (x j).val),B.gamma⟩)
      hκ hs h00 (small_union_range hκ.le B.real hreal (fun j => (x j).val)) hgamma δ hδ hδ1
    intro t LP LQ
    let f := gammaPermutedHeadFibreSliceLiftIso T hT hTarget ρ τ x P t LP
    let g := gammaHeadFibreSliceLiftIso E hE hETarget ρ x Q t LQ
    let g' := g.congr (congrArg (fun D : Set (Point (M := M) 1 a) => D ∩ {q | q.2 ∘ ρ = t}) (hSource x)) rfl
    exact ⟨(f.symm (gammaLogicInput _)).trans (gammaLogicInput _) g'⟩
  exact GammaIsp.of_swapVolumeBlocks H

end IntegrationInACVF.Section6
