import Integration7.RectangleFamilyNormalizedOrderIsomorphisms
import Integration7.RetainedDensityContractionObjects
import Integration7.GammaCoordinateDensityEquivalences

/-! The constructed opposite-order contractions of a shared-label
rectangle family compare in the actual volume category, including an
arbitrary nonzero density retained from the original RV tuple. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section7
open SpecialTransformations.Section5
open IntegrationInACVF.Section5 IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7.IndependentRectangleFamilyPreparations
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {G : Base (M := M)} {m : ℕ}

theorem constructed_volume_comparison {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ) (hreal : Cardinal.mk G.real < κ)
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (hGC : G.real ⊆ (C.base : Set M))
    {H : DefSet (M := M) (C.base : Set M) 2 m} (hH : GammaSetDefinable G (carrier H))
    (hfin : ∀ x : Fin 2 → VF (M := M), {r : Fin m → RV (M := M) | (x,r) ∈ carrier H}.Finite)
    {hRect : RectangularRVFibres (carrier H)} (F : IndependentRectangleFamilyPreparations G H hRect)
    (δ : Fin m) (hδ : ∀ p : H, (p.val.2 δ).val ≠ iRVZero) :
    let U := retainedDensityContractionGammaObject hκ hs hreal hc C hGC H hH hfin δ hδ
      F.headContraction (F.head_contraction_gamma hH)
    let V := retainedDensityContractionGammaObject hκ hs hreal hc C hGC H hH hfin δ hδ
      F.tailContraction (F.tail_contraction_gamma hH)
    ∃ D : BaseContext M, ∃ hCD : (C.base : Set M) ⊆ (D.base : Set M),
      GammaVolumeBlowupEquivalent G (D.base : Set M) 1 (U.extend hCD) (V.extend hCD) := by
  intro U V
  obtain ⟨D,hCD,e,he⟩ := gamma_coordinate_density_equivalence_realize hc C
    (FiniteRV.gammaFiniteContraction hκ hs hreal hGC hH hfin F.headContraction (F.head_contraction_gamma hH))
    (FiniteRV.gammaFiniteContraction hκ hs hreal hGC hH hfin F.tailContraction (F.tail_contraction_gamma hH))
    (Set.Subset.refl _) (Set.Subset.refl _)
    (FiniteRV.contractionOldLabelIndex F.headContraction δ) (FiniteRV.contractionOldLabelIndex F.tailContraction δ)
    (normalized_contraction_retained_density_nonzero F.headContraction δ hδ)
    (normalized_contraction_retained_density_nonzero F.tailContraction δ hδ)
    (F.normalizedGammaOrderIso hκ hs hreal hc C hGC hH hfin)
    (F.normalized_gamma_order_coordinates hκ hs hreal hc C hGC hH hfin)
    (F.normalized_gamma_order_retained_labels hκ hs hreal hc C hGC hH hfin δ)
  exact ⟨D,hCD,GammaVolumeBlowupEquivalent.of_iso D G e he⟩

end IntegrationInACVF.Section7.IndependentRectangleFamilyPreparations
