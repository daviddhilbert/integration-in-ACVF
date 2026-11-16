import Integration7.HKIndexedEssentialRestrictions
import Integration7.HKIndexedWeightedVolumeComparisons
import Integration7.IndexedVolumeFiniteWitnessGluing

/-! Exact-density finite-row witnesses on essential indices suffice for
actual weighted total-volume isomorphisms on the original Gamma base. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
open IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7.HK
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {p a b : ℕ}

set_option maxHeartbeats 2400000 in
theorem weighted_indexed_uniformity_on_essential_indices {κ : Cardinal}
    (hc : CanonicalStructure.IsCanonical (M := M))
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (hreal : Cardinal.mk B.real < κ) (hgamma : Cardinal.mk B.gamma < κ)
    {T : Set (Fin p → RV (M := M))}
    {R : (Fin p → RV (M := M)) → (Fin 1 → RV (M := M)) → Prop}
    (BP : GammaFiniteGraphPresentation B p 1 T R)
    (F : GammaFiniteRVSchema B p a 0 (fun _ => .rv))
    (G : GammaFiniteRVSchema B p b 0 (fun _ => .rv))
    (hF : ∀ t ∈ T, F.valid (rvValues t)) (hG : ∀ t ∈ T, G.valid (rvValues t))
    (δ : Fin a) (ε : Fin b)
    (hWitness : ∀ t ∈ T, (∀ i, (BP.totalVolume t i).val ≠ iRVZero) →
      ∃ H : GammaRelationFormula B p a b (fun _ => .rv),
        H.val ⊆ densityLabelConstraint (fun _ => .rv) δ ε ∧
          (gammaFiniteRowChartSchema F G H).valid (rvValues t))
    (C : BaseContext M) (P : F.IndexedPresentation BP) (Q : G.IndexedPresentation BP)
    (hPC : P.codes ⊆ (C.base : Set M)) (hQC : Q.codes ⊆ (C.base : Set M))
    (hBC : B.real ⊆ (C.base : Set M))
    (hδ : ∀ u : P.domain, (u.val (Fin.natAdd p δ)).val ≠ iRVZero)
    (hε : ∀ u : Q.domain, (u.val (Fin.natAdd p ε)).val ≠ iRVZero) :
    ∃ D : BaseContext M, ∃ hCD : (C.base : Set M) ⊆ (D.base : Set M),
    ∃ e : RVVolumeIso ((gammaCoordinateDensityObject (e := 0) (k := 0) hc C P.toGamma hPC (Fin.natAdd p δ) hδ).extend hCD)
      ((gammaCoordinateDensityObject (e := 0) (k := 0) hc C Q.toGamma hQC (Fin.natAdd p ε) hε).extend hCD), e.GammaDefinable B := by
  let BE := essentialIndexPresentation BP
  let PE := F.indexedPresentation BE (fun t ht => hF t ht.1)
  let QE := G.indexedPresentation BE (fun t ht => hG t ht.1)
  have hδE : ∀ u : PE.domain, (u.val (Fin.natAdd p δ)).val ≠ iRVZero := by
    intro u
    have hu := PE.domain_eq.le u.property
    exact hδ ⟨u.val,P.domain_eq.ge ⟨hu.1.1,hu.2⟩⟩
  have hεE : ∀ u : QE.domain, (u.val (Fin.natAdd p ε)).val ≠ iRVZero := by
    intro u
    have hu := QE.domain_eq.le u.property
    exact hε ⟨u.val,Q.domain_eq.ge ⟨hu.1.1,hu.2⟩⟩
  obtain ⟨C₁,hCC₁,hPE₁⟩ := finiteVolumePresentationContainingContext C PE hBC
  obtain ⟨C₂,hC₁C₂,hQE₂⟩ := finiteVolumePresentationContainingContext C₁ QE (hBC.trans hCC₁)
  let hCC₂ := hCC₁.trans hC₁C₂
  let hPE₂ := hPE₁.trans hC₁C₂
  obtain ⟨D,hC₂D,e,he⟩ := indexed_weighted_volume_comparison hc C₂ hκ hs hreal hgamma
    BE F G δ ε (fun t ht => hWitness t ht.1 ht.2) PE QE hPE₂ hQE₂ hδE hεE
  let hCD := hCC₂.trans hC₂D
  obtain ⟨eP,heP⟩ := weighted_indexed_essential_restriction_iso hc D F BP BE (fun _ h => h.1)
    (essential_index_presentation_volume BP) (fun t ht hNZ => ⟨ht,hNZ⟩)
    P PE (hPC.trans hCD) (hPE₂.trans hC₂D) δ hδ hδE
  obtain ⟨eQ,heQ⟩ := weighted_indexed_essential_restriction_iso hc D G BP BE (fun _ h => h.1)
    (essential_index_presentation_volume BP) (fun t ht hNZ => ⟨ht,hNZ⟩)
    Q QE (hQC.trans hCD) (hQE₂.trans hC₂D) ε hε hεE
  exact ⟨D,hCD,((eP.symm hc D).trans hc D e).trans hc D eQ,
    ((heP.symm hc D B).trans hc D B he).trans hc D B heQ⟩

end IntegrationInACVF.Section7.HK
