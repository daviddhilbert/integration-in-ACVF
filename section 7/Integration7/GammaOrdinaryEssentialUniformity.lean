module

public import Integration7.OrdinaryIndexedEssentialRestrictions
public import Integration7.GammaIndexedOrdinaryUnitComparisons
public import Integration7.IndexedVolumeFiniteWitnessGluing

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! Ordinary finite-row chart witnesses are needed only at nonzero
base-volume indices. Their actual unit-density total objects are then
original-Gamma volume isomorphic in a small containing context. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
open IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {p a b : ℕ}

set_option maxHeartbeats 2400000 in
theorem gamma_ordinary_indexed_uniformity_on_essential_indices {κ : Cardinal}
    (hc : CanonicalStructure.IsCanonical (M := M))
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (hreal : Cardinal.mk B.real < κ) (hgamma : Cardinal.mk B.gamma < κ)
    {T : Set (Fin p → RV (M := M))}
    {R : (Fin p → RV (M := M)) → (Fin 1 → RV (M := M)) → Prop}
    (BP : GammaFiniteGraphPresentation B p 1 T R)
    (F : GammaFiniteRVSchema B p a 0 (fun _ => .rv))
    (G : GammaFiniteRVSchema B p b 0 (fun _ => .rv))
    (hF : ∀ t ∈ T, F.valid (rvValues t)) (hG : ∀ t ∈ T, G.valid (rvValues t))
    (hWitness : ∀ t ∈ T, (∀ i, (BP.totalVolume t i).val ≠ iRVZero) →
      ∃ H : GammaRelationFormula B p a b (fun _ => .rv), (gammaFiniteRowChartSchema F G H).valid (rvValues t))
    (C : BaseContext M) (P : F.IndexedPresentation BP) (Q : G.IndexedPresentation BP)
    (hPC : P.codes ⊆ (C.base : Set M)) (hQC : Q.codes ⊆ (C.base : Set M))
    (hBC : B.real ⊆ (C.base : Set M)) :
    ∃ D : BaseContext M, ∃ hCD : (C.base : Set M) ⊆ (D.base : Set M),
    ∃ e : RVVolumeIso ((gammaUnitVolumeObject hc C P.toGamma hPC).extend hCD)
      ((gammaUnitVolumeObject hc C Q.toGamma hQC).extend hCD), e.GammaDefinable B := by
  let BE := essentialIndexPresentation BP
  let PE := F.indexedPresentation BE (fun t ht => hF t ht.1)
  let QE := G.indexedPresentation BE (fun t ht => hG t ht.1)
  obtain ⟨C₁,hCC₁,hPE₁⟩ := finiteVolumePresentationContainingContext C PE hBC
  obtain ⟨C₂,hC₁C₂,hQE₂⟩ := finiteVolumePresentationContainingContext C₁ QE (hBC.trans hCC₁)
  let hCC₂ := hCC₁.trans hC₁C₂
  let hPE₂ := hPE₁.trans hC₁C₂
  obtain ⟨D,hC₂D,e,he⟩ := gamma_indexed_ordinary_unit_volume_comparison hc C₂ hκ hs hreal hgamma
    BE F G (fun t ht => hWitness t ht.1 ht.2) PE QE hPE₂ hQE₂
  let hCD := hCC₂.trans hC₂D
  obtain ⟨eP,heP⟩ := ordinary_indexed_essential_restriction_iso hc D F BP BE (fun _ h => h.1)
    (essential_index_presentation_volume BP) (fun t ht hNZ => ⟨ht,hNZ⟩)
    P PE (hPC.trans hCD) (hPE₂.trans hC₂D)
  obtain ⟨eQ,heQ⟩ := ordinary_indexed_essential_restriction_iso hc D G BP BE (fun _ h => h.1)
    (essential_index_presentation_volume BP) (fun t ht hNZ => ⟨ht,hNZ⟩)
    Q QE (hQC.trans hCD) (hQE₂.trans hC₂D)
  exact ⟨D,hCD,((eP.symm hc D).trans hc D e).trans hc D eQ,
    ((heP.symm hc D B).trans hc D B he).trans hc D B heQ⟩

end IntegrationInACVF.Section7
