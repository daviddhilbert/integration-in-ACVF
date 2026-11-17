module

public import Integration7.IndexedEssentialIndexRestrictions
public import Integration7.GammaEssentialIndexDomains
public import Integration7.GammaRVIndexedVolumeUniformity

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! Indexed common blowups require witnesses only where every base
volume coordinate is nonzero. Zero-coordinate indices have no essential
labels in the total object and are removed by actual Gamma charts. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4
open SpecialTransformations.Section5 (RV)
open IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {p a b d k : ℕ}

set_option maxHeartbeats 2400000 in
theorem gamma_indexed_volume_uniformity_on_essential_indices {κ : Cardinal}
    (hc : CanonicalStructure.IsCanonical (M := M))
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (hreal : Cardinal.mk B.real < κ) (hgamma : Cardinal.mk B.gamma < κ)
    (F : GammaRVVolumeSchema B p a k (fun _ => .rv))
    (G : GammaRVVolumeSchema B p b k (fun _ => .rv))
    {T : Set (Fin p → RV (M := M))}
    {R : (Fin p → RV (M := M)) → (Fin d → RV (M := M)) → Prop}
    (BP : GammaFiniteGraphPresentation B p d T R)
    (hF : ∀ t ∈ T, F.valid (rvValues t)) (hG : ∀ t ∈ T, G.valid (rvValues t))
    (hWitness : ∀ t ∈ T, (∀ i, (BP.totalVolume t i).val ≠ iRVZero) →
      ∃ H : GammaVolumeCommonSchema F G, H.valid (rvValues t))
    (C : BaseContext M) (P : F.IndexedPresentation BP) (Q : G.IndexedPresentation BP)
    (hP : P.finite.codes ⊆ (C.base : Set M)) (hQ : Q.finite.codes ⊆ (C.base : Set M))
    (hB : B.real ⊆ (C.base : Set M)) :
    ∃ (D : BaseContext M) (hCD : (C.base : Set M) ⊆ (D.base : Set M)),
      GammaVolumeBlowupEquivalent B (D.base : Set M) (d+k)
        ⟨(P.inContext hc C hP).toObject.extend hCD,(P.gamma_object hc C hP).extend hCD⟩
        ⟨(Q.inContext hc C hQ).toObject.extend hCD,(Q.gamma_object hc C hQ).extend hCD⟩ := by
  let E := essentialIndexDomain BP
  let BE := essentialIndexPresentation BP
  have hET : E ⊆ T := fun _ h => h.1
  have hFE : ∀ t ∈ E, F.valid (rvValues t) := fun t ht => hF t ht.1
  have hGE : ∀ t ∈ E, G.valid (rvValues t) := fun t ht => hG t ht.1
  let PE := F.indexedVolumePresentation BE hFE
  let QE := G.indexedVolumePresentation BE hGE
  obtain ⟨C₁,hCC₁,hBE₁⟩ := finiteVolumePresentationContainingContext C BE hB
  obtain ⟨C₂,hC₁C₂,hPE₂⟩ := PE.exists_containingContext C₁ (hB.trans hCC₁)
  obtain ⟨C₃,hC₂C₃,hQE₃⟩ := QE.exists_containingContext C₂ (hB.trans (hCC₁.trans hC₁C₂))
  let hCC₃ := hCC₁.trans (hC₁C₂.trans hC₂C₃)
  let hPE₃ := hPE₂.trans hC₂C₃
  let hBE₃ := hBE₁.trans (hC₁C₂.trans hC₂C₃)
  obtain ⟨D,hC₃D,hCommon⟩ := gamma_rv_indexed_volume_witness_gamma_uniformity
    hc hκ hs hreal hgamma F G BE hFE hGE (fun t ht => hWitness t ht.1 ht.2)
    C₃ PE QE hPE₃ hQE₃ hBE₃ (hB.trans hCC₃)
  let hCD := hCC₃.trans hC₃D
  obtain ⟨eP,heP⟩ := indexed_volume_essential_index_restriction_iso hc D F BP BE hET
    (essential_index_presentation_volume BP) (fun t ht hNZ => ⟨ht,hNZ⟩) hF
    P PE (hP.trans hCD) (hPE₃.trans hC₃D)
  obtain ⟨eQ,heQ⟩ := indexed_volume_essential_index_restriction_iso hc D G BP BE hET
    (essential_index_presentation_volume BP) (fun t ht hNZ => ⟨ht,hNZ⟩) hG
    Q QE (hQ.trans hCD) (hQE₃.trans hC₃D)
  refine ⟨D,hCD,GammaVolumeBlowupEquivalent.trans hc D B ?_ (hCommon.trans hc D B ?_)⟩
  · exact GammaVolumeBlowupEquivalent.of_iso D B (eP.symm hc D) (heP.symm hc D B)
  · exact GammaVolumeBlowupEquivalent.of_iso D B eQ heQ

end IntegrationInACVF.Section7
