import Integration7.GammaIndexedVolumeBlowups
import Integration7.GammaVolumeBlowupEquivalence

/-! Uniform finite formula chains realize as actual original-Gamma
geometric chains. Auxiliary exception witnesses affect no geometric chart,
center base or exact chain length. -/

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
variable {B : Base (M := M)} {p a b d k r : ℕ}
variable {T : Set (Fin p → RV (M := M))}
variable {R : (Fin p → RV (M := M)) → (Fin d → RV (M := M)) → Prop}
variable {F : GammaRVVolumeSchema B p a k (fun _ => .rv)}
variable {G : GammaRVVolumeSchema B p b k (fun _ => .rv)}

set_option maxHeartbeats 1600000 in
theorem GammaVolumeChainSchema.indexedRealizeGamma {a b r : ℕ}
    {F : GammaRVVolumeSchema B p a k (fun _ => .rv)}
    {G : GammaRVVolumeSchema B p b k (fun _ => .rv)}
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (H : GammaVolumeChainSchema F G r)
    (BP : GammaFiniteGraphPresentation B p d T R) (hvalid : ∀ t ∈ T, H.valid (rvValues t))
    (P : F.IndexedPresentation BP) (Q : G.IndexedPresentation BP)
    (hP : P.finite.codes ⊆ (C.base : Set M)) (hQ : Q.finite.codes ⊆ (C.base : Set M))
    (hBP : BP.codes ⊆ (C.base : Set M)) (hB : B.real ⊆ (C.base : Set M)) :
    ∃ (D : BaseContext M) (hCD : (C.base : Set M) ⊆ (D.base : Set M))
      (W : GammaVolumeObjects B (D.base : Set M) (d+k)),
      GammaIteratedVolumeBlowup B (D.base : Set M) (d+k) r
        ⟨(P.inContext hc C hP).toObject.extend hCD,(P.gamma_object hc C hP).extend hCD⟩ W ∧
        ∃ e : RVVolumeIso W.val ((Q.inContext hc C hQ).toObject.extend hCD), e.GammaDefinable B := by
  cases H with
  | iso chart =>
    obtain ⟨D,hCD,e,he⟩ := chart.indexedRealizeBetweenGamma hc C F G BP
      (fun t ht => (hvalid t ht).1) (fun t ht => (hvalid t ht).2.1)
      (fun t ht => (hvalid t ht).2.2) P Q hP hQ hBP hB
    exact ⟨D,hCD,⟨(P.inContext hc C hP).toObject.extend hCD,(P.gamma_object hc C hP).extend hCD⟩,.refl _,e,he⟩
  | step W head tail =>
    let WP := W.indexedVolumePresentation BP (fun t ht => (hvalid t ht).1)
    obtain ⟨D,hCD,hWP⟩ := WP.exists_containingContext C hB
    obtain ⟨D₁,hDD₁,b,hb⟩ := head.indexedRealizeGamma hc D BP (fun t ht => (hvalid t ht).2.1)
      P WP (hP.trans hCD) hWP (hBP.trans hCD) (hB.trans hCD)
    obtain ⟨D₂,hD₁D₂,Y,hY,eY,heY⟩ := GammaVolumeChainSchema.indexedRealizeGamma hc D₁ tail BP
      (fun t ht => (hvalid t ht).2.2) WP Q (hWP.trans hDD₁) (hQ.trans (hCD.trans hDD₁))
      (hBP.trans (hCD.trans hDD₁)) (hB.trans (hCD.trans hDD₁))
    let Vg : GammaVolumeObjects B (D₂.base : Set M) (d+k) :=
      ⟨(WP.inContext hc D₁ (hWP.trans hDD₁)).toObject.extend hD₁D₂,
        (WP.gamma_object hc D₁ (hWP.trans hDD₁)).extend hD₁D₂⟩
    exact ⟨D₂,hCD.trans (hDD₁.trans hD₁D₂),Y,.step (V := Vg) ⟨b.extend hD₁D₂,hb.extend hD₁D₂⟩ hY,eY,heY⟩
termination_by r

set_option maxHeartbeats 2400000 in
theorem GammaVolumeCommonSchema.indexedRealizeGamma
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (H : GammaVolumeCommonSchema F G)
    (BP : GammaFiniteGraphPresentation B p d T R) (hvalid : ∀ t ∈ T, H.valid (rvValues t))
    (P : F.IndexedPresentation BP) (Q : G.IndexedPresentation BP)
    (hP : P.finite.codes ⊆ (C.base : Set M)) (hQ : Q.finite.codes ⊆ (C.base : Set M))
    (hBP : BP.codes ⊆ (C.base : Set M)) (hB : B.real ⊆ (C.base : Set M)) :
    ∃ (D : BaseContext M) (hCD : (C.base : Set M) ⊆ (D.base : Set M)),
      GammaVolumeBlowupEquivalent B (D.base : Set M) (d+k)
        ⟨(P.inContext hc C hP).toObject.extend hCD,(P.gamma_object hc C hP).extend hCD⟩
        ⟨(Q.inContext hc C hQ).toObject.extend hCD,(Q.gamma_object hc C hQ).extend hCD⟩ := by
  let LP := H.leftObject.indexedVolumePresentation BP (fun t ht => (hvalid t ht).2.2.1)
  let RP := H.rightObject.indexedVolumePresentation BP (fun t ht => (hvalid t ht).2.2.2.1)
  obtain ⟨D₀,hCD₀,hLP₀⟩ := LP.exists_containingContext C hB
  obtain ⟨D,hD₀D,hRP⟩ := RP.exists_containingContext D₀ (hB.trans hCD₀)
  let hCD := hCD₀.trans hD₀D
  let hLP := hLP₀.trans hD₀D
  obtain ⟨D₁,hDD₁,L,hL,eL,heL⟩ := H.leftChain.indexedRealizeGamma hc D BP
    (fun t ht => (hvalid t ht).2.2.2.2.1) P LP (hP.trans hCD) hLP (hBP.trans hCD) (hB.trans hCD)
  obtain ⟨D₂,hD₁D₂,R,hR,eR,heR⟩ := H.rightChain.indexedRealizeGamma hc D₁ BP
    (fun t ht => (hvalid t ht).2.2.2.2.2.1) Q RP (hQ.trans (hCD.trans hDD₁)) (hRP.trans hDD₁)
    (hBP.trans (hCD.trans hDD₁)) (hB.trans (hCD.trans hDD₁))
  let hDD₂ := hDD₁.trans hD₁D₂
  obtain ⟨D₃,hD₂D₃,e,he⟩ := H.comparison.indexedRealizeBetweenGamma hc D₂ H.leftObject H.rightObject BP
    (fun t ht => (hvalid t ht).2.2.2.2.2.2.1)
    (fun t ht => (hvalid t ht).2.2.2.2.2.2.2.1)
    (fun t ht => (hvalid t ht).2.2.2.2.2.2.2.2) LP RP (hLP.trans hDD₂) (hRP.trans hDD₂)
    (hBP.trans (hCD.trans hDD₂)) (hB.trans (hCD.trans hDD₂))
  let c := (((eL.extend hD₁D₂).extend hD₂D₃).trans hc D₃ e).trans hc D₃ ((eR.extend hD₂D₃).symm hc D₃)
  have hcΓ : c.GammaDefinable B := (((heL.extend hD₁D₂).extend hD₂D₃).trans hc D₃ B he).trans hc D₃ B
    ((heR.extend hD₂D₃).symm hc D₃ B)
  exact ⟨D₃,hCD.trans (hDD₂.trans hD₂D₃),H.leftLength,H.rightLength,
    (L.extend hD₁D₂).extend hD₂D₃,R.extend hD₂D₃,
    (hL.extend hD₁D₂).extend hD₂D₃,hR.extend hD₂D₃,c,hcΓ⟩

end IntegrationInACVF.Section7
