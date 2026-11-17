module

public import Integration7.BalancedTranslationNormalizedVolumeComparison
public import Integration7.TwoOrderProductNormalizedGammaObjects
public import Integration7.GammaVolumeBlowupEquivalence
public import Integration7.BalancedTranslationProductVolumeComparison
public import Integration7.TwoOrderProductCoordinateDensities
public import Integration7.NativeBalancedProductVolumeComparisonWithoutField
public import Integration7.NativeBalancedTranslations
public import Integration7.GammaRelativeTranslations

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! The actual horizontal and vertical translations of a balanced
native cell supply the opposite-order product comparison. Their centre
and positioning graphs retain the original Gamma base. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
open IntegrationInACVF.Section5
open IntegrationInACVF.Section4 IntegrationInACVF.Section4.Cells

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {P : Base (M := M)} {S : Set M} {d : ℕ}

theorem balanced_translation_constructed_common_blowup {κ : Cardinal}
    (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ) (hsmall : Cardinal.mk P.real < κ)
    (h00 : M ⊨ Axioms.ACVF00) (γ : Values.Gamma (M := M)) (hγ : γ ∈ P.gamma) (hγ1 : 1 < γ)
    (hPS : P.real ⊆ S) (hc : CanonicalStructure.IsCanonical (M := M))
    (Z : DefSet (M := M) S 2 0) (hZ : GammaSetDefinable P (carrier Z))
    (ε : VF (M := M) → VF (M := M)) (r t : RV (M := M))
    (h : IsBalanced (nativeVFPairDomain Z) ε r t)
    (hf : DefinableOver S (fun _ : Fin 2 => .vf) (positionCodes (first (nativeVFPairDomain Z)) ε))
    (hfΓ : DefinableOverBase P (fun _ : Fin 2 => .vf) (positionCodes (first (nativeVFPairDomain Z)) ε))
    (hr : r ≠ rv (0 : VF (M := M))) (hrS : r.val ∈ S) (htS : t.val ∈ S)
    (hr0 : r.val ≠ iRVZero) (ht0 : t.val ≠ iRVZero)
    (K : BalancedTranslationCentres Z h.2.2.1)
    (hKX : GammaScalarGraphDefinable P (fun p a => ∃ q : Z, q.val = p ∧ (K.horizontal q).val 0 = a))
    (hKY : GammaScalarGraphDefinable P (fun p a => ∃ q : Z, q.val = p ∧ (K.vertical q).val 0 = a))
    (z : Fin d → RV (M := M)) (hz : ∀ j, (z j).val ∈ S)
    (hzΓ : DefinableOverBase P (fun _ : Fin d => .rv) {fun j => (z j).val})
    (η : RV (M := M)) (hη : η.val ∈ S) (hη0 : η ≠ 0) (j : Fin d) (hj : z j = η) :
    let X := relativeTranslationImage Z 0 K.horizontal
    let Y := relativeTranslationImage Z 1 K.vertical
    ∃ F : TwoOrderProductPreparations X Y (nativeVFProjectionDomain Z 0) (nativeVFProjectionDomain Z 1)
      r t z hz P,
    GammaVolumeBlowupEquivalent P F.codes 1
      (F.headNormalizedGammaObject hκ.le hs hsmall hc hPS hrS η hη hη0 j hj)
      (F.tailNormalizedGammaObject hκ.le hs hsmall hc hPS htS η hη hη0 j hj) := by
  intro X Y
  obtain ⟨F,i,hi⟩ := balanced_translation_normalized_volume_comparison hκ hs hsmall h00 γ hγ hγ1 hPS hc
    Z hZ ε r t h hf hfΓ hr hrS htS hr0 ht0 K hKX hKY z hz hzΓ η hη hη0
  exact ⟨F,0,0,F.headNormalizedGammaObject hκ.le hs hsmall hc hPS hrS η hη hη0 j hj,
    F.tailNormalizedGammaObject hκ.le hs hsmall hc hPS htS η hη hη0 j hj,.refl _,.refl _,i,hi⟩

end IntegrationInACVF.Section7
