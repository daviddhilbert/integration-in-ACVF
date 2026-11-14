import Integration7.BalancedTranslationProductVolumeComparison
import Integration7.TwoOrderProductCoordinateDensities
import Integration7.NativeBalancedProductVolumeComparisonWithoutField
import Integration7.NativeBalancedTranslations
import Integration7.GammaRelativeTranslations

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

theorem balanced_translation_normalized_volume_comparison {κ : Cardinal}
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
    (η : RV (M := M)) (hη : η.val ∈ S) (hη0 : η ≠ 0) :
    let X := relativeTranslationImage Z 0 K.horizontal
    let Y := relativeTranslationImage Z 1 K.vertical
    ∃ F : TwoOrderProductPreparations X Y (nativeVFProjectionDomain Z 0) (nativeVFProjectionDomain Z 1)
      r t z hz P,
    ∃ i : RVVolumeIso (F.headNormalizedVolumeObject hκ.le hs hsmall hc hrS η hη hη0)
      (F.tailNormalizedVolumeObject hκ.le hs hsmall hc htS η hη hη0), i.GammaDefinable P := by
  intro X Y
  obtain ⟨F,i,hi⟩ := balanced_translation_product_volume_comparison hκ hs hsmall h00 γ hγ hγ1 hPS hc
    Z hZ ε r t h hf hfΓ hr hrS htS hr0 ht0 K hKX hKY z hz hzΓ η hη hη0
  exact ⟨F,F.normalized_volume_comparison hκ.le hs hsmall hc hPS hrS htS η hη hη0 i hi⟩

end IntegrationInACVF.Section7
