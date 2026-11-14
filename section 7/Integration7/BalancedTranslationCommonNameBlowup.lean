import Integration7.TwoOrderProductCommonNameVolumes
import Integration7.BalancedTranslationNormalizedVolumeComparison
import Integration7.TwoOrderProductNormalizedGammaObjects
import Integration7.GammaVolumeBlowupEquivalence
import Integration7.BalancedTranslationProductVolumeComparison
import Integration7.TwoOrderProductCoordinateDensities
import Integration7.NativeBalancedProductVolumeComparisonWithoutField
import Integration7.NativeBalancedTranslations
import Integration7.GammaRelativeTranslations

/-! The actual horizontal and vertical translations of a balanced
native cell supply the opposite-order product comparison in a prescribed genuine context. Their centre
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

theorem balanced_translation_common_blowup_in_context
    (C : BaseContext M) (hSC : S ⊆ (C.base : Set M))
    (hNames : commonRealNames P ⊆ (C.base : Set M)) (γ : Values.Gamma (M := M)) (hγ : γ ∈ P.gamma) (hγ1 : 1 < γ)
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
    let hsmall : Cardinal.mk P.real < C.κ :=
      (Cardinal.mk_le_mk_of_subset (hPS.trans hSC)).trans_lt C.small
    ∃ F : TwoOrderProductPreparations X Y (nativeVFProjectionDomain Z 0) (nativeVFProjectionDomain Z 1)
      r t z hz P,
    let G := F.present hSC hNames
    GammaVolumeBlowupEquivalent P (C.base : Set M) 1
      (G.headNormalizedGammaObject C.uncountable.le C.saturated hsmall hc (hPS.trans hSC)
        (hSC hrS) η (hSC hη) hη0 j hj)
      (G.tailNormalizedGammaObject C.uncountable.le C.saturated hsmall hc (hPS.trans hSC)
        (hSC htS) η (hSC hη) hη0 j hj) := by
  intro X Y hsmall
  obtain ⟨F,i,hi⟩ := balanced_translation_normalized_volume_comparison C.uncountable C.saturated hsmall
    C.model00 γ hγ hγ1 hPS hc Z hZ ε r t h hf hfΓ hr hrS htS hr0 ht0 K hKX hKY z hz hzΓ η hη hη0
  obtain ⟨e,he⟩ := F.normalized_volume_comparison_in_presentation C.uncountable.le C.saturated hsmall hc
    hSC hNames hrS htS η hη hη0 i hi
  let G := F.present hSC hNames
  exact ⟨F,0,0,G.headNormalizedGammaObject C.uncountable.le C.saturated hsmall hc (hPS.trans hSC)
    (hSC hrS) η (hSC hη) hη0 j hj,
    G.tailNormalizedGammaObject C.uncountable.le C.saturated hsmall hc (hPS.trans hSC)
      (hSC htS) η (hSC hη) hη0 j hj,.refl _,.refl _,e,he⟩

end IntegrationInACVF.Section7
