import Integration7.BalancedTranslationCommonNameBlowup
import Integration7.FixedLabelTranslationCommonBlowups
import Integration7.TwoOrderProductContractionVolumeIdentifications
import Integration7.VolumeContextJoins

/-! The balanced two-dimensional cell case of Lemma7.7 for arbitrary
specified opposite-order contractions, with actual original-Gamma common
forward blowup chains and the retained nonzero density. -/
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
variable {P : Base (M := M)} {d : ℕ}

set_option maxHeartbeats 2000000 in
theorem balanced_cell_opposite_order_contraction_comparison
    (C : BaseContext M) (hgamma : Cardinal.mk P.gamma < C.κ) (γ : Values.Gamma (M := M)) (hγ : γ ∈ P.gamma) (hγ1 : 1 < γ)
    (hPS : P.real ⊆ (C.base : Set M))
    (hNames : commonRealNames P ⊆ (C.base : Set M))
    (hGeneric : ∀ {p : ℕ} (x : Fin p → VF (M := M)),
      AlgebraicIndependent (vfParameterField P.real) x →
      AlgebraicIndependent (vfParameterField (C.base : Set M)) x) (hc : CanonicalStructure.IsCanonical (M := M))
    (Z : DefSet (M := M) (C.base : Set M) 2 0) (hZ : GammaSetDefinable P (carrier Z))
    (ε : VF (M := M) → VF (M := M)) (r t : RV (M := M))
    (h : IsBalanced (nativeVFPairDomain Z) ε r t)
    (hf : DefinableOver (C.base : Set M) (fun _ : Fin 2 => .vf) (positionCodes (first (nativeVFPairDomain Z)) ε))
    (hfΓ : DefinableOverBase P (fun _ : Fin 2 => .vf) (positionCodes (first (nativeVFPairDomain Z)) ε))
    (hr : r ≠ rv (0 : VF (M := M))) (hrS : r.val ∈ (C.base : Set M)) (htS : t.val ∈ (C.base : Set M))
    (hr0 : r.val ≠ iRVZero) (ht0 : t.val ≠ iRVZero)
    (K : BalancedTranslationCentres Z h.2.2.1)
    (hKX : GammaScalarGraphDefinable P (fun p a => ∃ q : Z, q.val = p ∧ (K.horizontal q).val 0 = a))
    (hKY : GammaScalarGraphDefinable P (fun p a => ∃ q : Z, q.val = p ∧ (K.vertical q).val 0 = a))
    (z : Fin d → RV (M := M)) (hz : ∀ j, (z j).val ∈ (C.base : Set M))
    (hzΓ : DefinableOverBase P (fun _ : Fin d => .rv) {fun j => (z j).val})
    (η : RV (M := M)) (hη : η.val ∈ (C.base : Set M)) (hη0 : η ≠ 0) (j : Fin d) (hj : z j = η)
    (T : StandardContraction (fixedRVLabelDomain Z z hz) (Equiv.refl _))
    (E : StandardContraction (fixedRVLabelDomain Z z hz) (Equiv.swap 0 1))
    (hT : GammaProgramDefinable P T.program) (hE : GammaProgramDefinable P E.program) :
    let hsmall : Cardinal.mk P.real < C.κ := (Cardinal.mk_le_mk_of_subset hPS).trans_lt C.small
    let U := fixedLabelContractionGammaObject C.uncountable.le C.saturated hsmall hc C hPS Z hZ z hz hzΓ j η hj hη0 T hT
    let V := fixedLabelContractionGammaObject C.uncountable.le C.saturated hsmall hc C hPS Z hZ z hz hzΓ j η hj hη0 E hE
    ∃ (D : BaseContext M) (hCD : (C.base : Set M) ⊆ (D.base : Set M)),
      GammaVolumeBlowupEquivalent P (D.base : Set M) 1 (U.extend hCD) (V.extend hCD) := by
  intro hsmall U V
  let X := relativeTranslationImage Z 0 K.horizontal
  let Y := relativeTranslationImage Z 1 K.vertical
  have hX := gamma_relative_translation_image Z 0 K.horizontal hKX
  have hY := gamma_relative_translation_image Z 1 K.vertical hKY
  obtain ⟨F,i,hi⟩ := balanced_translation_normalized_volume_comparison C.uncountable C.saturated hsmall
    C.model00 γ hγ hγ1 hPS hc Z hZ ε r t h hf hfΓ hr hrS htS hr0 ht0 K hKX hKY z hz hzΓ η hη hη0
  let G := F.present (Set.Subset.refl _) hNames
  obtain ⟨g,hg⟩ := F.normalized_volume_comparison_in_presentation C.uncountable.le C.saturated hsmall hc
    (Set.Subset.refl _) hNames hrS htS η hη hη0 i hi
  have hHead := G.head_contraction_gamma hX hzΓ
  have hTail := G.tail_contraction_gamma hY hzΓ
  obtain ⟨DH,hCDH,hH⟩ := fixed_label_translation_contraction_common_blowup hc C C.uncountable.le C.saturated
    hsmall hgamma γ hγ hγ1 hPS hGeneric Z hZ 0 K.horizontal
    (balanced_horizontal_native_centre_independent Z h.2.2.1 K.horizontal K.horizontal_value)
    hKX z hz hzΓ j η hj hη0 (by rfl) T G.headContraction hT hHead
  obtain ⟨DT,hCDT,hL⟩ := fixed_label_translation_contraction_common_blowup hc C C.uncountable.le C.saturated
    hsmall hgamma γ hγ hγ1 hPS hGeneric Z hZ 1 K.vertical
    (balanced_vertical_native_centre_independent Z K.vertical K.vertical_value)
    hKY z hz hzΓ j η hj hη0 (by decide) E G.tailContraction hE hTail
  have hEqHead := F.head_fixed_label_contraction_object C.uncountable.le C.saturated hsmall hc C
    (Set.Subset.refl _) hNames hPS hX hzΓ hrS η hη hη0 j hj
  have hEqTail := F.tail_fixed_label_contraction_object C.uncountable.le C.saturated hsmall hc C
    (Set.Subset.refl _) hNames hPS hY hzΓ htS η hη hη0 j hj
  have hH1 := Eq.mp (congrArg (fun W : GammaVolumeObjects P (C.base : Set M) 1 =>
    GammaVolumeBlowupEquivalent P (DH.base : Set M) 1 (U.extend hCDH) (W.extend hCDH)) hEqHead) hH
  have hL1 := Eq.mp (congrArg (fun W : GammaVolumeObjects P (C.base : Set M) 1 =>
    GammaVolumeBlowupEquivalent P (DT.base : Set M) 1 (V.extend hCDT) (W.extend hCDT)) hEqTail) hL
  obtain ⟨D,hHD,hLD⟩ := volume_context_join_exists DH DT
  let hCD := hCDH.trans hHD
  have hFirst := hH1.extend hHD
  have hLast := hL1.extend hLD
  have hMiddle : GammaVolumeBlowupEquivalent P (D.base : Set M) 1
      ((G.headNormalizedGammaObject C.uncountable.le C.saturated hsmall hc hPS hrS η hη hη0 j hj).extend hCD)
      ((G.tailNormalizedGammaObject C.uncountable.le C.saturated hsmall hc hPS htS η hη hη0 j hj).extend hCD) :=
    GammaVolumeBlowupEquivalent.of_iso D P (g.extend hCD) (hg.extend hCD)
  exact ⟨D,hCD,hFirst.trans hc D P (hMiddle.trans hc D P (hLast.symm hc D P))⟩

end IntegrationInACVF.Section7
