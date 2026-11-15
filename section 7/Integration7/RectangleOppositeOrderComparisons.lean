import Integration7.TwoOrderRectangleVolumeComparisons
import Integration7.FixedLabelContractionConstantDensities
import Integration7.FixedLabelSameOrderComparisons
import Integration7.VolumeContextJoins

/-! The rectangle case of Lemma7.7 for arbitrary specified contractions
in opposite orders, on the actual retained-density normalized objects. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section5

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {P : Base (M := M)} {d : ℕ}

set_option maxHeartbeats 1200000 in
theorem rectangle_opposite_order_contraction_comparison
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (hgamma : Cardinal.mk P.gamma < C.κ) (γ : Values.Gamma (M := M)) (hγ : γ ∈ P.gamma) (hγ1 : 1 < γ)
    (hPC : P.real ⊆ (C.base : Set M)) (hNames : commonRealNames P ⊆ (C.base : Set M))
    (hGeneric : ∀ {p : ℕ} (x : Fin p → VF (M := M)), AlgebraicIndependent (vfParameterField P.real) x →
      AlgebraicIndependent (vfParameterField (C.base : Set M)) x)
    (D E : DefSet (M := M) (C.base : Set M) 1 0)
    (hD : GammaSetDefinable P (carrier D)) (hE : GammaSetDefinable P (carrier E))
    (z : Fin d → RV (M := M)) (hz : ∀ j, (z j).val ∈ (C.base : Set M))
    (hzΓ : DefinableOverBase P (fun _ : Fin d => .rv) {fun j => (z j).val})
    (j : Fin d) (η : RV (M := M)) (hj : z j = η) (hη : η.val ∈ C.base) (hη0 : η ≠ 0)
    (T : IntegrationInACVF.Section5.StandardContraction (fixedRVLabelDomain (nativeUnaryProductDomain D E) z hz) (Equiv.refl _))
    (W : IntegrationInACVF.Section5.StandardContraction (fixedRVLabelDomain (nativeUnaryProductDomain D E) z hz) (Equiv.swap 0 1))
    (hT : IntegrationInACVF.Section5.GammaProgramDefinable P T.program)
    (hW : IntegrationInACVF.Section5.GammaProgramDefinable P W.program) :
    let hsmall : Cardinal.mk P.real < C.κ := (Cardinal.mk_le_mk_of_subset hPC).trans_lt C.small
    let Z := nativeUnaryProductDomain D E
    let hZ := gamma_native_unary_product D E hD hE
    let U := fixedLabelContractionGammaObject C.uncountable.le C.saturated hsmall hc C hPC Z hZ z hz hzΓ j η hj hη0 T hT
    let V := fixedLabelContractionGammaObject C.uncountable.le C.saturated hsmall hc C hPC Z hZ z hz hzΓ j η hj hη0 W hW
    ∃ (K : BaseContext M) (hCK : (C.base : Set M) ⊆ (K.base : Set M)),
      GammaVolumeBlowupEquivalent P (K.base : Set M) 1 (U.extend hCK) (V.extend hCK) := by
  intro hsmall Z hZ U V
  obtain ⟨F⟩ := gamma_two_order_rectangle_preparations_exists C hNames γ hγ hγ1 D E hD hE z hz hzΓ
  let H := fixedLabelContractionGammaObject C.uncountable.le C.saturated hsmall hc C hPC Z hZ z hz hzΓ j η hj hη0
    F.headContraction F.head_contraction_gamma
  let L := fixedLabelContractionGammaObject C.uncountable.le C.saturated hsmall hc C hPC Z hZ z hz hzΓ j η hj hη0
    F.tailContraction F.tail_contraction_gamma
  obtain ⟨KH,hCKH,hH⟩ := fixed_label_same_order_contraction_common_blowup hc C C.uncountable.le C.saturated
    hsmall hgamma γ hγ hγ1 hPC hGeneric Z hZ z hz hzΓ j η hj hη0 T F.headContraction hT F.head_contraction_gamma
  obtain ⟨KL,hCKL,hL⟩ := fixed_label_same_order_contraction_common_blowup hc C C.uncountable.le C.saturated
    hsmall hgamma γ hγ hγ1 hPC hGeneric Z hZ z hz hzΓ j η hj hη0 W F.tailContraction hW F.tail_contraction_gamma
  have hHead := fixed_label_contraction_constant_density C.uncountable.le C.saturated hsmall hc C hPC Z hZ z hz hzΓ
    j η hj hη hη0 F.headContraction F.head_contraction_gamma (F.headRawFiniteVolume hc C hPC)
  have hTail := fixed_label_contraction_constant_density C.uncountable.le C.saturated hsmall hc C hPC Z hZ z hz hzΓ
    j η hj hη hη0 F.tailContraction F.tail_contraction_gamma (F.tailRawFiniteVolume hc C hPC)
  have hProduct := F.normalized_volume_comparison hc C hPC η hη hη0
  have hEndpoints : (F.headNormalizedVolumeObject hc C hPC η hη hη0,
      F.tailNormalizedVolumeObject hc C hPC η hη hη0) = (H.val,L.val) := by
    apply Prod.ext
    · exact hHead.symm
    · exact hTail.symm
  have hType := congrArg (fun UV : PositiveRVVolumeObject (M := M) (C.base : Set M) 1 ×
        PositiveRVVolumeObject (M := M) (C.base : Set M) 1 => ∃ i : RVVolumeIso UV.1 UV.2, i.GammaDefinable P) hEndpoints
  have hActual : ∃ i : RVVolumeIso H.val L.val, i.GammaDefinable P :=
    Eq.mp hType hProduct
  obtain ⟨g,hg⟩ := hActual
  have hMiddle : GammaVolumeBlowupEquivalent P (C.base : Set M) 1 H L := GammaVolumeBlowupEquivalent.of_iso C P g hg
  obtain ⟨K,hHK,hLK⟩ := volume_context_join_exists KH KL
  let hCK := hCKH.trans hHK
  exact ⟨K,hCK,(hH.extend hHK).trans hc K P ((hMiddle.extend hCK).trans hc K P ((hL.extend hLK).symm hc K P))⟩

end IntegrationInACVF.Section7
