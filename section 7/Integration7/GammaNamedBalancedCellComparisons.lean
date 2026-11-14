import Integration7.BalancedCellOppositeOrderComparisons
import Integration7.NativeBalancedTranslationCommonNames
import Integration7.GammaNamesGenericParameters

/-! The balanced cell case for arbitrary specified contractions over a
common-name context of the original real/Gamma base. Translation centres
and real positioning presentations are constructed internally. -/
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

set_option maxHeartbeats 1600000 in
theorem gamma_named_balanced_cell_contraction_comparison
    (hc : CanonicalStructure.IsCanonical (M := M)) (C0 : BaseContext M)
    (hP0 : P.real ⊆ (C0.base : Set M)) (hBase : P.real = (C0.base : Set M))
    (hgamma : Cardinal.mk P.gamma < C0.κ)
    (γ : Values.Gamma (M := M)) (hγ : γ ∈ P.gamma) (hγ1 : 1 < γ) :
    let C := gammaNamesContainingVolumeContext C0 P hP0 hgamma
    let hPS : P.real ⊆ (C.base : Set M) := fun _ hx =>
      gamma_names_containing_volume_context_contains C0 P hP0 hgamma (Or.inl (hP0 hx))
    ∀    (Z : DefSet (M := M) (C.base : Set M) 2 0) (hZ : GammaSetDefinable P (carrier Z))
    (ε : VF (M := M) → VF (M := M)) (r t : RV (M := M))
    (h : IsBalanced (nativeVFPairDomain Z) ε r t)
    (hfΓ : DefinableOverBase P (fun _ : Fin 2 => .vf) (positionCodes (first (nativeVFPairDomain Z)) ε))
    (hr : r ≠ rv (0 : VF (M := M))) (hrS : r.val ∈ (C.base : Set M)) (htS : t.val ∈ (C.base : Set M))
    (hr0 : r.val ≠ iRVZero) (ht0 : t.val ≠ iRVZero)
    (z : Fin d → RV (M := M)) (hz : ∀ j, (z j).val ∈ (C.base : Set M))
    (hzΓ : DefinableOverBase P (fun _ : Fin d => .rv) {fun j => (z j).val})
    (η : RV (M := M)) (hη0 : η ≠ 0) (j : Fin d) (hj : z j = η)
    (T : StandardContraction (fixedRVLabelDomain Z z hz) (Equiv.refl _))
    (E : StandardContraction (fixedRVLabelDomain Z z hz) (Equiv.swap 0 1))
    (hT : GammaProgramDefinable P T.program) (hE : GammaProgramDefinable P E.program),
    let hsmall : Cardinal.mk P.real < C.κ := (Cardinal.mk_le_mk_of_subset hPS).trans_lt C.small
    let U := fixedLabelContractionGammaObject C.uncountable.le C.saturated hsmall hc C hPS Z hZ z hz hzΓ j η hj hη0 T hT
    let V := fixedLabelContractionGammaObject C.uncountable.le C.saturated hsmall hc C hPS Z hZ z hz hzΓ j η hj hη0 E hE
    ∃ (D : BaseContext M) (hCD : (C.base : Set M) ⊆ (D.base : Set M)),
      GammaVolumeBlowupEquivalent P (D.base : Set M) 1 (U.extend hCD) (V.extend hCD) := by
  intro C hPS Z hZ ε r t h hfΓ hr hrS htS hr0 ht0 z hz hzΓ η hη0 j hj T E hT hE
  have hNames : commonRealNames P ⊆ (C.base : Set M) := fun _ hx =>
    gamma_names_containing_volume_context_contains C0 P hP0 hgamma (Or.inr hx)
  obtain ⟨K,hKV,hKH⟩ := balanced_translation_centres_over_common_names hNames Z hZ h.2.2.1 hfΓ
  have hf := hfΓ.common_names.mono hNames
  have hη : η.val ∈ (C.base : Set M) := by
    rw [← hj]
    exact hz j
  exact balanced_cell_opposite_order_contraction_comparison C hgamma γ hγ hγ1 hPS hNames
    (fun x hx => gamma_names_context_preserves_independence hc C0 P hP0 hgamma hBase x hx)
    hc Z hZ ε r t h hf hfΓ hr hrS htS hr0 ht0 K hKH hKV z hz hzΓ η hη hη0 j hj T E hT hE

end IntegrationInACVF.Section7
