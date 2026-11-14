import Integration7.ZeroAuxVolumeCommonPromotion
import Integration7.VolumeCommonWitnessCompactness

/-! The finite witness cover may be chosen with every exception map
already over its original named parameter block. -/

set_option backward.isDefEq.respectTransparency false
noncomputable section
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters

namespace IntegrationInACVF.Section7

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {p a b k : ℕ} {sp : Fin p → SortTag}

theorem gamma_volume_common_witness_no_auxiliary {κ : Cardinal}
    (hc : CanonicalStructure.IsCanonical (M := M))
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (hreal : Cardinal.mk B.real < κ) (hgamma : Cardinal.mk B.gamma < κ)
    (F : GammaRVVolumeSchema B p a k sp) (G : GammaRVVolumeSchema B p b k sp)
    (z : Fin p → M) (hF : F.valid z) (hG : G.valid z) (hCommon : F.commonInNamedContext G z) :
    ∃ H : GammaVolumeCommonSchema F G, H.valid z ∧ H.NoAuxiliary := by
  obtain ⟨C,hBase,U,V,ha,hb,PU,PV,h⟩ := hCommon
  subst a b
  exact gamma_volume_common_promotion_no_auxiliary hc C hκ hs h00 hreal hgamma z hF.1.1 hBase
    F G hF hG PU PV h

theorem gamma_volume_common_finite_cover_no_auxiliary {κ : Cardinal}
    (hc : CanonicalStructure.IsCanonical (M := M))
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (hreal : Cardinal.mk B.real < κ) (hgamma : Cardinal.mk B.gamma < κ)
    (F : GammaRVVolumeSchema B p a k sp) (G : GammaRVVolumeSchema B p b k sp)
    (A : Set (Fin p → M)) (hA : DefinableOverBase B sp A)
    (hF : ∀ z ∈ A, F.valid z) (hG : ∀ z ∈ A, G.valid z)
    (hCommon : ∀ z ∈ A, F.commonInNamedContext G z) :
    ∃ J : Finset {H : GammaVolumeCommonSchema F G // H.NoAuxiliary}, ∃ bound : ℕ,
      ∀ z ∈ A, ∃ H ∈ J, H.val.leftLength ≤ bound ∧ H.val.rightLength ≤ bound ∧ H.val.valid z := by
  obtain ⟨J,N,hJ⟩ := Section6.gamma_uniform_witness_length hκ hs hreal hgamma sp A hA
    (fun H : {H : GammaVolumeCommonSchema F G // H.NoAuxiliary} => {z | H.val.valid z})
    (fun H => H.val.valid_definable hc) (fun H => max H.val.leftLength H.val.rightLength) (by
      intro z hz
      obtain ⟨H,hV,hAux⟩ := gamma_volume_common_witness_no_auxiliary hc hκ hs h00 hreal hgamma F G z
        (hF z hz) (hG z hz) (hCommon z hz)
      exact ⟨⟨H,hAux⟩,hV⟩)
  refine ⟨J,N,?_⟩
  intro z hz
  obtain ⟨H,hH,hN,hV⟩ := hJ z hz
  exact ⟨H,hH,(le_max_left _ _).trans hN,(le_max_right _ _).trans hN,hV⟩

end IntegrationInACVF.Section7
