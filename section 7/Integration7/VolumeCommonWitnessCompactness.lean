import Integration7.ActualVolumeCommonPromotion
import IntegrationSection6.GammaWitnessUniformity

/-! Compactness for actual volume common-blowup witnesses. The geometric
premise uses actual objects and common forward blowups over the original
named term context; witness-locus definability is proved from formula data. -/

set_option backward.isDefEq.respectTransparency false
noncomputable section
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters

namespace IntegrationInACVF.Section7

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {p a b k : ℕ} {sp : Fin p → SortTag}

def GammaRVVolumeSchema.commonInNamedContext (F : GammaRVVolumeSchema B p a k sp)
    (G : GammaRVVolumeSchema B p b k sp) (z : Fin p → M) : Prop :=
  ∃ C : BaseContext M,
    (C.base : Set M) = (Substructure.closure LRV (B.real ∪ Set.range z) : Set M) ∧
    ∃ U V : PositiveRVVolumeObject (M := M) (C.base : Set M) k,
      ∃ (ha : U.underlying.obj.arity = a) (hb : V.underlying.obj.arity = b),
        RVVolumeSchemaRow U (ha.symm ▸ F) z ∧ RVVolumeSchemaRow V (hb.symm ▸ G) z ∧
          VolumeBlowupEquivalent U V

theorem gamma_volume_common_witness_at_parameter {κ : Cardinal}
    (hc : CanonicalStructure.IsCanonical (M := M))
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (hreal : Cardinal.mk B.real < κ) (hgamma : Cardinal.mk B.gamma < κ)
    (F : GammaRVVolumeSchema B p a k sp) (G : GammaRVVolumeSchema B p b k sp)
    (z : Fin p → M) (hF : F.valid z) (hG : G.valid z)
    (hCommon : F.commonInNamedContext G z) :
    ∃ H : GammaVolumeCommonSchema F G, H.valid z := by
  obtain ⟨C,hBase,U,V,ha,hb,PU,PV,h⟩ := hCommon
  subst a b
  exact gamma_volume_actual_common_promotion hc C hκ hs h00 hreal hgamma z hF.1.1 hBase
    F G hF hG PU PV h

theorem gamma_volume_common_finite_witness_cover {κ : Cardinal}
    (hc : CanonicalStructure.IsCanonical (M := M))
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (hreal : Cardinal.mk B.real < κ) (hgamma : Cardinal.mk B.gamma < κ)
    (F : GammaRVVolumeSchema B p a k sp) (G : GammaRVVolumeSchema B p b k sp)
    (A : Set (Fin p → M)) (hA : DefinableOverBase B sp A)
    (hF : ∀ z ∈ A, F.valid z) (hG : ∀ z ∈ A, G.valid z)
    (hCommon : ∀ z ∈ A, F.commonInNamedContext G z) :
    ∃ J : Finset (GammaVolumeCommonSchema F G), ∃ bound : ℕ,
      ∀ z ∈ A, ∃ H ∈ J, H.leftLength ≤ bound ∧ H.rightLength ≤ bound ∧ H.valid z := by
  obtain ⟨J,N,hJ⟩ := Section6.gamma_uniform_witness_length hκ hs hreal hgamma sp A hA
    (fun H : GammaVolumeCommonSchema F G => {z | H.valid z}) (fun H => H.valid_definable hc)
    (fun H => max H.leftLength H.rightLength) (fun z hz =>
      gamma_volume_common_witness_at_parameter hc hκ hs h00 hreal hgamma F G z (hF z hz) (hG z hz)
        (hCommon z hz))
  refine ⟨J,N,?_⟩
  intro z hz
  obtain ⟨H,hH,hN,hValid⟩ := hJ z hz
  exact ⟨H,hH,(le_max_left _ _).trans hN,(le_max_right _ _).trans hN,hValid⟩

end IntegrationInACVF.Section7
