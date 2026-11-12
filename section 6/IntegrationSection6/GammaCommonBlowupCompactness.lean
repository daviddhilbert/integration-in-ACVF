import IntegrationSection6.GammaCommonBlowupPromotion
import IntegrationSection6.GammaCommonBlowupRealization
import IntegrationSection6.GammaWitnessUniformity

/-! Genuine finite-witness compactness for actual common blowups. The
witness loci are built from the checked object, admissibility and weighted
chart formulas, rather than assumed definable as an abstract Isp predicate. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5 SpecialTransformations.Section7
namespace IntegrationInACVF.Section6
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {p a b k : ℕ} {sp : Fin p → SortTag}

theorem gamma_common_witness_at_parameter {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (hreal : Cardinal.mk B.real < κ) (hgamma : Cardinal.mk B.gamma < κ)
    (F : GammaFiniteRVSchema B p a k sp) (G : GammaFiniteRVSchema B p b k sp)
    (z : Fin p → M) (hF : F.valid z) (hG : G.valid z)
    (P : GammaFiniteGraphPresentation ⟨B.real ∪ Set.range z,B.gamma⟩ a k
      (F.rowDomain z) (F.rowVolume z))
    (Q : GammaFiniteGraphPresentation ⟨B.real ∪ Set.range z,B.gamma⟩ b k
      (G.rowDomain z) (G.rowVolume z))
    (hI : FiniteRV.GammaIsp hκ hs h00 (small_union_range hκ B.real hreal z) P.toGamma Q.toGamma) :
    ∃ W : GammaFiniteCommonSchema F G, W.valid z := by
  have hRepF : gammaSchemaRepresents P.toGamma F z :=
    ⟨F.raw_row_domain_presented z P,F.raw_row_volume_presented z (F.valid_row_support hF) P⟩
  have hRepG : gammaSchemaRepresents Q.toGamma G z :=
    ⟨G.raw_row_domain_presented z Q,G.raw_row_volume_presented z (G.valid_row_support hG) Q⟩
  exact gamma_sorted_finite_common_promotion hκ hs h00 hreal hgamma sp z hF.1
    P.toGamma Q.toGamma F G hRepF hRepG hI

theorem gamma_common_finite_witness_cover {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (hreal : Cardinal.mk B.real < κ) (hgamma : Cardinal.mk B.gamma < κ)
    (F : GammaFiniteRVSchema B p a k sp) (G : GammaFiniteRVSchema B p b k sp)
    (A : Set (Fin p → M)) (hA : DefinableOverBase B sp A)
    (hF : ∀ z ∈ A, F.valid z) (hG : ∀ z ∈ A, G.valid z)
    (hCommon : ∀ z ∈ A,
      ∀ P : GammaFiniteGraphPresentation ⟨B.real ∪ Set.range z,B.gamma⟩ a k
        (F.rowDomain z) (F.rowVolume z),
      ∀ Q : GammaFiniteGraphPresentation ⟨B.real ∪ Set.range z,B.gamma⟩ b k
        (G.rowDomain z) (G.rowVolume z),
      FiniteRV.GammaIsp hκ hs h00 (small_union_range hκ B.real hreal z) P.toGamma Q.toGamma) :
    ∃ J : Finset (GammaFiniteCommonSchema F G), ∀ z ∈ A, ∃ W ∈ J, W.valid z := by
  apply gamma_finite_witnesses hκ hs hreal hgamma sp A hA
    (fun W : GammaFiniteCommonSchema F G => {z | W.valid z}) (fun W => W.valid_definable)
  intro z hz
  obtain ⟨P⟩ := F.realize z (hF z hz)
  obtain ⟨Q⟩ := G.realize z (hG z hz)
  exact gamma_common_witness_at_parameter hκ hs h00 hreal hgamma F G z
    (hF z hz) (hG z hz) P Q (hCommon z hz P Q)

theorem gamma_common_uniform_chain_bound {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (hreal : Cardinal.mk B.real < κ) (hgamma : Cardinal.mk B.gamma < κ)
    (F : GammaFiniteRVSchema B p a k sp) (G : GammaFiniteRVSchema B p b k sp)
    (A : Set (Fin p → M)) (hA : DefinableOverBase B sp A)
    (hcover : ∀ z ∈ A, ∃ W : GammaFiniteCommonSchema F G, W.valid z) :
    ∃ J : Finset (GammaFiniteCommonSchema F G), ∃ bound : ℕ,
      ∀ z ∈ A, ∃ W ∈ J, W.leftLength ≤ bound ∧ W.rightLength ≤ bound ∧ W.valid z := by
  obtain ⟨J,bound,hJ⟩ := gamma_uniform_witness_length hκ hs hreal hgamma sp A hA
    (fun W : GammaFiniteCommonSchema F G => {z | W.valid z}) (fun W => W.valid_definable)
    (fun W => max W.leftLength W.rightLength) hcover
  refine ⟨J,bound,?_⟩
  intro z hz
  obtain ⟨W,hW,hbound,hvalid⟩ := hJ z hz
  exact ⟨W,hW,(le_max_left _ _).trans hbound,(le_max_right _ _).trans hbound,hvalid⟩

end IntegrationInACVF.Section6
