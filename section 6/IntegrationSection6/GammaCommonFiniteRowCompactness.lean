import IntegrationSection6.GammaCommonBlowupCompactness
import IntegrationSection6.GammaSchemaFiniteRowPresentations

/-! Finite common-blowup witness covers need only actual finite row
semantics at the endpoints. No common cardinality bound is imposed on
the endpoint families. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5 SpecialTransformations.Section7
namespace IntegrationInACVF.Section6
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {p a b k : ℕ} {sp : Fin p → SortTag}

theorem gamma_common_witness_of_finiteRow {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (hreal : Cardinal.mk B.real < κ) (hgamma : Cardinal.mk B.gamma < κ)
    (F : GammaFiniteRVSchema B p a k sp) (G : GammaFiniteRVSchema B p b k sp)
    (z : Fin p → M) (hz : ∀ j, sortEval (sp j) (z j)) (hF : F.finiteRow z) (hG : G.finiteRow z)
    (P : GammaFiniteGraphPresentation ⟨B.real ∪ Set.range z,B.gamma⟩ a k (F.rowDomain z) (F.rowVolume z))
    (Q : GammaFiniteGraphPresentation ⟨B.real ∪ Set.range z,B.gamma⟩ b k (G.rowDomain z) (G.rowVolume z))
    (hI : FiniteRV.GammaIsp hκ hs h00 (small_union_range hκ B.real hreal z) P.toGamma Q.toGamma) :
    ∃ W : GammaFiniteCommonSchema F G, W.valid z := by
  have hRepF : gammaSchemaRepresents P.toGamma F z :=
    ⟨F.raw_row_domain_presented z P,F.raw_row_volume_presented z hF.2.1 P⟩
  have hRepG : gammaSchemaRepresents Q.toGamma G z :=
    ⟨G.raw_row_domain_presented z Q,G.raw_row_volume_presented z hG.2.1 Q⟩
  exact gamma_sorted_finite_common_promotion hκ hs h00 hreal hgamma sp z hz
    P.toGamma Q.toGamma F G hRepF hRepG hI

theorem gamma_common_finite_cover_of_finiteRows {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (hreal : Cardinal.mk B.real < κ) (hgamma : Cardinal.mk B.gamma < κ)
    (F : GammaFiniteRVSchema B p a k sp) (G : GammaFiniteRVSchema B p b k sp)
    (A : Set (Fin p → M)) (hA : DefinableOverBase B sp A)
    (hF : ∀ z ∈ A, F.finiteRow z) (hG : ∀ z ∈ A, G.finiteRow z)
    (hCommon : ∀ z ∈ A,
      ∀ P : GammaFiniteGraphPresentation ⟨B.real ∪ Set.range z,B.gamma⟩ a k (F.rowDomain z) (F.rowVolume z),
      ∀ Q : GammaFiniteGraphPresentation ⟨B.real ∪ Set.range z,B.gamma⟩ b k (G.rowDomain z) (G.rowVolume z),
      FiniteRV.GammaIsp hκ hs h00 (small_union_range hκ B.real hreal z) P.toGamma Q.toGamma) :
    ∃ J : Finset (GammaFiniteCommonSchema F G), ∀ z ∈ A, ∃ W ∈ J, W.valid z := by
  apply gamma_finite_witnesses hκ hs hreal hgamma sp A hA
    (fun W : GammaFiniteCommonSchema F G => {z | W.valid z}) (fun W => W.valid_definable)
  intro z hz
  have hproper := hA.proper z hz
  obtain ⟨P⟩ := F.realize_finiteRow z hproper (hF z hz)
  obtain ⟨Q⟩ := G.realize_finiteRow z hproper (hG z hz)
  exact gamma_common_witness_of_finiteRow hκ hs h00 hreal hgamma F G z hproper
    (hF z hz) (hG z hz) P Q (hCommon z hz P Q)

end IntegrationInACVF.Section6
