module

public import IntegrationSection6.GammaIsomorphismPromotion
public import IntegrationSection6.GammaSchemaNativeRows
public import IntegrationSection6.GammaSchemaValidityTransport
public import IntegrationSection6.GammaParameterRecoding

@[expose] public section

/-! A finite Gamma row isomorphism has a genuine formula witness with
the specified endpoint schemata. Endpoint bounds stay those of the
given valid families; changing charts introduces no new finiteness input. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5 SpecialTransformations.Section7
open IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {p a b k : ℕ} {sp : Fin p → SortTag}

def gammaFiniteRowChartSchema
    (F : GammaFiniteRVSchema B p a k sp) (G : GammaFiniteRVSchema B p b k sp)
    (H : GammaRelationFormula B p a b sp) : GammaFiniteRVIsoSchema B p a b k sp :=
  ⟨F,G,H.val,H.property⟩

theorem gamma_finite_row_chart_valid_of_rows
    (W : GammaFiniteRVIsoSchema B p a b k sp)
    (F : GammaFiniteRVSchema B p a k sp) (G : GammaFiniteRVSchema B p b k sp)
    (z : Fin p → M) (hW : W.valid z) (hF : F.valid z) (hG : G.valid z)
    (hWF : GammaSchemaRowAgreement W.source z F z)
    (hWG : GammaSchemaRowAgreement W.target z G z) :
    (gammaFiniteRowChartSchema F G ⟨W.chart,W.chart_definable⟩).valid z := by
  exact ⟨hF,hG,
    bijectiveMapRowValid_of_rows hF.1 hWF.1 hWG.1 (fun _ _ => Iff.rfl) hW.2.2.1,
    weightedChartRowValid_of_rows hF.1 (fun _ _ => Iff.rfl) hWF.2 hWG.2 hW.2.2.2⟩

theorem gamma_finite_row_isomorphism_formula_witness {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (hreal : Cardinal.mk B.real < κ) (hgamma : Cardinal.mk B.gamma < κ)
    (F : GammaFiniteRVSchema B p a k sp) (G : GammaFiniteRVSchema B p b k sp)
    (z : Fin p → M) (hF : F.valid z) (hG : G.valid z)
    (P : GammaFiniteGraphPresentation ⟨B.real ∪ Set.range z,B.gamma⟩ a k (F.rowDomain z) (F.rowVolume z))
    (Q : GammaFiniteGraphPresentation ⟨B.real ∪ Set.range z,B.gamma⟩ b k (G.rowDomain z) (G.rowVolume z))
    (e : GammaRVIso P.toGamma.toGammaRVObject Q.toGamma.toGammaRVObject) :
    ∃ H : GammaRelationFormula B p a b sp, (gammaFiniteRowChartSchema F G H).valid z := by
  obtain ⟨W,hW,hSD,hSV,hTD,hTV,_⟩ := gamma_sorted_finite_isomorphism_promotion
    hκ hs hreal hgamma sp z hF.1 P.toGamma Q.toGamma e
  apply Exists.intro ⟨W.chart,W.chart_definable⟩
  apply gamma_finite_row_chart_valid_of_rows W F G z hW hF hG
  · exact ⟨fun x => (hSD x).trans (F.raw_row_domain_presented z P x).symm,
      fun x y => (hSV x y).trans
        (F.raw_row_volume_presented z (fun t s h => hF.2.2.1 (fun j => (t j).val) (fun j => (s j).val) h) P x y).symm⟩
  · exact ⟨fun x => (hTD x).trans (G.raw_row_domain_presented z Q x).symm,
      fun x y => (hTV x y).trans
        (G.raw_row_volume_presented z (fun t s h => hG.2.2.1 (fun j => (t j).val) (fun j => (s j).val) h) Q x y).symm⟩

end IntegrationInACVF.Section7
