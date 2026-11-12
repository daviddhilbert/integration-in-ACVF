import IntegrationSection6.GammaRawCoproductSchemaBridge
import IntegrationSection6.GammaRawElementarySchemaBridge
import IntegrationSection6.GammaSchemaChartTransfer

/-! A finite blowup witness is encoded by actual center/remainder object
formulas, an admissible coordinate, and full source/result splitting charts.
Its validity locus is first order over the original real/Gamma base. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5 SpecialTransformations.Section7
namespace IntegrationInACVF.Section6
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {p a b k : ℕ} {sp : Fin p → SortTag}

structure GammaFiniteBlowupSchema (U : GammaFiniteRVSchema B p a k sp)
    (V : GammaFiniteRVSchema B p b k sp) where
  centerArity : ℕ
  remainderArity : ℕ
  center : GammaFiniteRVSchema B p centerArity k sp
  remainder : GammaFiniteRVSchema B p remainderArity k sp
  coordinate : Fin k
  admissibilityBound : ℕ
  sourceChart : GammaFiniteRVIsoSchema B p a (1+(centerArity+remainderArity)) k sp
  resultChart : GammaFiniteRVIsoSchema B p b (1+((centerArity+1)+remainderArity)) k sp

variable {U : GammaFiniteRVSchema B p a k sp} {V : GammaFiniteRVSchema B p b k sp}

def GammaFiniteBlowupSchema.admissibility (H : GammaFiniteBlowupSchema U V) :
    GammaFiniteAdmissibilitySchema B p H.centerArity k sp :=
  ⟨H.center,H.coordinate,H.admissibilityBound⟩

def GammaFiniteBlowupSchema.valid (H : GammaFiniteBlowupSchema U V) (z : Fin p → M) : Prop :=
  H.admissibility.valid z ∧ H.remainder.valid z ∧ H.sourceChart.valid z ∧ H.resultChart.valid z ∧
  H.sourceChart.source.sameRow U z ∧
  H.sourceChart.target.sameRow (H.center.coprodFormula H.remainder) z ∧
  H.resultChart.source.sameRow V z ∧
  H.resultChart.target.sameRow ((H.center.elementaryFormula H.coordinate).coprodFormula H.remainder) z

theorem GammaFiniteBlowupSchema.valid_definable (H : GammaFiniteBlowupSchema U V) :
    DefinableOverBase B sp {z | H.valid z} :=
  H.admissibility.valid_definable.inter (H.remainder.valid_definable.inter
    (H.sourceChart.valid_definable.inter (H.resultChart.valid_definable.inter
      ((H.sourceChart.source.sameRow_definable U).inter
        ((H.sourceChart.target.sameRow_definable (H.center.coprodFormula H.remainder)).inter
          ((H.resultChart.source.sameRow_definable V).inter
            (H.resultChart.target.sameRow_definable
              ((H.center.elementaryFormula H.coordinate).coprodFormula H.remainder))))))))

theorem GammaFiniteBlowupSchema.realize {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (hreal : Cardinal.mk B.real < κ) (H : GammaFiniteBlowupSchema U V)
    (z : Fin p → M) (hz : H.valid z)
    (P : GammaFiniteGraphPresentation ⟨B.real ∪ Set.range z,B.gamma⟩ a k
      (U.rowDomain z) (U.rowVolume z))
    (Q : GammaFiniteGraphPresentation ⟨B.real ∪ Set.range z,B.gamma⟩ b k
      (V.rowDomain z) (V.rowVolume z)) :
    ∃ CP : GammaFiniteGraphPresentation ⟨B.real ∪ Set.range z,B.gamma⟩ H.centerArity k
        (H.center.rowDomain z) (H.center.rowVolume z),
    ∃ RP : GammaFiniteGraphPresentation ⟨B.real ∪ Set.range z,B.gamma⟩ H.remainderArity k
        (H.remainder.rowDomain z) (H.remainder.rowVolume z),
    let hParam := hz.1.1.1
    let hAd := H.admissibility.admissible z hz.1 CP
    let EP := H.center.elementaryPresentation hκ hs h00 hreal z hParam CP H.coordinate hAd
    let SP := H.center.coprodPresentation H.remainder z hParam
      (H.center.valid_row_support hz.1.1) (H.remainder.valid_row_support hz.2.1) CP RP
    let TP := (H.center.elementaryFormula H.coordinate).coprodPresentation H.remainder z hParam
      (H.center.elementary_row_support H.coordinate z hParam) (H.remainder.valid_row_support hz.2.1) EP RP
    Nonempty (GammaRVIso P.toGamma.toGammaRVObject SP.toGamma.toGammaRVObject) ∧
      Nonempty (GammaRVIso Q.toGamma.toGammaRVObject TP.toGamma.toGammaRVObject) := by
  obtain ⟨CP⟩ := H.center.realize z hz.1.1
  obtain ⟨RP⟩ := H.remainder.realize z hz.2.1
  refine ⟨CP,RP,?_⟩
  dsimp only
  constructor
  · exact ⟨H.sourceChart.realizeBetween U (H.center.coprodFormula H.remainder) z hz.2.2.1
      hz.2.2.2.2.1 hz.2.2.2.2.2.1 P _⟩
  · exact ⟨H.resultChart.realizeBetween V ((H.center.elementaryFormula H.coordinate).coprodFormula H.remainder)
      z hz.2.2.2.1 hz.2.2.2.2.2.2.1 hz.2.2.2.2.2.2.2 Q _⟩

end IntegrationInACVF.Section6
