import Integration7.GammaVolumeCertificateContexts
import Integration7.GammaVolumeElementaryBounds
import IntegrationSection6.GammaAdmissibilitySchemata

/-! Finite formula data for a volume blowup: an admissible center, a
remainder, and actual volume-comparison chart certificates on the source
and result splittings. Validity compares full coordinate/density rows.
Realization and promotion of blowup witnesses are separate obligations. -/

noncomputable section
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {p a b k : ℕ} {sp : Fin p → SortTag}

structure GammaRVVolumeBlowupSchema (U : GammaRVVolumeSchema B p a k sp)
    (V : GammaRVVolumeSchema B p b k sp) where
  centerArity : ℕ
  remainderArity : ℕ
  center : GammaRVVolumeSchema B p centerArity k sp
  remainder : GammaRVVolumeSchema B p remainderArity k sp
  admissibilityBound : ℕ
  sourceChart : GammaRVVolumeIsoCertificateSchema B p a (1+(centerArity+remainderArity)) k sp
  resultChart : GammaRVVolumeIsoCertificateSchema B p b (1+((centerArity+1)+remainderArity)) k sp

variable {U : GammaRVVolumeSchema B p a k sp} {V : GammaRVVolumeSchema B p b k sp}

def GammaRVVolumeBlowupSchema.admissibility (H : GammaRVVolumeBlowupSchema U V) :
    GammaFiniteAdmissibilitySchema B p H.centerArity (k+1) sp :=
  ⟨H.center.object,Fin.last k,H.admissibilityBound⟩

def GammaRVVolumeBlowupSchema.valid (H : GammaRVVolumeBlowupSchema U V) (z : Fin p → M) : Prop :=
  U.valid z ∧ V.valid z ∧ H.center.valid z ∧ H.remainder.valid z ∧ H.admissibility.valid z ∧
    H.sourceChart.valid z ∧ H.resultChart.valid z ∧
    H.sourceChart.source.sameRow U z ∧
    H.sourceChart.target.sameRow (H.center.coprodFormula H.remainder) z ∧
    H.resultChart.source.sameRow V z ∧
    H.resultChart.target.sameRow (H.center.elementaryFormula.coprodFormula H.remainder) z

theorem GammaRVVolumeBlowupSchema.valid_definable
    (hc : CanonicalStructure.IsCanonical (M := M)) (H : GammaRVVolumeBlowupSchema U V) :
    DefinableOverBase B sp {z | H.valid z} :=
  U.valid_definable.inter (V.valid_definable.inter (H.center.valid_definable.inter
    (H.remainder.valid_definable.inter (H.admissibility.valid_definable.inter
      ((H.sourceChart.valid_definable hc).inter ((H.resultChart.valid_definable hc).inter
        ((H.sourceChart.source.sameRow_definable U).inter
          ((H.sourceChart.target.sameRow_definable (H.center.coprodFormula H.remainder)).inter
            ((H.resultChart.source.sameRow_definable V).inter
              (H.resultChart.target.sameRow_definable
                (H.center.elementaryFormula.coprodFormula H.remainder)))))))))))

end IntegrationInACVF.Section7
