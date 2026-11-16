module

public import Integration7.GammaVolumeExistentialCertificates
public import Integration7.GammaVolumeIsomorphismSchemata
public import IntegrationSection6.GammaFormulaBaseChange

@[expose] public section

/-! Changing a definability base leaves all coordinate, density,
Jacobian and exceptional-set formulas literally unchanged. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3.GammaParameters
open IntegrationInACVF.Section6

open IntegrationInACVF.Section7

namespace IntegrationInACVF.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {B C : Base (M := M)} {p a b k : ℕ} {sp : Fin p → SortTag}

def GammaFormulaBaseChange.volumeObject (H : GammaFormulaBaseChange C B)
    (F : GammaRVVolumeSchema C p a k sp) : GammaRVVolumeSchema B p a k sp where
  object := H.object F.object
  density := F.density
  density_definable := H.definable _ _ F.density_definable
  density_nonzero := F.density_nonzero

def GammaFormulaBaseChange.volumeIso (H : GammaFormulaBaseChange C B)
    (F : GammaRVVolumeIsoSchema C p a b k sp) : GammaRVVolumeIsoSchema B p a b k sp where
  source := H.volumeObject F.source
  target := H.volumeObject F.target
  chart := F.chart
  chart_definable := H.definable _ _ F.chart_definable
  supports := F.supports
  exceptionDegree := F.exceptionDegree
  exceptionDegree_lt := F.exceptionDegree_lt
  exception := H.object F.exception

def GammaFormulaBaseChange.volumeCertificate (H : GammaFormulaBaseChange C B)
    (F : GammaRVVolumeIsoCertificateSchema C p a b k sp) : GammaRVVolumeIsoCertificateSchema B p a b k sp where
  source := H.volumeObject F.source
  target := H.volumeObject F.target
  chart := F.chart
  chart_definable := H.definable _ _ F.chart_definable
  supports := F.supports
  extraArity := F.extraArity
  extraSort := F.extraSort
  exceptionDegree := F.exceptionDegree
  exceptionDegree_lt := F.exceptionDegree_lt
  exception := H.object F.exception

theorem GammaFormulaBaseChange.volumeObject_valid (H : GammaFormulaBaseChange C B)
    (F : GammaRVVolumeSchema C p a k sp) (z : Fin p → M) :
    (H.volumeObject F).valid z ↔ F.valid z := Iff.rfl

theorem GammaFormulaBaseChange.volumeIso_valid (H : GammaFormulaBaseChange C B)
    (F : GammaRVVolumeIsoSchema C p a b k sp) (z : Fin p → M) :
    (H.volumeIso F).valid z ↔ F.valid z := Iff.rfl

theorem GammaFormulaBaseChange.volumeCertificate_valid (H : GammaFormulaBaseChange C B)
    (F : GammaRVVolumeIsoCertificateSchema C p a b k sp) (z : Fin p → M) :
    (H.volumeCertificate F).valid z ↔ F.valid z := Iff.rfl

end IntegrationInACVF.Section6
