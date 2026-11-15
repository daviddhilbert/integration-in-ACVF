import Integration7.VolumeFamilyPositiveCoefficientRows
import Integration7.SelectedVolumeFamilyAddition
import Integration7.RVVolumeProducts

/-! Selected presentations of actual multiplication by a positive
constant coefficient, with the coefficient-first RV product on each row. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {C : BaseContext M} {n a k p : ℕ}

def selectedVolumeFamilyLeftProduct
    (U : PositiveRVVolumeObject (M := M) (C.base : Set M) p) (F : SelectedVFVolumeFamily C n a k) :
    SelectedVFVolumeFamily C n ((a+U.underlying.obj.arity)+(((p+1)+k)+1)) ((p+1)+k) :=
  (F.toDefinable.mulConstant U).toSelected

def selectedVolumeFamilyLeftProductRowIso
    (hc : CanonicalStructure.IsCanonical (M := M))
    (U : PositiveRVVolumeObject (M := M) (C.base : Set M) p) (F : SelectedVFVolumeFamily C n a k)
    (x : Fin n → VFType (M := M)) :
    RVVolumeIso ((selectedVolumeFamilyLeftProduct U F).rowInContext x)
      ((positiveVolumeCoefficientInContext U x).prod (F.rowInContext x)) := by
  let D := vfParameterVolumeContext C x
  exact (((F.toDefinable.mulConstant U).selectionRowIso hc x).symm hc D).trans hc D
    ((volumeFamilyPositiveCoefficientRowIso hc F.toDefinable U x).trans hc D
      ((RVVolumeIso.refl hc D (positiveVolumeCoefficientInContext U x)).prod hc D
        ((selectedToDefinableVolumeRowIso hc F x).symm hc D)))

end IntegrationInACVF.Section7
