import Integration7.CoordinateSelectedCoefficientFamilies

/-! Literal-label coefficient families represent the same genuine row
products as the general selected multiplication construction. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.DefinableGeometry
namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {C : BaseContext M} {n a k p : ℕ}
variable (hc : CanonicalStructure.IsCanonical (M := M))
variable (F : SelectedVFVolumeFamily C n a k)
variable (U : PositiveRVVolumeObject (M := M) (C.base : Set M) p)
variable (σ : Fin (p+1) → Fin U.underlying.obj.arity)
variable (hσ : ∀ u : U.underlying.obj.domain, U.underlying.obj.value u=u.val ∘ σ)

def coordinateSelectedCoefficientDefinableRowIso (x : Fin n → VFType (M := M)) :
    RVVolumeIso ((coordinateSelectedCoefficientFamily F U σ hσ).rowInContext x)
      ((F.toDefinable.mulConstant U).rowInContext x) := by
  let J := coordinateSelectedCoefficientFamily F U σ hσ
  let W := (F.toDefinable.mulConstant U).rowInContext x
  have hCoord : ∀ q : (J.rowInContext x).underlying.obj.domain,
      W.underlying.obj.value q=(J.rowInContext x).underlying.obj.value q := by
    intro q
    exact coordinate_selected_coefficient_volume F U σ hσ ⟨(x,q.val),q.property⟩
  exact RVVolumeIso.of_preserving_coordinates_full hc (vfParameterVolumeContext C x)
    (rvFiniteIsoOfAmbient
      (U := (J.rowInContext x).underlying) (V := W.underlying)
      (rvIsoOfVolumePreservingBijection
        (U := (J.rowInContext x).underlying.obj) (V := W.underlying.obj)
        (Map.id (J.rowInContext x).underlying.obj.domain) Function.bijective_id hCoord))
    hCoord (fun _ => rfl)

def coordinateSelectedCoefficientProductRowIso (x : Fin n → VFType (M := M)) :
    RVVolumeIso ((coordinateSelectedCoefficientFamily F U σ hσ).rowInContext x)
      ((positiveVolumeCoefficientInContext U x).prod (F.rowInContext x)) := by
  let D := vfParameterVolumeContext C x
  exact (coordinateSelectedCoefficientDefinableRowIso hc F U σ hσ x).trans hc D
    ((volumeFamilyPositiveCoefficientRowIso hc F.toDefinable U x).trans hc D
      ((RVVolumeIso.refl hc D (positiveVolumeCoefficientInContext U x)).prod hc D
        ((selectedToDefinableVolumeRowIso hc F x).symm hc D)))

def coordinateSelectedCoefficientSelectedRowIso (x : Fin n → VFType (M := M)) :
    RVVolumeIso ((coordinateSelectedCoefficientFamily F U σ hσ).rowInContext x)
      ((selectedVolumeFamilyLeftProduct U F).rowInContext x) :=
  (coordinateSelectedCoefficientProductRowIso hc F U σ hσ x).trans hc (vfParameterVolumeContext C x)
    ((selectedVolumeFamilyLeftProductRowIso hc U F x).symm hc (vfParameterVolumeContext C x))
end IntegrationInACVF.Section7
