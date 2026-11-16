import Integration7.HKZeroFamilyPositiveCoefficients
import Integration7.HKAEZeroModules
import Integration7.DefinableVolumeFamilySelectionRows
import Integration7.AEOrdinaryVolumeFunctionAddition
import Integration7.AERVVolumeFunctionAdditiveStructure
import Integration7.PositiveVolumeClassExtensions

/-! Positive coefficients multiply weighted-zero-valued AE functions into
positive-valued AE functions. Both quotients are respected on actual rows. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3
open scoped DirectSum

namespace IntegrationInACVF.Section7.HK
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {C : BaseContext M} {n a p : ℕ}

def selectedZeroFamilyPositiveProduct
    (U : PositiveRVVolumeObject (M := M) (C.base : Set M) p) (F : ZeroVFVolumeFamily C n a) :
    SelectedVFVolumeFamily C n ((a+U.underlying.obj.arity)+(p+1)) p := (F.mulConstant U).toSelected

theorem selected_zero_family_positive_product_row_class
    (hc : CanonicalStructure.IsCanonical (M := M))
    (U : PositiveRVVolumeObject (M := M) (C.base : Set M) p) (F : ZeroVFVolumeFamily C n a)
    (x : Fin n → VFType (M := M)) :
    positiveVolumeBlowupClass hc (vfParameterVolumeContext C x) ((selectedZeroFamilyPositiveProduct U F).rowInContext x) =
      rvVolumeBlowupClass hc (vfParameterVolumeContext C x) (n := 0) (F.rowInContext x) •
        positiveVolumeClassExtend hc C (vfParameterVolumeContext C x)
          (fun _ h => vfParameterVolumeContext_contains C x (Or.inl h)) p (positiveVolumeBlowupClass hc C U) :=
  (positiveVolumeBlowupClass_iso hc _ ((F.mulConstant U).selectionRowIso hc x)).symm.trans
    (zero_family_positive_coefficient_row_class hc F U x)

theorem ae_zero_positive_coefficient_product_congr
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (U V : PositiveRVVolumeObject (M := M) (C.base : Set M) p)
    (F G : ZeroVolumeFunctionPresentation C (n+1)) (hUV : VolumeBlowupEquivalent U V)
    (hFG : AEZeroVolumeFunctionEquivalent hc C F G) :
    AERVVolumeFunctionEquivalent hc C ⟨_,selectedZeroFamilyPositiveProduct U F.2⟩
      ⟨_,selectedZeroFamilyPositiveProduct V G.2⟩ := by
  obtain ⟨E,hE,hFG⟩ := hFG
  have hU : positiveVolumeBlowupClass hc C U=positiveVolumeBlowupClass hc C V := Quotient.sound hUV
  refine ⟨E,hE,?_⟩
  intro x hx
  rw [selected_zero_family_positive_product_row_class,selected_zero_family_positive_product_row_class,
    hU,hFG x hx]

def aeZeroVolumeFunctionPositiveCoefficientProduct
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M) (n p : ℕ) :
    PositiveVolumeBlowupClasses hc C p → AEZeroVolumeFunction hc C n → AERVVolumeFunction hc C n p :=
  Quotient.map₂ (fun U F => ⟨_,selectedZeroFamilyPositiveProduct U F.2⟩)
    (fun U V hUV F G hFG => ae_zero_positive_coefficient_product_congr hc C U V F G hUV hFG)

end IntegrationInACVF.Section7.HK
