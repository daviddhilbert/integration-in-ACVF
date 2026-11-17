module

public import Integration7.OrdinaryFamilyPositiveCoefficientRows
public import Integration7.DefinableVolumeFamilySelectionRows
public import Integration7.AEOrdinaryVolumeFunctionAddition
public import Integration7.AERVVolumeFunctionAdditiveStructure
public import Integration7.PositiveVolumeClassExtensions

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! Positive coefficients multiply ordinary-valued AE functions into
positive-valued AE functions. Both quotients are respected on actual rows. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3
open scoped DirectSum

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {C : BaseContext M} {n a p : ℕ}

def selectedOrdinaryFamilyPositiveProduct
    (U : PositiveRVVolumeObject (M := M) (C.base : Set M) p) (F : OrdinaryVFVolumeFamily C n a) :
    SelectedVFVolumeFamily C n ((a+U.underlying.obj.arity)+(p+1)) p := (F.mulConstant U).toSelected

theorem selected_ordinary_family_positive_product_row_class
    (hc : CanonicalStructure.IsCanonical (M := M))
    (U : PositiveRVVolumeObject (M := M) (C.base : Set M) p) (F : OrdinaryVFVolumeFamily C n a)
    (x : Fin n → VFType (M := M)) :
    positiveVolumeBlowupClass hc (vfParameterVolumeContext C x) ((selectedOrdinaryFamilyPositiveProduct U F).rowInContext x) =
      rvVolumeBlowupClass hc (vfParameterVolumeContext C x) (n := 0) (F.rowInContext x) •
        positiveVolumeClassExtend hc C (vfParameterVolumeContext C x)
          (fun _ h => vfParameterVolumeContext_contains C x (Or.inl h)) p (positiveVolumeBlowupClass hc C U) :=
  (positiveVolumeBlowupClass_iso hc _ ((F.mulConstant U).selectionRowIso hc x)).symm.trans
    (ordinary_family_positive_coefficient_row_class hc F U x)

theorem ae_ordinary_positive_coefficient_product_congr
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (U V : PositiveRVVolumeObject (M := M) (C.base : Set M) p)
    (F G : OrdinaryVolumeFunctionPresentation C (n+1)) (hUV : VolumeBlowupEquivalent U V)
    (hFG : AEOrdinaryRVVolumeFunctionEquivalent hc C F G) :
    AERVVolumeFunctionEquivalent hc C ⟨_,selectedOrdinaryFamilyPositiveProduct U F.2⟩
      ⟨_,selectedOrdinaryFamilyPositiveProduct V G.2⟩ := by
  obtain ⟨E,hE,hFG⟩ := hFG
  have hU : positiveVolumeBlowupClass hc C U=positiveVolumeBlowupClass hc C V := Quotient.sound hUV
  refine ⟨E,hE,?_⟩
  intro x hx
  rw [selected_ordinary_family_positive_product_row_class,selected_ordinary_family_positive_product_row_class,
    hU,hFG x hx]

def aeOrdinaryRVVolumeFunctionPositiveCoefficientProduct
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M) (n p : ℕ) :
    PositiveVolumeBlowupClasses hc C p → AEOrdinaryRVVolumeFunction hc C n → AERVVolumeFunction hc C n p :=
  Quotient.map₂ (fun U F => ⟨_,selectedOrdinaryFamilyPositiveProduct U F.2⟩)
    (fun U V hUV F G hFG => ae_ordinary_positive_coefficient_product_congr hc C U V F G hUV hFG)

end IntegrationInACVF.Section7
