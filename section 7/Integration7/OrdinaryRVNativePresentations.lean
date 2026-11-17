module

public import Integration7.NativeOrdinaryRVVolumeFactors
public import Integration7.AllDegreeVolumeClasses
public import Section4.RVIsoTools

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! The literal native presentation of an ordinary RV[0] coefficient
has the same actual finite object and the same ordinary class. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.DefinableGeometry
namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

def ordinaryRVNativeIso (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (Z : RVFiniteObject (M := M) (C.base : Set M) 0) :
    nativeOrdinaryRVObject hc C (ordinaryRVNativeDomain hc C Z) (ordinary_rv_native_labels_finite hc C Z) ≅ Z :=
  rvFiniteIsoOfAmbient (rvIsoOfCarrierEq _ _ _ _ (ordinary_rv_native_labels_carrier hc C Z)
    (fun _ => funext (fun i => Fin.elim0 i)))

theorem ordinary_rv_native_class (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (Z : RVFiniteObject (M := M) (C.base : Set M) 0) :
    rvVolumeBlowupClass hc C (n := 0)
      (nativeOrdinaryRVObject hc C (ordinaryRVNativeDomain hc C Z) (ordinary_rv_native_labels_finite hc C Z)) =
    rvVolumeBlowupClass hc C (n := 0) Z := Quotient.sound ⟨ordinaryRVNativeIso hc C Z⟩
end IntegrationInACVF.Section7
