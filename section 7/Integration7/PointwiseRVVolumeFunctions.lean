module

public import Integration7.SelectedFamilyIntegral

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! Positive homogeneous definable RV-volume functions modulo actual
pointwise common-blowup equality, with their descended integral. This is
the pointwise stage; the paper's larger almost-everywhere quotient is separate. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n k : ℕ}

abbrev SelectedVolumeFunctionPresentation (C : BaseContext M) (n k : ℕ) :=
  Σ a, SelectedVFVolumeFamily C n a k

def pointwiseRVVolumeFunctionSetoid
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M) (n k : ℕ) :
    Setoid (SelectedVolumeFunctionPresentation C n k) where
  r F G := ∀ x, positiveVolumeBlowupClass hc (vfParameterVolumeContext C x) (F.2.rowInContext x) =
    positiveVolumeBlowupClass hc (vfParameterVolumeContext C x) (G.2.rowInContext x)
  iseqv := ⟨fun _ _ => rfl,fun h x => (h x).symm,fun h g x => (h x).trans (g x)⟩

abbrev PointwiseRVVolumeFunction
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M) (n k : ℕ) :=
  Quotient (pointwiseRVVolumeFunctionSetoid hc C n k)

def pointwiseRVVolumeFunctionValue
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (f : PointwiseRVVolumeFunction hc C n k) :
    ∀ x : Fin n → VFType (M := M), PositiveVolumeBlowupClasses hc (vfParameterVolumeContext C x) k :=
  Quotient.lift (fun F x => positiveVolumeBlowupClass hc (vfParameterVolumeContext C x) (F.2.rowInContext x))
    (fun _ _ h => funext h) f

theorem pointwiseRVVolumeFunction_ext
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (f g : PointwiseRVVolumeFunction hc C n k)
    (h : ∀ x, pointwiseRVVolumeFunctionValue hc C f x = pointwiseRVVolumeFunctionValue hc C g x) : f=g := by
  induction f using Quotient.inductionOn with
  | h F =>
    induction g using Quotient.inductionOn with
    | h G => exact Quotient.sound h

def pointwiseRVVolumeFunctionIntegral
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (Ξ : Set (Values.Gamma (M := M))) (hΞ : Cardinal.mk Ξ < C.κ)
    (hGenerated : VFGammaGeneratedBase (⟨(C.base : Set M),Ξ⟩ : Base (M := M)))
    (hNames : commonRealNames (⟨(C.base : Set M),Ξ⟩ : Base (M := M)) ⊆ (C.base : Set M))
    (γ : Values.Gamma (M := M)) (hγ : γ ∈ Ξ) (hγ1 : 1 < γ) :
    PointwiseRVVolumeFunction hc C n k → PositiveVolumeBlowupClasses hc C (appendVolumeDegree n k) :=
  Quotient.lift (fun F => selectedFamilyIntegralValue hc C Ξ hGenerated F.2) (by
    intro F G h
    exact selected_family_integral_value_independent hc C Ξ hΞ hGenerated hNames γ hγ hγ1 F.2 G.2
      (fun x => (positiveVolumeBlowupClass_eq_iff hc (vfParameterVolumeContext C x)).mp (h x)))

theorem pointwise_rv_volume_function_integral_representative
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (Ξ : Set (Values.Gamma (M := M))) (hΞ : Cardinal.mk Ξ < C.κ)
    (hGenerated : VFGammaGeneratedBase (⟨(C.base : Set M),Ξ⟩ : Base (M := M)))
    (hNames : commonRealNames (⟨(C.base : Set M),Ξ⟩ : Base (M := M)) ⊆ (C.base : Set M))
    (γ : Values.Gamma (M := M)) (hγ : γ ∈ Ξ) (hγ1 : 1 < γ)
    (F : SelectedVolumeFunctionPresentation C n k) :
    pointwiseRVVolumeFunctionIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 (Quotient.mk _ F) =
      selectedFamilyIntegralValue hc C Ξ hGenerated F.2 := rfl

end IntegrationInACVF.Section7
