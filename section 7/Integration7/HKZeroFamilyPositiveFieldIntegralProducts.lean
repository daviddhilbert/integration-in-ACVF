module

public import Integration7.HKZeroFinitePositiveCoefficientRowIsomorphisms
public import Integration7.FiniteCoefficientUnaryFieldIntegrals
public import Integration7.FieldBaseAppendedIntegralIndependence
public import Integration7.RVCoordinateDensityPresentations

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! Every positive coefficient commutes with the actual unary field-base integral of a weighted-zero-valued family. Both densities survive the genuine product chart and row comparisons. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
namespace IntegrationInACVF.Section7.HK
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {a p : ℕ}
variable (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
variable (Ξ : Set (Values.Gamma (M := M))) (hΞ : Cardinal.mk Ξ < C.κ)
variable (FBase : VFFieldBase (C.base : Set M))
variable (hNames : commonRealNames (⟨(C.base : Set M),Ξ⟩ : Base (M := M)) ⊆ (C.base : Set M))
variable (γ : Values.Gamma (M := M)) (hγ : γ ∈ Ξ) (hγ1 : 1 < γ)
include hΞ hNames γ hγ hγ1

theorem zero_coefficient_field_appended_integral_iso
    (F : ZeroVFVolumeFamily C 1 a)
    (U V : PositiveRVVolumeObject (M := M) (C.base : Set M) p) (e : RVVolumeIso U V) :
    selectedFamilyFieldAppendedIntegral hc C Ξ FBase (selectedZeroFamilyPositiveProduct U F) =
      selectedFamilyFieldAppendedIntegral hc C Ξ FBase (selectedZeroFamilyPositiveProduct V F) := by
  apply selected_family_field_appended_integral_independent hc C Ξ hΞ FBase hNames γ hγ hγ1
  intro x
  apply (positiveVolumeBlowupClass_eq_iff hc (vfParameterVolumeContext C x)).mp
  rw [selected_zero_family_positive_product_row_class,selected_zero_family_positive_product_row_class,
    positiveVolumeBlowupClass_iso hc C e]

set_option maxHeartbeats 1600000 in
theorem zero_family_field_appended_integral_positive_coefficient
    (F : ZeroVFVolumeFamily C 1 a)
    (U : PositiveRVVolumeObject (M := M) (C.base : Set M) p) :
    selectedFamilyFieldAppendedIntegral hc C Ξ FBase (selectedZeroFamilyPositiveProduct U F) =
      rvVolumeBlowupClassesProduct hc C (p+1) 1 (positiveVolumeBlowupClass hc C U)
        (unaryFieldVolumeIntegral hc C Ξ FBase F.fullVFObject) := by
  let R := rvCoordinateDensityNativeDomain hc C U
  let σ : Fin (p+1) → Fin ((p+1)+(U.underlying.obj.arity+1)) := Fin.castAdd (U.underlying.obj.arity+1)
  let ε := Fin.natAdd (p+1) (Fin.last U.underlying.obj.arity)
  let hR := rv_coordinate_density_native_finite hc C U
  let hε := rv_coordinate_density_native_nonzero hc C U
  let V := rvCoordinateDensityNativeObject hc C U
  let e := rvCoordinateDensityNativeIso hc C U
  let J := finiteVolumeCoefficientFamily hc C F.fullVFObject.densityGraph.domain
    F.fullVFObject.densityGraph.finite_labels F.fullVFObject.densityGraph.form R σ ε hR hε
  calc
    selectedFamilyFieldAppendedIntegral hc C Ξ FBase (selectedZeroFamilyPositiveProduct U F) =
        selectedFamilyFieldAppendedIntegral hc C Ξ FBase (selectedZeroFamilyPositiveProduct V F) :=
      zero_coefficient_field_appended_integral_iso hc C Ξ hΞ FBase hNames γ hγ hγ1 F U V e
    _ = selectedFamilyFieldAppendedIntegral hc C Ξ FBase J :=
      (selected_family_field_appended_integral_independent hc C Ξ hΞ FBase hNames γ hγ hγ1 J
        (selectedZeroFamilyPositiveProduct V F)
        (fun x => VolumeBlowupEquivalent.of_iso (vfParameterVolumeContext C x)
          (zeroFinitePositiveCoefficientSelectedRowIso hc C F R σ ε hR hε x))).symm
    _ = rvVolumeBlowupClassesProduct hc C (p+1) 1 (positiveVolumeBlowupClass hc C V)
        (unaryFieldVolumeIntegral hc C Ξ FBase F.fullVFObject) :=
      finite_coefficient_unary_field_integral_product hc C Ξ hΞ FBase hNames γ hγ hγ1 F.fullVFObject R σ ε hR hε
    _ = _ := by rw [← positiveVolumeBlowupClass_iso hc C e]
end IntegrationInACVF.Section7.HK
