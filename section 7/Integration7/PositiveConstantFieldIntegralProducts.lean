module

public import Integration7.CoordinateCoefficientFieldIntegralProducts
public import Integration7.ConstantCoefficientIntegralDensityGraphs
public import Integration7.RVCoordinateDensityPresentations

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! The chosen unary field-base appended integral commutes with every
positive constant RV coefficient and every positive selected family.
Both literal-coordinate reductions are justified by full volume isomorphisms. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section5
namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {a k p : ℕ}
variable (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
variable (Ξ : Set (Values.Gamma (M := M))) (hΞ : Cardinal.mk Ξ < C.κ)
variable (FBase : VFFieldBase (C.base : Set M))
variable (hNames : commonRealNames (⟨(C.base : Set M),Ξ⟩ : Base (M := M)) ⊆ (C.base : Set M))
variable (γ : Values.Gamma (M := M)) (hγ : γ ∈ Ξ) (hγ1 : 1 < γ)
include hΞ hNames γ hγ hγ1

set_option maxHeartbeats 1600000 in
theorem retained_family_field_appended_integral_positive_coefficient
    (F : SelectedVFVolumeFamily C 1 a k) (δ : Fin a)
    (hF : ∀ q : F.domain, F.form.value q=q.val.2 δ)
    (hδ : ∀ q ∈ F.domain.carrier, (q.2 δ).val ≠ iRVZero)
    (U : PositiveRVVolumeObject (M := M) (C.base : Set M) p) :
    selectedFamilyFieldAppendedIntegral hc C Ξ FBase (selectedVolumeFamilyLeftProduct U F) =
      rvVolumeBlowupClassesProduct hc C (p+1) ((k+1)+1) (positiveVolumeBlowupClass hc C U)
        (selectedFamilyFieldAppendedIntegral hc C Ξ FBase F) := by
  let R := rvCoordinateDensityNativeDomain hc C U
  let σ : Fin (p+1) → Fin ((p+1)+(U.underlying.obj.arity+1)) := Fin.castAdd (U.underlying.obj.arity+1)
  let ε := Fin.natAdd (p+1) (Fin.last U.underlying.obj.arity)
  let hR := rv_coordinate_density_native_finite hc C U
  let hε := rv_coordinate_density_native_nonzero hc C U
  let V := rvCoordinateDensityNativeObject hc C U
  let e := rvCoordinateDensityNativeIso hc C U
  calc
    selectedFamilyFieldAppendedIntegral hc C Ξ FBase (selectedVolumeFamilyLeftProduct U F) =
        selectedFamilyFieldAppendedIntegral hc C Ξ FBase (selectedVolumeFamilyLeftProduct V F) :=
      selected_coefficient_field_appended_integral_iso hc C Ξ hΞ FBase hNames γ hγ hγ1 F U V e
    _ = selectedFamilyFieldAppendedIntegral hc C Ξ FBase (nativeCoordinateCoefficientFamily hc C F R σ ε hR hε) :=
      (coordinate_selected_coefficient_field_appended_integral hc C Ξ hΞ FBase hNames γ hγ hγ1 F V σ (fun _ => rfl)).symm
    _ = rvVolumeBlowupClassesProduct hc C (p+1) ((k+1)+1) (positiveVolumeBlowupClass hc C V)
        (selectedFamilyFieldAppendedIntegral hc C Ξ FBase F) :=
      native_coefficient_field_appended_integral_product hc C Ξ hΞ FBase hNames γ hγ hγ1 F δ hF hδ R σ ε hR hε
    _ = _ := by rw [← positiveVolumeBlowupClass_iso hc C e]

theorem selected_family_field_appended_integral_positive_coefficient
    (F : SelectedVFVolumeFamily C 1 a k) (U : PositiveRVVolumeObject (M := M) (C.base : Set M) p) :
    selectedFamilyFieldAppendedIntegral hc C Ξ FBase (selectedVolumeFamilyLeftProduct U F) =
      rvVolumeBlowupClassesProduct hc C (p+1) ((k+1)+1) (positiveVolumeBlowupClass hc C U)
        (selectedFamilyFieldAppendedIntegral hc C Ξ FBase F) := by
  rw [selected_coefficient_field_appended_integral_densityGraph hc C Ξ hΞ FBase hNames γ hγ hγ1 F U]
  rw [retained_family_field_appended_integral_positive_coefficient hc C Ξ hΞ FBase hNames γ hγ hγ1 F.densityGraph
    (Fin.last a) F.densityGraph_form_last F.densityGraph_label_nonzero U]
  rw [← selected_family_field_appended_integral_densityGraph hc C Ξ hΞ FBase hNames γ hγ hγ1 F]
end IntegrationInACVF.Section7
