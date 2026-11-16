module

public import Integration7.CoordinateSelectedCoefficientRows
public import Integration7.FieldBaseAppendedIntegralIndependence
public import Integration7.SelectedDensityGraphRowMaps

@[expose] public section

/-! Genuine row volume isomorphisms identify the chosen appended
integrals of density-graph and literal-label coefficient presentations. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section5
namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n a k p : ℕ}
variable (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
variable (Ξ : Set (Values.Gamma (M := M))) (hΞ : Cardinal.mk Ξ < C.κ)
variable (FBase : VFFieldBase (C.base : Set M))
variable (hNames : commonRealNames (⟨(C.base : Set M),Ξ⟩ : Base (M := M)) ⊆ (C.base : Set M))
variable (γ : Values.Gamma (M := M)) (hγ : γ ∈ Ξ) (hγ1 : 1 < γ)
include hΞ hNames γ hγ hγ1

theorem selected_family_field_appended_integral_densityGraph (F : SelectedVFVolumeFamily C (n+1) a k) :
    selectedFamilyFieldAppendedIntegral hc C Ξ FBase F =
      selectedFamilyFieldAppendedIntegral hc C Ξ FBase F.densityGraph :=
  selected_family_field_appended_integral_independent hc C Ξ hΞ FBase hNames γ hγ hγ1 F F.densityGraph
    (fun x => VolumeBlowupEquivalent.of_iso (vfParameterVolumeContext C x) (F.densityGraphRowIso hc x))

theorem coordinate_selected_coefficient_field_appended_integral
    (F : SelectedVFVolumeFamily C (n+1) a k)
    (U : PositiveRVVolumeObject (M := M) (C.base : Set M) p)
    (σ : Fin (p+1) → Fin U.underlying.obj.arity)
    (hσ : ∀ u : U.underlying.obj.domain, U.underlying.obj.value u=u.val ∘ σ) :
    selectedFamilyFieldAppendedIntegral hc C Ξ FBase (coordinateSelectedCoefficientFamily F U σ hσ) =
      selectedFamilyFieldAppendedIntegral hc C Ξ FBase (selectedVolumeFamilyLeftProduct U F) :=
  selected_family_field_appended_integral_independent hc C Ξ hΞ FBase hNames γ hγ hγ1 _ _
    (fun x => VolumeBlowupEquivalent.of_iso (vfParameterVolumeContext C x)
      (coordinateSelectedCoefficientSelectedRowIso hc F U σ hσ x))

theorem selected_coefficient_field_appended_integral_iso
    (F : SelectedVFVolumeFamily C (n+1) a k)
    (U V : PositiveRVVolumeObject (M := M) (C.base : Set M) p) (e : RVVolumeIso U V) :
    selectedFamilyFieldAppendedIntegral hc C Ξ FBase (selectedVolumeFamilyLeftProduct U F) =
      selectedFamilyFieldAppendedIntegral hc C Ξ FBase (selectedVolumeFamilyLeftProduct V F) := by
  apply selected_family_field_appended_integral_independent hc C Ξ hΞ FBase hNames γ hγ hγ1
  intro x
  let D := vfParameterVolumeContext C x
  let hCD : (C.base : Set M) ⊆ (D.base : Set M) := fun _ h => vfParameterVolumeContext_contains C x (Or.inl h)
  let ec := (e.extend hCD).prod hc D (RVVolumeIso.refl hc D (F.rowInContext x))
  exact VolumeBlowupEquivalent.of_iso D
    ((selectedVolumeFamilyLeftProductRowIso hc U F x).trans hc D
      (ec.trans hc D ((selectedVolumeFamilyLeftProductRowIso hc V F x).symm hc D)))
end IntegrationInACVF.Section7
