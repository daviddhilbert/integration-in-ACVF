module

public import Integration7.FieldBaseAppendedIntegralAdditivity
public import Integration7.FrozenHeadIntegralValues

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! Freezing a VF tuple respects the actual family sum on every row,
and hence its genuine unary field-base fibre integral is additive. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n a b k : ℕ}

theorem selected_frozen_head_family_row_class
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (F : SelectedVFVolumeFamily C (n+1) a k) (x : Fin n → VFType (M := M)) (y : Fin 1 → VFType (M := M)) :
    positiveVolumeBlowupClass (k := k) hc (vfParameterVolumeContext (frozenHeadVolumeContext hc C x) y)
      ((F.frozenHeadFamily hc x).rowInContext y) =
      positiveVolumeClassExtend hc (vfParameterVolumeContext C (Fin.cons (y 0) x))
        (vfParameterVolumeContext (frozenHeadVolumeContext hc C x) y)
        (head_fibre_row_context_contains C _ x (frozen_head_volume_context_contains hc C x) y) k
        (positiveVolumeBlowupClass (k := k) hc _ (F.rowInContext (Fin.cons (y 0) x))) :=
  (positiveVolumeBlowupClass_iso hc _ (selectedHeadFibreRowIso hc C _ F x
    (frozen_head_volume_context_contains hc C x) y)).symm

theorem selected_frozen_head_sum_row_class
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (F : SelectedVFVolumeFamily C (n+1) a k) (G : SelectedVFVolumeFamily C (n+1) b k)
    (x : Fin n → VFType (M := M)) (y : Fin 1 → VFType (M := M)) :
    positiveVolumeBlowupClass (k := k) hc (vfParameterVolumeContext (frozenHeadVolumeContext hc C x) y)
      (((selectedVolumeFamilySum F G).frozenHeadFamily hc x).rowInContext y) =
      positiveVolumeBlowupClass (k := k) hc (vfParameterVolumeContext (frozenHeadVolumeContext hc C x) y)
        ((selectedVolumeFamilySum (F.frozenHeadFamily hc x) (G.frozenHeadFamily hc x)).rowInContext y) := by
  rw [selected_frozen_head_family_row_class,selected_volume_family_sum_row_class, map_add,
    selected_volume_family_sum_row_class,selected_frozen_head_family_row_class,selected_frozen_head_family_row_class]

theorem selected_family_frozen_head_appended_integral_add
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (Ξ : Set (Values.Gamma (M := M))) (hΞ : Cardinal.mk Ξ < C.κ)
    (hNames : commonRealNames (⟨(C.base : Set M),Ξ⟩ : Base (M := M)) ⊆ (C.base : Set M))
    (γ : Values.Gamma (M := M)) (hγ : γ ∈ Ξ) (hγ1 : 1 < γ)
    (F : SelectedVFVolumeFamily C (n+1) a k) (G : SelectedVFVolumeFamily C (n+1) b k)
    (x : Fin n → VFType (M := M)) :
    selectedFamilyFrozenHeadAppendedIntegral hc C Ξ (selectedVolumeFamilySum F G) x =
      selectedFamilyFrozenHeadAppendedIntegral hc C Ξ F x + selectedFamilyFrozenHeadAppendedIntegral hc C Ξ G x := by
  let D := frozenHeadVolumeContext hc C x
  let hNamesD := frozen_head_volume_context_common_names hc C Ξ hNames x
  let FBase := definablyClosedVolumeContextField hc (vfParameterVolumeContext C x)
  have h := selected_family_field_integral_independent hc D Ξ hΞ FBase hNamesD γ hγ hγ1
    ((selectedVolumeFamilySum F G).frozenHeadFamily hc x)
    (selectedVolumeFamilySum (F.frozenHeadFamily hc x) (G.frozenHeadFamily hc x))
    (fun y => (positiveVolumeBlowupClass_eq_iff (k := k) hc _).mp (selected_frozen_head_sum_row_class hc C F G x y))
  change selectedFamilyFieldAppendedIntegral hc D Ξ FBase ((selectedVolumeFamilySum F G).frozenHeadFamily hc x) =
    selectedFamilyFieldAppendedIntegral hc D Ξ FBase (F.frozenHeadFamily hc x) +
    selectedFamilyFieldAppendedIntegral hc D Ξ FBase (G.frozenHeadFamily hc x)
  apply (canonicalFromAppendedVolumeAddEquiv hc D 0 k).injective
  rw [map_add,selected_family_field_integral_from_appended,selected_family_field_integral_from_appended,
    selected_family_field_integral_from_appended]
  exact h.trans (selected_family_field_canonical_integral_add hc D Ξ hΞ FBase hNamesD γ hγ hγ1 _ _)
end IntegrationInACVF.Section7
