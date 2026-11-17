module

public import Integration7.DefinablyClosedVolumeContexts
public import Integration7.FieldBaseVolumeFamilyIntegrals
public import Integration7.SelectedHeadFibreRows
public import Integration7.BlowupParameterExtension

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! Genuine unary fibre integrals in the definable closure of the
original context and frozen VF tuple. No extra Gamma representative,
VF/Gamma generation, or assumed fibre integral is introduced. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n a b k : ℕ}

def frozenHeadVolumeContext (hc : CanonicalStructure.IsCanonical (M := M))
    (C : BaseContext M) (x : Fin n → VFType (M := M)) : BaseContext M :=
  definablyClosedVolumeContext hc (vfParameterVolumeContext C x)

theorem frozen_head_volume_context_contains (hc : CanonicalStructure.IsCanonical (M := M))
    (C : BaseContext M) (x : Fin n → VFType (M := M)) :
    ((vfParameterVolumeContext C x).base : Set M) ⊆ ((frozenHeadVolumeContext hc C x).base : Set M) :=
  definably_closed_volume_context_contains hc _

theorem frozen_head_volume_context_common_names (hc : CanonicalStructure.IsCanonical (M := M))
    (C : BaseContext M) (Ξ : Set (Values.Gamma (M := M)))
    (hNames : commonRealNames (⟨(C.base : Set M),Ξ⟩ : Base (M := M)) ⊆ (C.base : Set M))
    (x : Fin n → VFType (M := M)) :
    commonRealNames (⟨((frozenHeadVolumeContext hc C x).base : Set M),Ξ⟩ : Base (M := M)) ⊆
      ((frozenHeadVolumeContext hc C x).base : Set M) := by
  rintro d (hd | hd)
  · exact hd
  · exact frozen_head_volume_context_contains hc C x
      (vfParameterVolumeContext_contains C x (Or.inl (hNames (Or.inr hd))))

def SelectedVFVolumeFamily.frozenHeadFamily
    (hc : CanonicalStructure.IsCanonical (M := M)) {C : BaseContext M}
    (F : SelectedVFVolumeFamily C (n+1) a k) (x : Fin n → VFType (M := M)) :
    SelectedVFVolumeFamily (frozenHeadVolumeContext hc C x) 1 a k :=
  (F.headFibre x).extendContext (frozen_head_volume_context_contains hc C x)

def selectedFamilyFrozenHeadIntegral
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (Ξ : Set (Values.Gamma (M := M)))
    (F : SelectedVFVolumeFamily C (n+1) a k) (x : Fin n → VFType (M := M)) :
    PositiveVolumeBlowupClasses hc (frozenHeadVolumeContext hc C x) (k+1) :=
  selectedFamilyFieldCanonicalIntegral hc (frozenHeadVolumeContext hc C x) Ξ
    (definablyClosedVolumeContextField hc (vfParameterVolumeContext C x)) (F.frozenHeadFamily hc x)

theorem selected_family_frozen_head_integral_independent
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (Ξ : Set (Values.Gamma (M := M))) (hΞ : Cardinal.mk Ξ < C.κ)
    (hNames : commonRealNames (⟨(C.base : Set M),Ξ⟩ : Base (M := M)) ⊆ (C.base : Set M))
    (γ : Values.Gamma (M := M)) (hγ : γ ∈ Ξ) (hγ1 : 1 < γ)
    (F : SelectedVFVolumeFamily C (n+1) a k) (G : SelectedVFVolumeFamily C (n+1) b k)
    (hCommon : ∀ z, VolumeBlowupEquivalent (F.rowInContext z) (G.rowInContext z))
    (x : Fin n → VFType (M := M)) :
    selectedFamilyFrozenHeadIntegral hc C Ξ F x = selectedFamilyFrozenHeadIntegral hc C Ξ G x := by
  let D := frozenHeadVolumeContext hc C x
  let hD := frozen_head_volume_context_contains hc C x
  apply selected_family_field_integral_independent hc D Ξ hΞ
    (definablyClosedVolumeContextField hc (vfParameterVolumeContext C x))
    (frozen_head_volume_context_common_names hc C Ξ hNames x) γ hγ hγ1
  intro y
  have eF := selectedHeadFibreRowIso hc C D F x hD y
  have eG := selectedHeadFibreRowIso hc C D G x hD y
  have h := (hCommon (Fin.cons (y 0) x)).extend (head_fibre_row_context_contains C D x hD y)
  exact (VolumeBlowupEquivalent.of_iso (vfParameterVolumeContext D y) (eF.symm hc _)).trans hc _
    (h.trans hc _ (VolumeBlowupEquivalent.of_iso (vfParameterVolumeContext D y) eG))

end IntegrationInACVF.Section7
