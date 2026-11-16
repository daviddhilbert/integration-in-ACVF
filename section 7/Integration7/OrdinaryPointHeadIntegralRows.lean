module

public import Integration7.OrdinaryUnitFrozenIntegralProducts
public import Integration7.PositiveVolumeClassProductExtensions
public import Integration7.DefinableVolumeParameterDescent

@[expose] public section

/-! Multiplying an ordinary-valued family by the degree-one point
commutes with the actual head integral, on every original-context row. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open IntegrationInACVF.Section5
namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n a : ℕ}

theorem ordinary_point_product_head_integral_row
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (Ξ : Set (Values.Gamma (M := M))) (hΞ : Cardinal.mk Ξ < C.κ)
    (hNames : commonRealNames (⟨(C.base : Set M),Ξ⟩ : Base (M := M)) ⊆ (C.base : Set M))
    (γ : Values.Gamma (M := M)) (hγ : γ ∈ Ξ) (hγ1 : 1 < γ)
    (F : OrdinaryVFVolumeFamily C (n+1) a)
    (T : HeadPreparation (nativeMixedVolumeDomain hc F.fullVFObject.densityGraph.domain))
    (S : HeadPreparation (nativeMixedVolumeDomain hc
      (selectedOrdinaryFamilyPositiveProduct (degreeOnePointVolumeObject (C.base : Set M)) F).densityGraph.domain))
    (x : Fin n → VFType (M := M)) :
    positiveVolumeBlowupClass hc (vfParameterVolumeContext C x)
      (((selectedOrdinaryFamilyPositiveProduct (degreeOnePointVolumeObject (C.base : Set M)) F).headIntegral hc Ξ S).rowInContext x) =
    rvVolumeBlowupClassesProduct hc (vfParameterVolumeContext C x) 1 1
      (positiveVolumeClassExtend hc C (vfParameterVolumeContext C x)
        (fun _ h => vfParameterVolumeContext_contains C x (Or.inl h)) 0
        (positiveVolumeBlowupClass hc C (degreeOnePointVolumeObject (C.base : Set M))))
      (positiveVolumeBlowupClass hc (vfParameterVolumeContext C x) ((F.headIntegral hc Ξ T).rowInContext x)) := by
  apply positive_volume_class_extend_injective_definable hc (vfParameterVolumeContext C x)
    (frozenHeadVolumeContext hc C x) (frozen_head_volume_context_contains hc C x)
    (definably_closed_volume_context_names hc _)
  let CX := vfParameterVolumeContext C x
  let D := frozenHeadVolumeContext hc C x
  let hCX : (C.base : Set M) ⊆ (CX.base : Set M) := fun _ h => vfParameterVolumeContext_contains C x (Or.inl h)
  let hXD := frozen_head_volume_context_contains hc C x
  let uX := positiveVolumeClassExtend hc C CX hCX 0
    (positiveVolumeBlowupClass hc C (degreeOnePointVolumeObject (C.base : Set M)))
  let fX := positiveVolumeBlowupClass hc CX ((F.headIntegral hc Ξ T).rowInContext x)
  have hProduct := positive_volume_class_extend_product hc CX D hXD (p := 0) (q := 0) uX fX
  have hU : positiveVolumeClassExtend hc CX D hXD 0 uX =
      positiveVolumeBlowupClass hc D (degreeOnePointVolumeObject (D.base : Set M)) := rfl
  have hF := ordinary_head_integral_is_frozen_fibre_integral hc C Ξ hΞ hNames γ hγ hγ1 F T x
  have hH := selected_head_integral_is_frozen_fibre_integral hc C Ξ hΞ hNames γ hγ hγ1
    (selectedOrdinaryFamilyPositiveProduct (degreeOnePointVolumeObject (C.base : Set M)) F) S x
  have hIntegral := ordinary_point_product_frozen_head_integral hc C Ξ hΞ hNames γ hγ hγ1 F x
  exact hH.trans (hIntegral.trans ((congrArg₂ (rvVolumeBlowupClassesProduct hc D 1 1) hU.symm hF.symm).trans hProduct.symm))
end IntegrationInACVF.Section7
