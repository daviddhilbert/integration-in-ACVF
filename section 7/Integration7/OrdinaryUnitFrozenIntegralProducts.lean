module

public import Integration7.OrdinaryUnitFieldIntegralProducts
public import Integration7.OrdinaryUnitSelectedPointRows
public import Integration7.FrozenHeadAppendedIntegralIndependence
public import Integration7.FrozenOrdinaryHeadIntegralValues

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! Freezing an ordinary unit presentation commutes with its actual
density graph. The point-coefficient family's frozen integral is
therefore the point times the genuine ordinary frozen integral. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry
namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n a : ℕ}
variable (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)

def ordinaryFrozenUnitSelectedRowIso (F : OrdinaryVFVolumeFamily C (n+1) a)
    (x : Fin n → VFType (M := M)) (y : Fin 1 → VFType (M := M)) :
    RVVolumeIso (((F.unitSelectedFamily).frozenHeadFamily hc x).rowInContext y)
      (((F.frozenHeadFamily hc x).unitSelectedFamily).rowInContext y) := by
  let D := frozenHeadVolumeContext hc C x
  let U := ((F.unitSelectedFamily).frozenHeadFamily hc x).rowInContext y
  let V := ((F.frozenHeadFamily hc x).unitSelectedFamily).rowInContext y
  have hUV : U.underlying.obj.domain.carrier=V.underlying.obj.domain.carrier := by
    ext r
    change (Fin.cons (y 0) x,r) ∈ (volumeDensityGraph F.fullVFObject.form).carrier ↔
      (y,r) ∈ (volumeDensityGraph (F.frozenHeadFamily hc x).fullVFObject.form).carrier
    rw [volume_density_graph_mem_iff,volume_density_graph_mem_iff]
    rfl
  have hCoord (u : U.underlying.obj.domain) : V.underlying.obj.value ⟨u.val,hUV.le u.property⟩=U.underlying.obj.value u := rfl
  let e : U.underlying ≅ V.underlying := rvFiniteIsoOfAmbient (U := U.underlying) (V := V.underlying)
    (rvIsoOfCarrierEq U.underlying.obj.domain V.underlying.obj.domain U.underlying.obj.volume V.underlying.obj.volume hUV hCoord)
  exact RVVolumeIso.of_preserving_coordinates_full hc (vfParameterVolumeContext D y) e hCoord (fun _ => rfl)

variable (Ξ : Set (Values.Gamma (M := M))) (hΞ : Cardinal.mk Ξ < C.κ)
variable (hNames : commonRealNames (⟨(C.base : Set M),Ξ⟩ : Base (M := M)) ⊆ (C.base : Set M))
variable (γ : Values.Gamma (M := M)) (hγ : γ ∈ Ξ) (hγ1 : 1 < γ)
include hΞ hNames γ hγ hγ1

theorem ordinary_unit_selected_frozen_head_integral (F : OrdinaryVFVolumeFamily C (n+1) a)
    (x : Fin n → VFType (M := M)) :
    selectedFamilyFrozenHeadAppendedIntegral hc C Ξ F.unitSelectedFamily x =
      rvVolumeBlowupClassesProduct hc (frozenHeadVolumeContext hc C x) 1 1
        (positiveVolumeBlowupClass hc (frozenHeadVolumeContext hc C x)
          (degreeOnePointVolumeObject ((frozenHeadVolumeContext hc C x).base : Set M)))
        (ordinaryFamilyFrozenHeadIntegral hc C Ξ F x) := by
  let D := frozenHeadVolumeContext hc C x
  let FBase := definablyClosedVolumeContextField hc (vfParameterVolumeContext C x)
  let hNamesD := frozen_head_volume_context_common_names hc C Ξ hNames x
  have h := selected_family_field_appended_integral_independent hc D Ξ hΞ FBase hNamesD γ hγ hγ1
    ((F.unitSelectedFamily).frozenHeadFamily hc x) ((F.frozenHeadFamily hc x).unitSelectedFamily)
    (fun y => VolumeBlowupEquivalent.of_iso (vfParameterVolumeContext D y) (ordinaryFrozenUnitSelectedRowIso hc C F x y))
  exact h.trans (ordinary_unit_selected_field_appended_integral hc D Ξ hΞ FBase hNamesD γ hγ hγ1 (F.frozenHeadFamily hc x))

theorem ordinary_point_product_frozen_head_integral (F : OrdinaryVFVolumeFamily C (n+1) a)
    (x : Fin n → VFType (M := M)) :
    selectedFamilyFrozenHeadAppendedIntegral hc C Ξ
      (selectedOrdinaryFamilyPositiveProduct (degreeOnePointVolumeObject (C.base : Set M)) F) x =
      rvVolumeBlowupClassesProduct hc (frozenHeadVolumeContext hc C x) 1 1
        (positiveVolumeBlowupClass hc (frozenHeadVolumeContext hc C x)
          (degreeOnePointVolumeObject ((frozenHeadVolumeContext hc C x).base : Set M)))
        (ordinaryFamilyFrozenHeadIntegral hc C Ξ F x) := by
  have h := selected_family_frozen_head_appended_integral_independent hc C Ξ hΞ hNames γ hγ hγ1
    F.unitSelectedFamily (selectedOrdinaryFamilyPositiveProduct (degreeOnePointVolumeObject (C.base : Set M)) F)
    (fun z => VolumeBlowupEquivalent.of_iso (vfParameterVolumeContext C z) (ordinaryUnitSelectedPointRowIso F hc z)) x
  exact h.symm.trans (ordinary_unit_selected_frozen_head_integral hc C Ξ hΞ hNames γ hγ hγ1 F x)
end IntegrationInACVF.Section7
