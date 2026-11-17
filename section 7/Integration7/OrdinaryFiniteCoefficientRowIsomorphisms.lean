module

public import Integration7.OrdinaryFiniteCoefficientRowMaps
public import Integration7.AEOrdinaryPositiveCoefficientProducts

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! Removing the ordinary unit graph preserves every actual coefficient
coordinate and its density. The resulting full volume isomorphism compares
the finite-label coefficient presentation with the standard AE product. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section5 (RV carrier)
namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n a d p : ℕ}
variable (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
variable (F : OrdinaryVFVolumeFamily C (n+1) a)
variable (R : SpecialTransformations.Section5.DefSet (M := M) (C.base : Set M) 0 d)
variable (σ : Fin (p+1) → Fin d) (ε : Fin d)
variable (hR : ∀ t : Fin (p+1) → RV (M := M),
  {r : Fin d → RV (M := M) | (Fin.elim0,r) ∈ carrier R ∧ r ∘ σ=t}.Finite)
variable (hε : ∀ q : R, (q.val.2 ε).val ≠ iRVZero)
variable (x : Fin (n+1) → VFType (M := M))

def ordinaryFiniteCoefficientRowIso :
    RVVolumeIso
      ((finiteVolumeCoefficientFamily hc C F.fullVFObject.densityGraph.domain
        F.fullVFObject.densityGraph.finite_labels F.fullVFObject.densityGraph.form R σ ε hR hε).rowInContext x)
      ((F.mulConstant (nativeCoordinateDensityVolumeObject hc C R σ ε hR hε)).rowInContext x) := by
  let U := nativeCoordinateDensityVolumeObject hc C R σ ε hR hε
  let A := F.fullVFObject.densityGraph.domain
  let J := finiteVolumeCoefficientFamily hc C A F.fullVFObject.densityGraph.finite_labels
    F.fullVFObject.densityGraph.form R σ ε hR hε
  let f := ordinaryFiniteCoefficientRowProjection hc C F R σ ε hR hε x
  have hf := ordinary_finite_coefficient_row_projection_bijective hc C F R σ ε hR hε x
  have hTarget (r : (J.rowInContext x).underlying.obj.domain) :
      (ordinaryFamilyPositiveCoefficientProjection F U ⟨(x,(f r).val),(f r).property⟩).val =
        r.val ∘ Fin.natAdd (a+1) := by
    have h := congrArg Prod.snd (mixed_rv_factor_unpack_value F.domain U.underlying.obj.domain
      ⟨(x,(f r).val),(f r).property⟩)
    change (ordinaryFamilyPositiveCoefficientProjection F U ⟨(x,(f r).val),(f r).property⟩).val =
      (f r).val ∘ Fin.natAdd a at h
    rw [h,ordinary_finite_coefficient_row_projection_value]
    funext i
    simp only [Function.comp_apply,Fin.append_right]
  have hCoord (r : (J.rowInContext x).underlying.obj.domain) :
      ((F.mulConstant U).rowInContext x).underlying.obj.value (f r)=(J.rowInContext x).underlying.obj.value r :=
    congrArg (fun v => v ∘ σ) (hTarget r)
  have hForm (r : (J.rowInContext x).underlying.obj.domain) :
      ((F.mulConstant U).rowInContext x).form.value (f r)=(J.rowInContext x).form.value r := by
    have hSource := congrArg Prod.snd (mixed_rv_factor_unpack_value A U.underlying.obj.domain ⟨(x,r.val),r.property⟩)
    change (ordinaryFamilyPositiveCoefficientProjection F U ⟨(x,(f r).val),(f r).property⟩).val ε =
      1 * (mixedRVFactorUnpack A U.underlying.obj.domain ⟨(x,r.val),r.property⟩).val.2 ε
    rw [hTarget,hSource,one_mul]
    rfl
  exact RVVolumeIso.of_preserving_coordinates_full hc (vfParameterVolumeContext C x)
    (rvFiniteIsoOfAmbient (rvIsoOfVolumePreservingBijection f hf hCoord)) hCoord hForm

def ordinaryFiniteCoefficientSelectedRowIso :
    RVVolumeIso
      ((finiteVolumeCoefficientFamily hc C F.fullVFObject.densityGraph.domain
        F.fullVFObject.densityGraph.finite_labels F.fullVFObject.densityGraph.form R σ ε hR hε).rowInContext x)
      ((selectedOrdinaryFamilyPositiveProduct (nativeCoordinateDensityVolumeObject hc C R σ ε hR hε) F).rowInContext x) :=
  (ordinaryFiniteCoefficientRowIso hc C F R σ ε hR hε x).trans hc (vfParameterVolumeContext C x)
    ((F.mulConstant (nativeCoordinateDensityVolumeObject hc C R σ ε hR hε)).selectionRowIso hc x)
end IntegrationInACVF.Section7
