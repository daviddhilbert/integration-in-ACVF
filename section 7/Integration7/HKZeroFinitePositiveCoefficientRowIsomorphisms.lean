import Integration7.HKZeroFinitePositiveCoefficientRowMaps
import Integration7.HKAEZeroPositiveCoefficientProducts

/-! Deleting the functional density graph preserves all coefficient coordinates and both density factors. The resulting full volume isomorphism compares the finite-label presentation with the actual AE product. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section5 (RV carrier)
namespace IntegrationInACVF.Section7.HK
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n a d p : ℕ}
variable (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
variable (F : ZeroVFVolumeFamily C (n+1) a)
variable (R : SpecialTransformations.Section5.DefSet (M := M) (C.base : Set M) 0 d)
variable (σ : Fin (p+1) → Fin d) (ε : Fin d)
variable (hR : ∀ t : Fin (p+1) → RV (M := M),
  {r : Fin d → RV (M := M) | (Fin.elim0,r) ∈ carrier R ∧ r ∘ σ=t}.Finite)
variable (hε : ∀ q : R, (q.val.2 ε).val ≠ iRVZero)
variable (x : Fin (n+1) → VFType (M := M))

def zeroFinitePositiveCoefficientRowIso :
    RVVolumeIso
      ((finiteVolumeCoefficientFamily hc C F.fullVFObject.densityGraph.domain
        F.fullVFObject.densityGraph.finite_labels F.fullVFObject.densityGraph.form R σ ε hR hε).rowInContext x)
      ((F.mulConstant (nativeCoordinateDensityVolumeObject hc C R σ ε hR hε)).rowInContext x) := by
  let U := nativeCoordinateDensityVolumeObject hc C R σ ε hR hε
  let A := F.fullVFObject.densityGraph.domain
  let J := finiteVolumeCoefficientFamily hc C A F.fullVFObject.densityGraph.finite_labels
    F.fullVFObject.densityGraph.form R σ ε hR hε
  let f := zeroFinitePositiveCoefficientRowProjection hc C F R σ ε hR hε x
  have hf := zero_finite_positive_coefficient_row_projection_bijective hc C F R σ ε hR hε x
  have hTarget (r : (J.rowInContext x).underlying.obj.domain) :
      (ordinaryFamilyPositiveCoefficientProjection F.toOrdinary U ⟨(x,(f r).val),(f r).property⟩).val =
        r.val ∘ Fin.natAdd (a+1) := by
    have h := congrArg Prod.snd (mixed_rv_factor_unpack_value F.domain U.underlying.obj.domain
      ⟨(x,(f r).val),(f r).property⟩)
    change (ordinaryFamilyPositiveCoefficientProjection F.toOrdinary U ⟨(x,(f r).val),(f r).property⟩).val =
      (f r).val ∘ Fin.natAdd a at h
    rw [h,zero_finite_positive_coefficient_row_projection_value]
    funext i
    simp only [Function.comp_apply,Fin.append_right]
  have hCoord (r : (J.rowInContext x).underlying.obj.domain) :
      ((F.mulConstant U).rowInContext x).underlying.obj.value (f r)=(J.rowInContext x).underlying.obj.value r :=
    congrArg (fun v => v ∘ σ) (hTarget r)
  have hForm (r : (J.rowInContext x).underlying.obj.domain) :
      ((F.mulConstant U).rowInContext x).form.value (f r)=(J.rowInContext x).form.value r := by
    have hSource := congrArg Prod.snd (mixed_rv_factor_unpack_value A U.underlying.obj.domain ⟨(x,r.val),r.property⟩)
    let t := mixedRVFactorUnpack F.domain U.underlying.obj.domain ⟨(x,(f r).val),(f r).property⟩
    let v := mixedRVFactorUnpack A U.underlying.obj.domain ⟨(x,r.val),r.property⟩
    change F.form.value (Map.prodFst _ _ t) * U.form.value (Map.prodSnd _ _ t) =
      F.fullVFObject.densityGraph.form.value (Map.prodFst _ _ v) * U.form.value (Map.prodSnd _ _ v)
    congr 1
    · change F.form.value (Map.prodFst _ _ t) =
        F.form.value (densityGraphProjection F.fullVFObject.form (Map.prodFst _ _ v))
      congr 1
      apply Subtype.ext
      rw [densityGraphProjection_value]
      have hT := congrArg Prod.fst (mixed_rv_factor_unpack_value F.domain U.underlying.obj.domain
        ⟨(x,(f r).val),(f r).property⟩)
      have hV := congrArg Prod.fst (mixed_rv_factor_unpack_value A U.underlying.obj.domain ⟨(x,r.val),r.property⟩)
      change (Map.prodFst _ _ t).val=(x,(f r).val ∘ Fin.castAdd d) at hT
      change (Map.prodFst _ _ v).val=(x,r.val ∘ Fin.castAdd d) at hV
      have hLabels : (f r).val ∘ Fin.castAdd d = (r.val ∘ Fin.castAdd d) ∘ Fin.castAdd 1 := by
        rw [zero_finite_positive_coefficient_row_projection_value]
        funext i
        simp only [Function.comp_apply,Fin.append_left]
      exact hT.trans ((congrArg (fun z : Fin a → RV (M := M) => (x,z)) hLabels).trans
        (congrArg (fun z : (Fin (n+1) → VFType (M := M)) × (Fin (a+1) → RV (M := M)) =>
          (z.1,z.2 ∘ Fin.castAdd 1)) hV).symm)
    · change (ordinaryFamilyPositiveCoefficientProjection F.toOrdinary U ⟨(x,(f r).val),(f r).property⟩).val ε =
        (mixedRVFactorUnpack A U.underlying.obj.domain ⟨(x,r.val),r.property⟩).val.2 ε
      exact (congrFun (hTarget r) ε).trans (congrFun hSource ε).symm
  exact RVVolumeIso.of_preserving_coordinates_full hc (vfParameterVolumeContext C x)
    (rvFiniteIsoOfAmbient (rvIsoOfVolumePreservingBijection f hf hCoord)) hCoord hForm

def zeroFinitePositiveCoefficientSelectedRowIso :
    RVVolumeIso
      ((finiteVolumeCoefficientFamily hc C F.fullVFObject.densityGraph.domain
        F.fullVFObject.densityGraph.finite_labels F.fullVFObject.densityGraph.form R σ ε hR hε).rowInContext x)
      ((selectedZeroFamilyPositiveProduct (nativeCoordinateDensityVolumeObject hc C R σ ε hR hε) F).rowInContext x) :=
  (zeroFinitePositiveCoefficientRowIso hc C F R σ ε hR hε x).trans hc (vfParameterVolumeContext C x)
    ((F.mulConstant (nativeCoordinateDensityVolumeObject hc C R σ ε hR hε)).selectionRowIso hc x)
end IntegrationInACVF.Section7.HK
