import Integration7.DefinableRescalingProducts
import Integration7.SelectedJacobianRowComparison
import Integration7.SelectedVolumeFamilyPositiveProducts

/-! The actual row Jacobian transform respects multiplication by a
positive constant volume coefficient, over the original target base. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.DefinableGeometry
namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n a b k p : ℕ}

theorem selected_jacobian_row_positive_product_comparison
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    {X Y : DefSet (rawVFSpace (M := M) n) (C.base : Set M)}
    (U : PositiveRVVolumeObject (M := M) (C.base : Set M) p)
    (F : SelectedVFVolumeFamily C n a k) (H : SelectedVFVolumeFamily C n b ((p+1)+k))
    (φ : Map X Y) (hφ : Function.Bijective φ)
    (hF : ∀ q : F.domain, q.val.1 ∈ X.carrier) (hH : ∀ q : H.domain, q.val.1 ∈ X.carrier)
    (y : Y)
    (h : positiveVolumeBlowupClass hc (vfParameterVolumeContext C (φ.inverse hφ y).val)
        (H.rowInContext (φ.inverse hφ y).val) =
      rvVolumeBlowupClassesProduct hc (vfParameterVolumeContext C (φ.inverse hφ y).val) (p+1) (k+1)
        (positiveVolumeBlowupClass hc (vfParameterVolumeContext C (φ.inverse hφ y).val)
          (positiveVolumeCoefficientInContext U (φ.inverse hφ y).val))
        (positiveVolumeBlowupClass hc (vfParameterVolumeContext C (φ.inverse hφ y).val)
          (F.rowInContext (φ.inverse hφ y).val))) :
    positiveVolumeBlowupClass hc (vfParameterVolumeContext C y.val)
        ((H.jacobianPushforward φ hφ hH).rowInContext y.val) =
      rvVolumeBlowupClassesProduct hc (vfParameterVolumeContext C y.val) (p+1) (k+1)
        (positiveVolumeBlowupClass hc (vfParameterVolumeContext C y.val)
          (positiveVolumeCoefficientInContext U y.val))
        (positiveVolumeBlowupClass hc (vfParameterVolumeContext C y.val)
          ((F.jacobianPushforward φ hφ hF).rowInContext y.val)) := by
  let CY := vfParameterVolumeContext C y.val
  let x : Fin n → Transfer.VFType (M := M) := (φ.inverse hφ y).val
  have hCY : (C.base : Set M) ⊆ (CY.base : Set M) :=
    fun _ h => vfParameterVolumeContext_contains C y.val (Or.inl h)
  have hy : ∀ i, (CY.base : Set M).Definable₁ LRV {(y.val i).val} :=
    fun i => Set.Definable.singleton_of_mem LRV
      (vfParameterVolumeContext_contains C y.val (Or.inr (Set.mem_range_self i)))
  have hx : ∀ i, (CY.base : Set M).Definable₁ LRV {(x i).val} :=
    vf_map_value_coordinate_definable ((φ.inverse hφ).extend hCY) ⟨y.val,y.property⟩ hy
  let D := finiteVolumeParameterContext CY (Set.range (fun i => (x i).val)) (Set.finite_range _)
  have hYD : (CY.base : Set M) ⊆ (D.base : Set M) :=
    fun _ h => finiteVolumeParameterContext_contains CY _ _ (Or.inl h)
  have hXD : ((vfParameterVolumeContext C x).base : Set M) ⊆ (D.base : Set M) := by
    apply Substructure.closure_le.mpr
    rintro z (hz | hz)
    · exact hYD (hCY hz)
    · exact finiteVolumeParameterContext_contains CY _ _ (Or.inr hz)
  have hD : ∀ d ∈ (D.base : Set M), (CY.base : Set M).Definable₁ LRV {d} :=
    finite_volume_parameter_context_definable CY _ _ (by rintro d ⟨i,rfl⟩; exact hx i)
  let c := (pureVFInverseJacobianDensityForm φ hφ).value y
  have hDef : (CY.base : Set M).Definable₁ LRV {c.val} :=
    vf_rv_map_value_coordinate_definable
      ((pureVFInverseJacobianDensityForm φ hφ).map.extend hCY) ⟨y.val,y.property⟩ hy 0
  have hDefD : (D.base : Set M).Definable₁ LRV {c.val} := hDef.mono hYD
  have h0 : c ≠ 0 := (pureVFInverseJacobianDensityForm φ hφ).nonzero y
  let EX := positiveVolumeClassExtend hc (vfParameterVolumeContext C x) D hXD
  let EY := positiveVolumeClassExtend hc CY D hYD
  let R (j : ℕ) := positiveVolumeClassRescaleDefinable (k := j) hc D c hDefD h0
  have eh := congrArg (R ((p+1)+k)) (congrArg (EX ((p+1)+k)) h)
  dsimp only [EX,R] at eh
  rw [positive_volume_class_extend_product hc (vfParameterVolumeContext C x) D hXD (p := p) (q := k)] at eh
  have eh' := eh.trans (positive_volume_class_rescale_definable_product hc D c hDefD h0 (p := p) (k := k)
    (EX p (positiveVolumeBlowupClass hc (vfParameterVolumeContext C x) (positiveVolumeCoefficientInContext U x)))
    (EX k (positiveVolumeBlowupClass hc (vfParameterVolumeContext C x) (F.rowInContext x))))
  have eF := positiveVolumeBlowupClass_iso hc D
    (selectedJacobianRowIso hc C D F φ hφ hF y hXD hYD hDefD)
  have eH := positiveVolumeBlowupClass_iso hc D
    (selectedJacobianRowIso hc C D H φ hφ hH y hXD hYD hDefD)
  have eU : EX p (positiveVolumeBlowupClass hc (vfParameterVolumeContext C x)
      (positiveVolumeCoefficientInContext U x)) =
      EY p (positiveVolumeBlowupClass hc CY (positiveVolumeCoefficientInContext U y.val)) :=
    positiveVolumeBlowupClass_iso hc D (RVVolumeIso.of_preserving_coordinates_full hc D
      (rvFiniteIsoOfAmbient (rvIsoOfVolumePreservingBijection (Map.id _) Function.bijective_id (fun _ => rfl)))
      (fun _ => rfl) (fun _ => rfl))
  apply positive_volume_class_extend_injective_definable hc CY D hYD hD
  rw [positive_volume_class_extend_product]
  exact eH.symm.trans (eh'.trans (congrArg₂
    (rvVolumeBlowupClassesProduct hc D (p+1) (k+1)) eU eF))
end IntegrationInACVF.Section7
