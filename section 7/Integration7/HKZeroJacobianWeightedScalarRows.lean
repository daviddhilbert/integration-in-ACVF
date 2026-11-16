import Integration7.HKDefinableRescalingWeightedProducts
import Integration7.HKPositiveVolumeClassScalarExtensions
import Integration7.HKSelectedFamilyWeightedZeroProducts
import Integration7.HKZeroJacobianRowComparison
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
namespace IntegrationInACVF.Section7.HK
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n a b k p : ℕ}

theorem zero_jacobian_row_weighted_scalar_comparison
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    {X Y : DefSet (rawVFSpace (M := M) n) (C.base : Set M)}
    (Z : ZeroRVVolumeObject (M := M) (C.base : Set M))
    (F : ZeroVFVolumeFamily C n a) (H : ZeroVFVolumeFamily C n b)
    (φ : Map X Y) (hφ : Function.Bijective φ)
    (hF : ∀ q : F.domain, q.val.1 ∈ X.carrier) (hH : ∀ q : H.domain, q.val.1 ∈ X.carrier)
    (y : Y)
    (h : rvVolumeBlowupClass hc (vfParameterVolumeContext C (φ.inverse hφ y).val) (n := 0)
        (H.rowInContext (φ.inverse hφ y).val) =
      ((rvVolumeBlowupClass hc (vfParameterVolumeContext C (φ.inverse hφ y).val) (n := 0)
          (zeroVolumeCoefficientInContext Z (φ.inverse hφ y).val))) *
        (rvVolumeBlowupClass hc (vfParameterVolumeContext C (φ.inverse hφ y).val) (n := 0)
          (F.rowInContext (φ.inverse hφ y).val))) :
    rvVolumeBlowupClass hc (vfParameterVolumeContext C y.val) (n := 0)
        ((H.jacobianPushforward φ hφ hH).rowInContext y.val) =
      ((rvVolumeBlowupClass hc (vfParameterVolumeContext C y.val) (n := 0)
          (zeroVolumeCoefficientInContext Z y.val))) *
        (rvVolumeBlowupClass hc (vfParameterVolumeContext C y.val) (n := 0)
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
  let EX := zeroVolumeCoefficientExtend hc (vfParameterVolumeContext C x) D hXD
  let EY := zeroVolumeCoefficientExtend hc CY D hYD
  let R := zeroVolumeClassRescaleDefinable hc D c hDefD h0
  let zX := rvVolumeBlowupClass hc (vfParameterVolumeContext C x) (n := 0) (zeroVolumeCoefficientInContext Z x)
  let zY := rvVolumeBlowupClass hc CY (n := 0) (zeroVolumeCoefficientInContext Z y.val)
  have eh := congrArg R (congrArg EX h)
  rw [map_mul] at eh
  have eh' := eh.trans (zero_rescale_product_right hc D c hDefD h0 (EX zX)
    (EX (rvVolumeBlowupClass hc (vfParameterVolumeContext C x) (n := 0) (F.rowInContext x))))
  have eF : R (EX (rvVolumeBlowupClass hc (vfParameterVolumeContext C x) (n := 0) (F.rowInContext x))) =
      EY (rvVolumeBlowupClass hc CY (n := 0) ((F.jacobianPushforward φ hφ hF).rowInContext y.val)) :=
    Quotient.sound ⟨zeroJacobianRowIso hc C D F φ hφ hF y hXD hYD hDefD⟩
  have eH : R (EX (rvVolumeBlowupClass hc (vfParameterVolumeContext C x) (n := 0) (H.rowInContext x))) =
      EY (rvVolumeBlowupClass hc CY (n := 0) ((H.jacobianPushforward φ hφ hH).rowInContext y.val)) :=
    Quotient.sound ⟨zeroJacobianRowIso hc C D H φ hφ hH y hXD hYD hDefD⟩
  have eZ : EX zX = EY zY := rfl
  apply zero_volume_coefficient_extend_injective_definable hc CY D hYD hD
  rw [map_mul]
  exact eH.symm.trans (eh'.trans (congrArg₂ (fun z v => z*v) eZ eF))
end IntegrationInACVF.Section7.HK
