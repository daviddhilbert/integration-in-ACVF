module

public import Integration7.HKZeroJacobianRowIsomorphisms
public import Integration7.DefinableBaseMapValues

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! The actual Jacobian transform respects the exact weighted-zero fibre
isomorphism relation. Inverse images and the Jacobian value are definable over
the target tuple, so all extra names can be eliminated again. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.DefinableGeometry

namespace IntegrationInACVF.Section7.HK
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n a b k : ℕ}

theorem zero_jacobian_row_comparison
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    {X Y : DefSet (rawVFSpace (M := M) n) (C.base : Set M)}
    (F : ZeroVFVolumeFamily C n a) (G : ZeroVFVolumeFamily C n b)
    (φ : Map X Y) (hφ : Function.Bijective φ)
    (hF : ∀ p : F.domain, p.val.1 ∈ X.carrier) (hG : ∀ p : G.domain, p.val.1 ∈ X.carrier)
    (y : Y)
    (h : Nonempty (ZeroRVVolumeIso (F.rowInContext (φ.inverse hφ y).val)
      (G.rowInContext (φ.inverse hφ y).val))) :
    Nonempty (ZeroRVVolumeIso ((F.jacobianPushforward φ hφ hF).rowInContext y.val)
      ((G.jacobianPushforward φ hφ hG).rowInContext y.val)) := by
  let CY := vfParameterVolumeContext C y.val
  let x := (φ.inverse hφ y).val
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
  have eF := zeroJacobianRowIso hc C D F φ hφ hF y hXD hYD hDefD
  have eG := zeroJacobianRowIso hc C D G φ hφ hG y hXD hYD hDefD
  let hScaled := (h.some.extend hXD).rescaleDefinable c hDefD h0
  let hCommon := eF.symm.trans (hScaled.trans eG)
  exact ⟨hCommon.descendDefinableNames hYD hD⟩

end IntegrationInACVF.Section7.HK
