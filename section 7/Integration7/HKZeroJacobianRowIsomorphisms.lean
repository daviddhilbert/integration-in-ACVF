module

public import Integration7.HKZeroDefinableDensityRescaling
public import Integration7.HKZeroFamilyJacobianPushforwards
public import Integration7.SelectedVolumeRowContexts
public import Integration7.VolumeRelabeling
public import Section4.RVIsoTools

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! On a fixed target fibre the actual weighted-zero family Jacobian transform is
the original fibre with its density multiplied by the inverse base
Jacobian. The label bijection is the identity on every old RV label. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.DefinableGeometry

namespace IntegrationInACVF.Section7.HK
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n a k : ℕ}

def zeroJacobianRowIso
    (hc : CanonicalStructure.IsCanonical (M := M)) (C D : BaseContext M)
    {X Y : DefSet (rawVFSpace (M := M) n) (C.base : Set M)}
    (F : ZeroVFVolumeFamily C n a) (φ : Map X Y) (hφ : Function.Bijective φ)
    (hF : ∀ p : F.domain, p.val.1 ∈ X.carrier) (y : Y)
    (hXD : ((vfParameterVolumeContext C (φ.inverse hφ y).val).base : Set M) ⊆ (D.base : Set M))
    (hYD : ((vfParameterVolumeContext C y.val).base : Set M) ⊆ (D.base : Set M))
    (hDef : (D.base : Set M).Definable₁ LRV {((pureVFInverseJacobianDensityForm φ hφ).value y).val}) :
    ZeroRVVolumeIso
      (((F.rowInContext (φ.inverse hφ y).val).extend hXD).rescaleDefinable
        ((pureVFInverseJacobianDensityForm φ hφ).value y) hDef
        ((pureVFInverseJacobianDensityForm φ hφ).nonzero y))
      (((F.jacobianPushforward φ hφ hF).rowInContext y.val).extend hYD) := by
  let U := ((F.rowInContext (φ.inverse hφ y).val).extend hXD).rescaleDefinable
    ((pureVFInverseJacobianDensityForm φ hφ).value y) hDef
    ((pureVFInverseJacobianDensityForm φ hφ).nonzero y)
  let V := ((F.jacobianPushforward φ hφ hF).rowInContext y.val).extend hYD
  have hUV : U.underlying.obj.domain.carrier = V.underlying.obj.domain.carrier := by
    ext r
    exact (F.pushforwardBase_fibre φ hφ hF y r).symm
  let e : U.underlying ≅ V.underlying := rvFiniteIsoOfAmbient
    (U := U.underlying) (V := V.underlying) (rvIsoOfCarrierEq U.underlying.obj.domain V.underlying.obj.domain
    U.underlying.obj.volume V.underlying.obj.volume hUV (fun _ => funext (fun i => Fin.elim0 i)))
  refine ⟨e,?_⟩
  intro r
  let p : F.domain := ⟨((φ.inverse hφ y).val,r.val),r.property⟩
  have hq : (mixedVFBaseMap φ F.domain hF).toImage p =
      (⟨(y.val,r.val),hUV.le r.property⟩ : (F.jacobianPushforward φ hφ hF).domain) := by
    apply Subtype.ext
    exact Prod.ext (congrArg Subtype.val (Map.apply_inverse φ hφ y)) rfl
  have h := F.jacobianPushforward_density φ hφ hF p
  rw [hq] at h
  have hBase : φ ⟨p.val.1,hF p⟩ = y := Map.apply_inverse φ hφ y
  rw [hBase] at h
  exact h.symm

end IntegrationInACVF.Section7.HK
