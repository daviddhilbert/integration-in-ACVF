module

public import Integration7.HKZeroJacobianCoproducts

@[expose] public section

/-! The actual weighted-zero Jacobian transform is additive on supported
AE functions. This uses literal coproduct graphs and both original forms. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.DefinableGeometry

namespace IntegrationInACVF.Section7.HK
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n a b : ℕ}

theorem zero_jacobian_sum_row_class
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    {X Y : DefSet (rawVFSpace (M := M) (n+1)) (C.base : Set M)}
    (F : ZeroVFVolumeFamily C (n+1) a) (G : ZeroVFVolumeFamily C (n+1) b)
    (φ : Map X Y) (hφ : Function.Bijective φ)
    (hF : ∀ p : F.domain, p.val.1 ∈ X.carrier) (hG : ∀ p : G.domain, p.val.1 ∈ X.carrier)
    (y : Fin (n+1) → VFType (M := M)) :
    rvVolumeBlowupClass hc (vfParameterVolumeContext C y) (n := 0)
      (((F.coprod G).jacobianPushforward φ hφ (zero_family_coprod_supported F G hF hG)).rowInContext y) =
      rvVolumeBlowupClass hc (vfParameterVolumeContext C y) (n := 0) ((F.jacobianPushforward φ hφ hF).rowInContext y) +
        rvVolumeBlowupClass hc (vfParameterVolumeContext C y) (n := 0) ((G.jacobianPushforward φ hφ hG).rowInContext y) := by
  let A := ((F.coprod G).jacobianPushforward φ hφ (zero_family_coprod_supported F G hF hG)).rowInContext y
  let B := ((F.jacobianPushforward φ hφ hF).coprod (G.jacobianPushforward φ hφ hG)).rowInContext y
  have hAB : A.underlying.obj.domain.carrier = B.underlying.obj.domain.carrier :=
    Set.ext (fun r => Set.ext_iff.mp (zero_jacobian_coprod_domain F G φ hφ hF hG) (y,r))
  let f : Map A.underlying.obj.domain B.underlying.obj.domain := Map.inclusion hAB.le
  have hf : Function.Bijective f := by
    constructor
    · intro u v huv
      have he := congrArg Subtype.val huv
      exact Subtype.ext he
    · intro v
      exact ⟨⟨v.val,hAB.ge v.property⟩,rfl⟩
  have hρ : ∀ u, A.form.value u = B.form.value (f u) := fun u =>
    zero_jacobian_coprod_density F G φ hφ hF hG ⟨(y,u.val),u.property⟩
  exact (show rvVolumeBlowupClass hc (vfParameterVolumeContext C y) (n := 0) A =
      rvVolumeBlowupClass hc (vfParameterVolumeContext C y) (n := 0) B from
    Quotient.sound ⟨ZeroRVVolumeIso.ofBijection f hf hρ⟩).trans
      (zero_family_coprod_row_class hc (F.jacobianPushforward φ hφ hF) (G.jacobianPushforward φ hφ hG) y)

theorem supported_zero_volume_jacobian_map_add
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    {X Y : DefSet (rawVFSpace (M := M) (n+1)) (C.base : Set M)}
    (φ : Map X Y) (hφ : Function.Bijective φ) (f g : SupportedAEZeroVolumeFunction hc C X) :
    supportedZeroVolumeFunctionJacobian hc C φ hφ (f+g) =
      supportedZeroVolumeFunctionJacobian hc C φ hφ f + supportedZeroVolumeFunctionJacobian hc C φ hφ g := by
  induction f using Quotient.inductionOn with
  | h F =>
    induction g using Quotient.inductionOn with
    | h G =>
      apply Quotient.sound
      apply ae_zero_volume_equivalent_of_pointwise hc C
      intro y
      exact (zero_jacobian_sum_row_class hc C F.2.val G.2.val φ hφ F.2.property G.2.property y).trans
        (zero_family_coprod_row_class hc (F.2.val.jacobianPushforward φ hφ F.2.property)
          (G.2.val.jacobianPushforward φ hφ G.2.property) y).symm

def supportedZeroVolumeJacobianAddHom
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    {X Y : DefSet (rawVFSpace (M := M) (n+1)) (C.base : Set M)}
    (φ : Map X Y) (hφ : Function.Bijective φ) :
    SupportedAEZeroVolumeFunction hc C X →+ SupportedAEZeroVolumeFunction hc C Y where
  toFun := supportedZeroVolumeFunctionJacobian hc C φ hφ
  map_zero' := supported_zero_volume_jacobian_map_zero hc C φ hφ
  map_add' := supported_zero_volume_jacobian_map_add hc C φ hφ

end IntegrationInACVF.Section7.HK
