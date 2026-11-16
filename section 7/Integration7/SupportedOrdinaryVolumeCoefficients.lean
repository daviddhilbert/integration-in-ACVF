module

public import Integration7.SupportedVolumeJacobianAddition
public import Integration7.SelectedJacobianRowOrdinaryCoefficients
public import Integration7.AERVVolumeOrdinaryCoefficientModules

@[expose] public section

/-! Supported positive functions form a module over ordinary RV[0]
coefficients, and their actual Jacobian transform is linear over this ring. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.DefinableGeometry
open scoped DirectSum
namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n a k : ℕ}

theorem selected_volume_family_zero_product_supported
    {C : BaseContext M} {X : DefSet (rawVFSpace (M := M) n) (C.base : Set M)}
    (Z : RVFiniteObject (M := M) (C.base : Set M) 0)
    (F : SelectedVFVolumeFamily C n a k) (hF : ∀ q : F.domain, q.val.1 ∈ X.carrier) :
    ∀ q : (F.prodZero Z).domain, q.val.1 ∈ X.carrier := by
  intro q
  have hmem := (mem_mixed_rv_factor_domain F.domain Z.obj.domain q.val.1 q.val.2).mp q.property
  exact hF ⟨(q.val.1,q.val.2 ∘ Fin.castAdd Z.obj.arity),hmem.1⟩

def supportedOrdinaryVolumeCoefficientProduct
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (X : DefSet (rawVFSpace (M := M) (n+1)) (C.base : Set M)) :
    RVVolumeBlowupClasses hc C 0 → SupportedAERVVolumeFunction hc C X k → SupportedAERVVolumeFunction hc C X k :=
  Quotient.map₂ (fun Z F => ⟨_,⟨F.2.val.prodZero Z,
      selected_volume_family_zero_product_supported Z F.2.val F.2.property⟩⟩)
    (fun Z T hZT F G hFG => ae_volume_zero_coefficient_product_congr hc C F.2.val G.2.val Z T hZT.some hFG)

theorem supported_volume_forget_ordinary_coefficient
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (X : DefSet (rawVFSpace (M := M) (n+1)) (C.base : Set M))
    (z : RVVolumeBlowupClasses hc C 0) (f : SupportedAERVVolumeFunction hc C X k) :
    supportedVolumeFunctionForget hc C X (supportedOrdinaryVolumeCoefficientProduct hc C X z f) =
      z • supportedVolumeFunctionForget hc C X f :=
  Quotient.inductionOn₂ z f (fun _ _ => rfl)

instance supportedVolumeFunctionOrdinarySMul
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (X : DefSet (rawVFSpace (M := M) (n+1)) (C.base : Set M)) :
    SMul (RVVolumeBlowupClasses hc C 0) (SupportedAERVVolumeFunction hc C X k) :=
  ⟨supportedOrdinaryVolumeCoefficientProduct hc C X⟩

theorem supported_volume_forget_smul
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (X : DefSet (rawVFSpace (M := M) (n+1)) (C.base : Set M))
    (z : RVVolumeBlowupClasses hc C 0) (f : SupportedAERVVolumeFunction hc C X k) :
    supportedVolumeFunctionForget hc C X (z • f) = z • supportedVolumeFunctionForget hc C X f :=
  supported_volume_forget_ordinary_coefficient hc C X z f

instance supportedVolumeFunctionOrdinaryModule
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (X : DefSet (rawVFSpace (M := M) (n+1)) (C.base : Set M)) :
    Module (RVVolumeBlowupClasses hc C 0) (SupportedAERVVolumeFunction hc C X k) :=
  Function.Injective.module (RVVolumeBlowupClasses hc C 0)
    (supportedVolumeFunctionForgetAddHom (k := k) hc C X)
    (supported_volume_function_forget_injective hc C X)
    (supported_volume_forget_smul hc C X)

theorem supported_volume_jacobian_map_smul
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    {X Y : DefSet (rawVFSpace (M := M) (n+1)) (C.base : Set M)}
    (φ : Map X Y) (hφ : Function.Bijective φ)
    (z : RVVolumeBlowupClasses hc C 0) (f : SupportedAERVVolumeFunction hc C X k) :
    supportedVolumeFunctionJacobian hc C φ hφ (z • f) = z • supportedVolumeFunctionJacobian hc C φ hφ f := by
  induction z using Quotient.inductionOn with
  | h Z =>
    induction f using Quotient.inductionOn with
    | h F =>
      apply Quotient.sound
      apply ae_rv_volume_function_equivalent_of_pointwise hc C
      intro y
      change positiveVolumeBlowupClass hc (vfParameterVolumeContext C y)
          (((F.2.val.prodZero Z).jacobianPushforward φ hφ
            (selected_volume_family_zero_product_supported Z F.2.val F.2.property)).rowInContext y) =
        positiveVolumeBlowupClass hc (vfParameterVolumeContext C y)
          (((F.2.val.jacobianPushforward φ hφ F.2.property).prodZero Z).rowInContext y)
      rw [volume_family_zero_product_row_scalar]
      by_cases hy : y ∈ Y.carrier
      · exact selected_jacobian_row_ordinary_scalar_comparison hc C Z F.2.val (F.2.val.prodZero Z)
          φ hφ F.2.property (selected_volume_family_zero_product_supported Z F.2.val F.2.property) ⟨y,hy⟩
          (volume_family_zero_product_row_scalar hc F.2.val Z _)
      · let D := vfParameterVolumeContext C y
        have hEmpty {d : ℕ} (H : SelectedVFVolumeFamily C (n+1) d k)
            (hH : ∀ q : H.domain, q.val.1 ∈ X.carrier) :
            positiveVolumeBlowupClass hc D ((H.jacobianPushforward φ hφ hH).rowInContext y) = 0 :=
          positiveVolumeBlowupClass_iso hc D (RVVolumeIso.of_empty hc D _ _
            (selected_jacobian_row_empty_outside C H φ hφ hH y hy) rfl)
        rw [hEmpty (F.2.val.prodZero Z) _,hEmpty F.2.val _,smul_zero]

def supportedVolumeJacobianOrdinaryLinearMap
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    {X Y : DefSet (rawVFSpace (M := M) (n+1)) (C.base : Set M)}
    (φ : Map X Y) (hφ : Function.Bijective φ) :
    SupportedAERVVolumeFunction hc C X k →ₗ[RVVolumeBlowupClasses hc C 0]
      SupportedAERVVolumeFunction hc C Y k where
  toAddHom := supportedVolumeJacobianAddHom (k := k) hc C φ hφ
  map_smul' := fun z f => supported_volume_jacobian_map_smul hc C φ hφ z f
end IntegrationInACVF.Section7
