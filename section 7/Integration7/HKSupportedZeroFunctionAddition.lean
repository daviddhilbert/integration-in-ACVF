module

public import Integration7.HKSupportedZeroFunctionJacobians
public import Integration7.HKAEZeroFunctionAddition

@[expose] public section

/-! Weighted-zero functions supported on an actual definable VF domain
have the pointwise additive structure of their injective AE forgetful map. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.DefinableGeometry

namespace IntegrationInACVF.Section7.HK
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n a b : ℕ}

theorem zero_family_coprod_supported {C : BaseContext M}
    {X : DefSet (rawVFSpace (M := M) (n+1)) (C.base : Set M)}
    (F : ZeroVFVolumeFamily C (n+1) a) (G : ZeroVFVolumeFamily C (n+1) b)
    (hF : ∀ p : F.domain, p.val.1 ∈ X.carrier) (hG : ∀ p : G.domain, p.val.1 ∈ X.carrier) :
    ∀ p : (F.coprod G).domain, p.val.1 ∈ X.carrier := by
  intro p
  rcases vf_volume_coprod_cases F.fullVFObject G.fullVFObject p with ⟨u,hu⟩ | ⟨v,hv⟩
  · exact (congrArg (fun q => q.val.1) hu) ▸ hF u
  · exact (congrArg (fun q => q.val.1) hv) ▸ hG v

instance supportedZeroVolumeFunctionAdd
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (X : DefSet (rawVFSpace (M := M) (n+1)) (C.base : Set M)) :
    Add (SupportedAEZeroVolumeFunction hc C X) :=
  ⟨Quotient.map₂ (fun F G => ⟨_,⟨F.2.val.coprod G.2.val,
      zero_family_coprod_supported F.2.val G.2.val F.2.property G.2.property⟩⟩)
    (fun F F' hF G G' hG => ae_zero_family_coprod_congr hc C
      ⟨F.1,F.2.val⟩ ⟨F'.1,F'.2.val⟩ ⟨G.1,G.2.val⟩ ⟨G'.1,G'.2.val⟩ hF hG)⟩

instance supportedZeroVolumeFunctionZero
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (X : DefSet (rawVFSpace (M := M) (n+1)) (C.base : Set M)) :
    Zero (SupportedAEZeroVolumeFunction hc C X) :=
  ⟨Quotient.mk _ ⟨0,⟨zeroFamily C (n+1),fun p => False.elim p.property⟩⟩⟩

theorem supported_zero_volume_function_forget_add
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (X : DefSet (rawVFSpace (M := M) (n+1)) (C.base : Set M))
    (f g : SupportedAEZeroVolumeFunction hc C X) :
    supportedZeroVolumeFunctionForget hc C X (f+g) =
      supportedZeroVolumeFunctionForget hc C X f + supportedZeroVolumeFunctionForget hc C X g :=
  Quotient.inductionOn₂ f g (fun _ _ => rfl)

theorem supported_zero_volume_function_forget_zero
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (X : DefSet (rawVFSpace (M := M) (n+1)) (C.base : Set M)) :
    supportedZeroVolumeFunctionForget hc C X (0 : SupportedAEZeroVolumeFunction hc C X) = 0 := rfl

instance supportedZeroVolumeFunctionAddCommMonoid
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (X : DefSet (rawVFSpace (M := M) (n+1)) (C.base : Set M)) :
    AddCommMonoid (SupportedAEZeroVolumeFunction hc C X) where
  add_assoc f g h := supported_zero_volume_function_forget_injective hc C X (by
    simp only [supported_zero_volume_function_forget_add,add_assoc])
  add_comm f g := supported_zero_volume_function_forget_injective hc C X (by
    simp only [supported_zero_volume_function_forget_add,add_comm])
  zero_add f := supported_zero_volume_function_forget_injective hc C X (by
    simp only [supported_zero_volume_function_forget_add,supported_zero_volume_function_forget_zero,zero_add])
  add_zero f := supported_zero_volume_function_forget_injective hc C X (by
    simp only [supported_zero_volume_function_forget_add,supported_zero_volume_function_forget_zero,add_zero])
  nsmul := nsmulRec

def supportedZeroVolumeFunctionForgetAddHom
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (X : DefSet (rawVFSpace (M := M) (n+1)) (C.base : Set M)) :
    SupportedAEZeroVolumeFunction hc C X →+ AEZeroVolumeFunction hc C n where
  toFun := supportedZeroVolumeFunctionForget hc C X
  map_zero' := supported_zero_volume_function_forget_zero hc C X
  map_add' := supported_zero_volume_function_forget_add hc C X

theorem zero_rv_volume_class_of_empty
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (U : ZeroRVVolumeObject (M := M) (C.base : Set M)) (hU : U.underlying.obj.domain.carrier = ∅) :
    rvVolumeBlowupClass hc C (n := 0) U = 0 := by
  let V := empty (C.base : Set M) 0
  let f : Map U.underlying.obj.domain V.underlying.obj.domain := Map.fromEmpty hU V.underlying.obj.domain
  apply Quotient.sound
  refine ⟨ZeroRVVolumeIso.ofBijection f (Map.bijective_of_empty f hU rfl) ?_⟩
  intro u
  exact False.elim ((Set.eq_empty_iff_forall_notMem.mp hU) u.val u.property)

theorem supported_zero_volume_jacobian_map_zero
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    {X Y : DefSet (rawVFSpace (M := M) (n+1)) (C.base : Set M)}
    (φ : Map X Y) (hφ : Function.Bijective φ) :
    supportedZeroVolumeFunctionJacobian hc C φ hφ (0 : SupportedAEZeroVolumeFunction hc C X) = 0 := by
  apply Quotient.sound
  apply ae_zero_volume_equivalent_of_pointwise hc C
  intro y
  rw [zero_family_row_class]
  apply zero_rv_volume_class_of_empty hc (vfParameterVolumeContext C y)
  apply Set.eq_empty_iff_forall_notMem.mpr
  rintro r ⟨p,hp⟩
  exact p.property

end IntegrationInACVF.Section7.HK
