module

public import Integration7.HKZeroFamilyJacobianPushforwards
public import Integration7.HKAEZeroIntegrals

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! The actual weighted-zero VF realization gives change of variables
with no added coefficient degree and no cancellation or localization. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry

namespace IntegrationInACVF.Section7.HK
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n a : ℕ}

def zeroFamilyJacobianVolumeBijection
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    {X Y : DefSet (rawVFSpace (M := M) (n+1)) (C.base : Set M)}
    (F : ZeroVFVolumeFamily C (n+1) a) (φ : Map X Y) (hφ : Function.Bijective φ)
    (hF : ∀ p : F.domain, p.val.1 ∈ X.carrier) :
    VFVolumeBijection F.fullVFObject (F.jacobianPushforward φ hφ hF).fullVFObject :=
  ⟨(mixedVFBaseMap φ F.domain hF).toImage,
    mixed_vf_base_map_to_image_bijective φ hφ.1 F.domain hF,
    zero_family_jacobian_pushforward_preserves_volume hc C (Nat.zero_lt_succ n) F φ hφ hF⟩

theorem zero_family_jacobian_integral
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (Ξ : Set (Values.Gamma (M := M))) (hΞ : Cardinal.mk Ξ < C.κ)
    (hGenerated : VFGammaGeneratedBase (⟨(C.base : Set M),Ξ⟩ : Base (M := M)))
    (hNames : commonRealNames (⟨(C.base : Set M),Ξ⟩ : Base (M := M)) ⊆ (C.base : Set M))
    (γ : Values.Gamma (M := M)) (hγ : γ ∈ Ξ) (hγ1 : 1 < γ)
    {X Y : DefSet (rawVFSpace (M := M) (n+1)) (C.base : Set M)}
    (F : ZeroVFVolumeFamily C (n+1) a) (φ : Map X Y) (hφ : Function.Bijective φ)
    (hF : ∀ p : F.domain, p.val.1 ∈ X.carrier) :
    aeZeroVolumeFunctionIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 (Quotient.mk _ ⟨a,F⟩) =
      aeZeroVolumeFunctionIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1
        (Quotient.mk _ ⟨a,F.jacobianPushforward φ hφ hF⟩) :=
  congrArg (positiveVolumeIntegrationEquiv hc C Ξ hΞ hGenerated hNames γ hγ hγ1)
    (Quotient.sound ⟨VFVolumeIso.of_bijection (zeroFamilyJacobianVolumeBijection hc C F φ hφ hF)⟩)

end IntegrationInACVF.Section7.HK
