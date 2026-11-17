module

public import Integration7.HKZeroJacobianAlmostEverywhere
public import Integration7.HKZeroFamilyJacobianIntegrals
public import Integration7.HKAEZeroIntegrals

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! Actual weighted-zero-valued functions on a definable VF domain,
presented by families supported there and identified almost everywhere.
The Jacobian transform descends to this quotient and preserves its
literal weighted integral. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry

namespace IntegrationInACVF.Section7.HK
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n : ℕ}

abbrev SupportedZeroVolumeFunctionPresentation (C : BaseContext M)
    (X : DefSet (rawVFSpace (M := M) (n+1)) (C.base : Set M)) :=
  Σ a, {F : ZeroVFVolumeFamily C (n+1) a // ∀ p : F.domain, p.val.1 ∈ X.carrier}

def supportedZeroVolumeFunctionSetoid
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (X : DefSet (rawVFSpace (M := M) (n+1)) (C.base : Set M)) :
    Setoid (SupportedZeroVolumeFunctionPresentation C X) :=
  Setoid.comap (fun F => (⟨F.1,F.2.val⟩ : ZeroVolumeFunctionPresentation C (n+1)))
    (aeZeroVolumeFunctionSetoid hc C n)

abbrev SupportedAEZeroVolumeFunction
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (X : DefSet (rawVFSpace (M := M) (n+1)) (C.base : Set M)) :=
  Quotient (supportedZeroVolumeFunctionSetoid hc C X)

def supportedZeroVolumeFunctionForget
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (X : DefSet (rawVFSpace (M := M) (n+1)) (C.base : Set M)) :
    SupportedAEZeroVolumeFunction hc C X → AEZeroVolumeFunction hc C n :=
  Quotient.map (fun F => (⟨F.1,F.2.val⟩ : ZeroVolumeFunctionPresentation C (n+1)))
    (fun _ _ h => h)

theorem supported_zero_volume_function_forget_injective
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (X : DefSet (rawVFSpace (M := M) (n+1)) (C.base : Set M)) :
    Function.Injective (supportedZeroVolumeFunctionForget hc C X) := by
  intro u v
  induction u using Quotient.inductionOn with
  | h F =>
    induction v using Quotient.inductionOn with
    | h G =>
      intro h
      have hAE : AEZeroVolumeFunctionEquivalent hc C ⟨F.1,F.2.val⟩ ⟨G.1,G.2.val⟩ :=
        Quotient.exact h
      exact Quotient.sound hAE

def SupportedZeroVolumeFunctionPresentation.jacobianTransform
    {C : BaseContext M} {X Y : DefSet (rawVFSpace (M := M) (n+1)) (C.base : Set M)}
    (F : SupportedZeroVolumeFunctionPresentation C X) (φ : Map X Y) (hφ : Function.Bijective φ) :
    SupportedZeroVolumeFunctionPresentation C Y := by
  refine ⟨F.1,⟨F.2.val.jacobianPushforward φ hφ F.2.property,?_⟩⟩
  rintro ⟨q,p,hp⟩
  have he : (φ ⟨p.val.1,F.2.property p⟩).val = q.1 := congrArg Prod.fst hp
  exact he ▸ (φ ⟨p.val.1,F.2.property p⟩).property

def supportedZeroVolumeFunctionJacobian
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    {X Y : DefSet (rawVFSpace (M := M) (n+1)) (C.base : Set M)}
    (φ : Map X Y) (hφ : Function.Bijective φ) :
    SupportedAEZeroVolumeFunction hc C X → SupportedAEZeroVolumeFunction hc C Y :=
  Quotient.map (fun F => F.jacobianTransform φ hφ) (by
    intro F G h
    exact zero_jacobian_preserves_ae_equivalence hc C F.2.val G.2.val φ hφ
      F.2.property G.2.property h)

theorem supported_zero_volume_function_jacobian_integral
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (Ξ : Set (Values.Gamma (M := M))) (hΞ : Cardinal.mk Ξ < C.κ)
    (hGenerated : VFGammaGeneratedBase (⟨(C.base : Set M),Ξ⟩ : Base (M := M)))
    (hNames : commonRealNames (⟨(C.base : Set M),Ξ⟩ : Base (M := M)) ⊆ (C.base : Set M))
    (γ : Values.Gamma (M := M)) (hγ : γ ∈ Ξ) (hγ1 : 1 < γ)
    {X Y : DefSet (rawVFSpace (M := M) (n+1)) (C.base : Set M)}
    (φ : Map X Y) (hφ : Function.Bijective φ) (f : SupportedAEZeroVolumeFunction hc C X) :
    aeZeroVolumeFunctionIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1
      (supportedZeroVolumeFunctionForget hc C X f) =
    aeZeroVolumeFunctionIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1
      (supportedZeroVolumeFunctionForget hc C Y (supportedZeroVolumeFunctionJacobian hc C φ hφ f)) := by
  induction f using Quotient.inductionOn with
  | h F =>
    exact zero_family_jacobian_integral hc C Ξ hΞ hGenerated hNames γ hγ hγ1
      F.2.val φ hφ F.2.property

end IntegrationInACVF.Section7.HK
