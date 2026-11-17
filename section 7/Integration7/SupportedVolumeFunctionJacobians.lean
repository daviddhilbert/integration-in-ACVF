module

public import Integration7.SelectedJacobianAlmostEverywhere
public import Integration7.SelectedFamilyJacobianIntegrals
public import Integration7.AERVVolumeFunctionIntegrals

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! Actual positive homogeneous functions on a definable VF domain,
presented by families supported there and identified almost everywhere.
The Jacobian transform descends to this quotient and preserves its
literal canonical integral. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n k : ℕ}

abbrev SupportedVolumeFunctionPresentation (C : BaseContext M)
    (X : DefSet (rawVFSpace (M := M) (n+1)) (C.base : Set M)) (k : ℕ) :=
  Σ a, {F : SelectedVFVolumeFamily C (n+1) a k // ∀ p : F.domain, p.val.1 ∈ X.carrier}

def supportedVolumeFunctionSetoid
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (X : DefSet (rawVFSpace (M := M) (n+1)) (C.base : Set M)) (k : ℕ) :
    Setoid (SupportedVolumeFunctionPresentation C X k) :=
  Setoid.comap (fun F => (⟨F.1,F.2.val⟩ : SelectedVolumeFunctionPresentation C (n+1) k))
    (aeRVVolumeFunctionSetoid hc C n k)

abbrev SupportedAERVVolumeFunction
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (X : DefSet (rawVFSpace (M := M) (n+1)) (C.base : Set M)) (k : ℕ) :=
  Quotient (supportedVolumeFunctionSetoid hc C X k)

def supportedVolumeFunctionForget
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (X : DefSet (rawVFSpace (M := M) (n+1)) (C.base : Set M)) :
    SupportedAERVVolumeFunction hc C X k → AERVVolumeFunction hc C n k :=
  Quotient.map (fun F => (⟨F.1,F.2.val⟩ : SelectedVolumeFunctionPresentation C (n+1) k))
    (fun _ _ h => h)

theorem supported_volume_function_forget_injective
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (X : DefSet (rawVFSpace (M := M) (n+1)) (C.base : Set M)) :
    Function.Injective (supportedVolumeFunctionForget hc C X (k := k)) := by
  intro u v
  induction u using Quotient.inductionOn with
  | h F =>
    induction v using Quotient.inductionOn with
    | h G =>
      intro h
      have hAE : AERVVolumeFunctionEquivalent hc C ⟨F.1,F.2.val⟩ ⟨G.1,G.2.val⟩ :=
        Quotient.exact h
      exact Quotient.sound hAE

def SupportedVolumeFunctionPresentation.jacobianTransform
    {C : BaseContext M} {X Y : DefSet (rawVFSpace (M := M) (n+1)) (C.base : Set M)}
    (F : SupportedVolumeFunctionPresentation C X k) (φ : Map X Y) (hφ : Function.Bijective φ) :
    SupportedVolumeFunctionPresentation C Y k := by
  refine ⟨F.1,⟨F.2.val.jacobianPushforward φ hφ F.2.property,?_⟩⟩
  rintro ⟨q,p,hp⟩
  have he : (φ ⟨p.val.1,F.2.property p⟩).val = q.1 := congrArg Prod.fst hp
  exact he ▸ (φ ⟨p.val.1,F.2.property p⟩).property

def supportedVolumeFunctionJacobian
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    {X Y : DefSet (rawVFSpace (M := M) (n+1)) (C.base : Set M)}
    (φ : Map X Y) (hφ : Function.Bijective φ) :
    SupportedAERVVolumeFunction hc C X k → SupportedAERVVolumeFunction hc C Y k :=
  Quotient.map (fun F => F.jacobianTransform φ hφ) (by
    intro F G h
    exact selected_jacobian_preserves_ae_equivalence hc C F.2.val G.2.val φ hφ
      F.2.property G.2.property h)

theorem supported_volume_function_jacobian_integral
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (Ξ : Set (Values.Gamma (M := M))) (hΞ : Cardinal.mk Ξ < C.κ)
    (hGenerated : VFGammaGeneratedBase (⟨(C.base : Set M),Ξ⟩ : Base (M := M)))
    (hNames : commonRealNames (⟨(C.base : Set M),Ξ⟩ : Base (M := M)) ⊆ (C.base : Set M))
    (γ : Values.Gamma (M := M)) (hγ : γ ∈ Ξ) (hγ1 : 1 < γ)
    {X Y : DefSet (rawVFSpace (M := M) (n+1)) (C.base : Set M)}
    (φ : Map X Y) (hφ : Function.Bijective φ) (f : SupportedAERVVolumeFunction hc C X k) :
    aeRVVolumeFunctionIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1
      (supportedVolumeFunctionForget hc C X f) =
    aeRVVolumeFunctionIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1
      (supportedVolumeFunctionForget hc C Y (supportedVolumeFunctionJacobian hc C φ hφ f)) := by
  induction f using Quotient.inductionOn with
  | h F =>
    exact selected_family_jacobian_canonical_integral hc C Ξ hΞ hGenerated hNames γ hγ hγ1
      F.2.val φ hφ F.2.property

end IntegrationInACVF.Section7
