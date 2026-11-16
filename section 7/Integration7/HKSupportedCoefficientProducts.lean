module

public import Integration7.HKSupportedGradedVolumeFunctions
public import Integration7.HKGradedAEVolumeActionCoherence
public import Integration7.NormalizedOrdinaryVolumeSupports
public import Integration7.SupportedPositiveVolumeCoefficients

@[expose] public section

/-! All genuine weighted coefficient products retain literal VF
support. Their supported quotients forget to the actual AE products. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.DefinableGeometry
namespace IntegrationInACVF.Section7.HK
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n a d k p : ℕ}

theorem mixed_finite_factor_preserves_support {C : BaseContext M}
    {X : DefSet (rawVFSpace (M := M) n) (C.base : Set M)}
    (A : DefSet (rawMixedSpace (M := M) n a) (C.base : Set M))
    (R : DefSet (rawRVSpace (M := M) d) (C.base : Set M))
    (hA : ∀ q : A, q.val.1 ∈ X.carrier) (q : mixedRVFactorDomain A R) : q.val.1 ∈ X.carrier := by
  have hm := (mem_mixed_rv_factor_domain A R q.val.1 q.val.2).mp q.property
  exact hA ⟨(q.val.1,q.val.2 ∘ Fin.castAdd d),hm.1⟩

theorem selected_zero_positive_product_supported {C : BaseContext M}
    {X : DefSet (rawVFSpace (M := M) n) (C.base : Set M)}
    (U : PositiveRVVolumeObject (M := M) (C.base : Set M) p)
    (F : ZeroVFVolumeFamily C n a) (hF : ∀ q : F.domain, q.val.1 ∈ X.carrier) :
    ∀ q : (selectedZeroFamilyPositiveProduct U F).domain, q.val.1 ∈ X.carrier := by
  rintro ⟨q,z,hz⟩
  have he := congrArg Prod.fst hz
  change z.val.1=q.1 at he
  have hmem := (mem_mixed_rv_factor_domain F.domain U.underlying.obj.domain z.val.1 z.val.2).mp z.property
  exact he ▸ hF ⟨(z.val.1,z.val.2 ∘ Fin.castAdd U.underlying.obj.arity),hmem.1⟩

set_option maxHeartbeats 1600000 in
def supportedZeroWeightedCoefficientProduct
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (X : DefSet (rawVFSpace (M := M) (n+1)) (C.base : Set M)) :
    RVBlowupClasses hc C 0 → SupportedAEZeroVolumeFunction hc C X → SupportedAEZeroVolumeFunction hc C X :=
  Quotient.map₂ (fun (Z : ZeroRVVolumeObject (M := M) (C.base : Set M))
    (F : SupportedZeroVolumeFunctionPresentation C X) => ⟨_,⟨F.2.val.prodZero Z,
    mixed_finite_factor_preserves_support F.2.val.domain Z.underlying.obj.domain F.2.property⟩⟩)
    (fun Z T hZT F G hFG => ae_zero_volume_scalar_congr hc C Z T
      ⟨F.1,F.2.val⟩ ⟨G.1,G.2.val⟩ hZT hFG)

def supportedPositiveWeightedCoefficientProduct
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (X : DefSet (rawVFSpace (M := M) (n+1)) (C.base : Set M)) :
    RVBlowupClasses hc C 0 → SupportedAERVVolumeFunction hc C X k → SupportedAERVVolumeFunction hc C X k :=
  Quotient.map₂ (fun Z F => ⟨_,⟨selectedFamilyWeightedZeroProduct F.2.val Z,
    mixed_finite_factor_preserves_support F.2.val.domain Z.underlying.obj.domain F.2.property⟩⟩)
    (by
      rintro Z T ⟨e⟩ F G hFG
      exact ae_weighted_zero_product_congr hc C F.2.val G.2.val Z T e hFG)

set_option maxHeartbeats 1600000 in
def supportedZeroPositiveCoefficientProduct
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (X : DefSet (rawVFSpace (M := M) (n+1)) (C.base : Set M)) :
    PositiveVolumeBlowupClasses hc C p → SupportedAEZeroVolumeFunction hc C X → SupportedAERVVolumeFunction hc C X p :=
  Quotient.map₂ (fun (U : PositiveRVVolumeObject (M := M) (C.base : Set M) p)
    (F : SupportedZeroVolumeFunctionPresentation C X) =>
      (⟨_,⟨selectedZeroFamilyPositiveProduct U F.2.val,
        selected_zero_positive_product_supported U F.2.val F.2.property⟩⟩ : SupportedVolumeFunctionPresentation C X p))
    (by
      intro U V hUV F G hFG
      exact ae_zero_positive_coefficient_product_congr hc C U V ⟨F.1,F.2.val⟩ ⟨G.1,G.2.val⟩ hUV hFG)

theorem supported_zero_forget_weighted_coefficient
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (X : DefSet (rawVFSpace (M := M) (n+1)) (C.base : Set M))
    (z : RVBlowupClasses hc C 0) (f : SupportedAEZeroVolumeFunction hc C X) :
    supportedZeroVolumeFunctionForget hc C X (supportedZeroWeightedCoefficientProduct hc C X z f) =
      z • supportedZeroVolumeFunctionForget hc C X f := Quotient.inductionOn₂ z f (fun _ _ => rfl)

theorem supported_positive_forget_weighted_coefficient
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (X : DefSet (rawVFSpace (M := M) (n+1)) (C.base : Set M))
    (z : RVBlowupClasses hc C 0) (f : SupportedAERVVolumeFunction hc C X k) :
    supportedVolumeFunctionForget hc C X (supportedPositiveWeightedCoefficientProduct hc C X z f) =
      z • supportedVolumeFunctionForget hc C X f := Quotient.inductionOn₂ z f (fun _ _ => rfl)

theorem supported_zero_forget_positive_coefficient
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (X : DefSet (rawVFSpace (M := M) (n+1)) (C.base : Set M))
    (u : PositiveVolumeBlowupClasses hc C p) (f : SupportedAEZeroVolumeFunction hc C X) :
    supportedVolumeFunctionForget hc C X (supportedZeroPositiveCoefficientProduct hc C X u f) =
      aeZeroVolumeFunctionPositiveCoefficientProduct hc C n p u (supportedZeroVolumeFunctionForget hc C X f) :=
  Quotient.inductionOn₂ u f (fun _ _ => rfl)

end IntegrationInACVF.Section7.HK
