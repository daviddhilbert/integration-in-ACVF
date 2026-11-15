import Integration7.NormalizedVolumeDomainJacobians
import Integration7.NormalizedPositiveFunctionGeneration

/-! Ordinary RV[0] families retain their geometric support under
actual point padding, so the full normalized domain formula includes
ordinary generators without assigning them artificial densities. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry
namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n a p : ℕ}

theorem selected_ordinary_positive_product_supported
    {C : BaseContext M} {X : DefSet (rawVFSpace (M := M) n) (C.base : Set M)}
    (U : PositiveRVVolumeObject (M := M) (C.base : Set M) p)
    (F : OrdinaryVFVolumeFamily C n a) (hF : ∀ q : F.domain, q.val.1 ∈ X.carrier) :
    ∀ q : (selectedOrdinaryFamilyPositiveProduct U F).domain, q.val.1 ∈ X.carrier := by
  rintro ⟨q,z,hz⟩
  have he := congrArg Prod.fst hz
  change z.val.1=q.1 at he
  have hmem := (mem_mixed_rv_factor_domain F.domain U.underlying.obj.domain z.val.1 z.val.2).mp z.property
  exact he ▸ hF ⟨(z.val.1,z.val.2 ∘ Fin.castAdd U.underlying.obj.arity),hmem.1⟩

def ordinaryPointSupportedVolumeFunction
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (X : DefSet (rawVFSpace (M := M) (n+1)) (C.base : Set M))
    (F : OrdinaryVFVolumeFamily C (n+1) a) (hF : ∀ q : F.domain, q.val.1 ∈ X.carrier) :
    SupportedAERVVolumeFunction hc C X 0 :=
  Quotient.mk _ ⟨_,⟨selectedOrdinaryFamilyPositiveProduct (degreeOnePointVolumeObject (C.base : Set M)) F,
    selected_ordinary_positive_product_supported _ F hF⟩⟩

theorem normalized_ordinary_family_has_support
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (X : DefSet (rawVFSpace (M := M) (n+1)) (C.base : Set M))
    (F : OrdinaryVFVolumeFamily C (n+1) a) (hF : ∀ q : F.domain, q.val.1 ∈ X.carrier) :
    HasNormalizedVolumeSupport hc C X
      (normalizedVolumeFunctionGenerator hc C n
        (DirectSum.of (AEVolumeFunctionComponent hc C n) 0 (Quotient.mk _ ⟨a,F⟩))) := by
  rw [normalized_ordinary_function_positive_generator]
  exact normalized_positive_supported_generator_has_support hc C X 0 (ordinaryPointSupportedVolumeFunction hc C X F hF)

theorem normalized_volume_domain_jacobian_ordinary_family
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    {X Y : DefSet (rawVFSpace (M := M) (n+1)) (C.base : Set M)} (φ : Map X Y) (hφ : Function.Bijective φ)
    (F : OrdinaryVFVolumeFamily C (n+1) a) (hF : ∀ q : F.domain, q.val.1 ∈ X.carrier) :
    normalizedVolumeDomainJacobian hc C φ hφ (normalizedVolumeFunctionGenerator hc C n
      (DirectSum.of (AEVolumeFunctionComponent hc C n) 0 (Quotient.mk _ ⟨a,F⟩))) =
      normalizedPositiveVolumeFunction hc C n 0 (supportedVolumeFunctionForget hc C Y
        (supportedVolumeFunctionJacobian hc C φ hφ (ordinaryPointSupportedVolumeFunction hc C X F hF))) := by
  rw [normalized_ordinary_function_positive_generator]
  exact normalized_volume_domain_jacobian_positive hc C φ hφ 0 (ordinaryPointSupportedVolumeFunction hc C X F hF)

theorem normalized_ordinary_family_domain_change_of_variables
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (Ξ : Set (Values.Gamma (M := M))) (hΞ : Cardinal.mk Ξ < C.κ)
    (hGenerated : VFGammaGeneratedBase (⟨(C.base : Set M),Ξ⟩ : Base (M := M)))
    (hNames : commonRealNames (⟨(C.base : Set M),Ξ⟩ : Base (M := M)) ⊆ (C.base : Set M))
    (γ : Values.Gamma (M := M)) (hγ : γ ∈ Ξ) (hγ1 : 1 < γ)
    {X Y : DefSet (rawVFSpace (M := M) (n+1)) (C.base : Set M)} (φ : Map X Y) (hφ : Function.Bijective φ)
    (F : OrdinaryVFVolumeFamily C (n+1) a) (hF : ∀ q : F.domain, q.val.1 ∈ X.carrier) :
    normalizedVolumeIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 n
      (normalizedVolumeFunctionGenerator hc C n (DirectSum.of (AEVolumeFunctionComponent hc C n) 0 (Quotient.mk _ ⟨a,F⟩))) =
    normalizedVolumeIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 n
      (normalizedVolumeDomainJacobian hc C φ hφ (normalizedVolumeFunctionGenerator hc C n
        (DirectSum.of (AEVolumeFunctionComponent hc C n) 0 (Quotient.mk _ ⟨a,F⟩)))) :=
  normalized_volume_domain_change_of_variables hc C Ξ hΞ hGenerated hNames γ hγ hγ1 φ hφ _
    (normalized_ordinary_family_has_support hc C X F hF)
end IntegrationInACVF.Section7
