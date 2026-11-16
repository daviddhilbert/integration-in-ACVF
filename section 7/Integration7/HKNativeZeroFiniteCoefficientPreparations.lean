import Integration7.HKZeroFamilyScalarProducts
import Integration7.HKZeroFamilyHeadIntegrals
import Integration7.HKNativeZeroDensityObjects
import Integration7.IndependentRVProductDensityGraphs

/-! A finite weighted coefficient is retained through a special
preparation of the actual product-density graph. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section5 (RV carrier SpecialBijection GammaChainDefinable)
open IntegrationInACVF.Section5
namespace IntegrationInACVF.Section7.HK
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {a b d k : ℕ}
variable (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
variable (F : ZeroVFVolumeFamily C 1 a)
variable (R : SpecialTransformations.Section5.DefSet (M := M) (C.base : Set M) 0 d)
variable (ε : Fin d) (hR : (rawVolumeContractionLabels hc R).carrier.Finite)
variable (hε : ∀ q : R, (q.val.2 ε).val ≠ iRVZero)

def nativeZeroFiniteCoefficientFamily :=
  F.prodZero (nativeZeroDensityObject hc C R ε hR hε)

theorem native_zero_finite_coefficient_density (δ : Fin a)
    (hF : ∀ q : F.domain, F.form.value q=q.val.2 δ)
    (q : (nativeZeroFiniteCoefficientFamily hc C F R ε hR hε).domain) :
    (nativeZeroFiniteCoefficientFamily hc C F R ε hR hε).form.value q =
      q.val.2 (Fin.natAdd a ε) * q.val.2 (Fin.castAdd d δ) := by
  let w := mixedRVFactorUnpack F.domain (rawVolumeContractionLabels hc R) q
  have hw := mixed_rv_factor_unpack_value F.domain (rawVolumeContractionLabels hc R) q
  change F.form.value (Map.prodFst _ _ w) * (Map.prodSnd _ _ w).val ε = _
  rw [hF]
  have hLeft := congrArg (fun z => z.1.2) hw
  have hRight := congrArg Prod.snd hw
  change (Map.prodFst _ _ w).val.2 = q.val.2 ∘ Fin.castAdd d at hLeft
  change (Map.prodSnd _ _ w).val = q.val.2 ∘ Fin.natAdd a at hRight
  rw [hLeft,hRight]
  exact mul_comm _ _

variable (Ξ : Set (Values.Gamma (M := M)))
variable (hNames : commonRealNames (⟨(C.base : Set M),Ξ⟩ : Base (M := M)) ⊆ (C.base : Set M))

theorem native_zero_finite_coefficient_density_graph_source (δ : Fin a)
    (hF : ∀ q : F.domain, F.form.value q=q.val.2 δ) :
    nativeMixedVolumeDomain hc (nativeZeroFiniteCoefficientFamily hc C F R ε hR hε).fullVFObject.densityGraph.domain =
      constrainedUnarySource C Ξ hNames (nativeMixedVolumeDomain hc F.domain)
        (independentRVDensityConstraint hc C Ξ hNames R δ ε) (Fin.castAdd 1 ∘ Fin.castAdd d) :=
  independent_rv_product_density_graph_source hc C Ξ hNames R δ ε F.domain _
    (native_zero_finite_coefficient_density hc C F R ε hR hε δ hF)

theorem native_zero_finite_coefficient_special_preparation_exists (δ : Fin a)
    (hF : ∀ q : F.domain, F.form.value q=q.val.2 δ)
    {B : SpecialTransformations.Section5.DefSet (M := M) (C.base : Set M) 1 b}
    (T : SpecialBijection (nativeMixedVolumeDomain hc F.domain) B)
    (hT : GammaChainDefinable (⟨(C.base : Set M),Ξ⟩ : Base (M := M)) T.chain)
    (hB : SpecialTransformations.Section5.IsRVPullback (carrier B)) :
    Nonempty (RVLabelConstraintSpecialPreparation T
      (nativeMixedVolumeDomain hc (nativeZeroFiniteCoefficientFamily hc C F R ε hR hε).fullVFObject.densityGraph.domain)
      (independentRVDensityConstraint hc C Ξ hNames R δ ε) (Fin.castAdd 1 ∘ Fin.castAdd d)
      (⟨(C.base : Set M),Ξ⟩ : Base (M := M))) := by
  rw [native_zero_finite_coefficient_density_graph_source hc C F R ε hR hε Ξ hNames δ hF]
  exact constrained_unary_special_preparation_exists C Ξ hNames T hT hB _ _

end IntegrationInACVF.Section7.HK
