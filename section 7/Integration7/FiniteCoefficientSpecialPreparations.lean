import Integration7.FiniteVolumeCoefficientFamilies
import Integration7.IndependentRVProductDensityGraphs

/-! Finite-label coefficient products admit actual constrained special
preparations with the original labels retained, without a dummy selected
unit coordinate. The preparation lives on their actual density graph. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section5 (RV carrier SpecialBijection GammaChainDefinable)
open IntegrationInACVF.Section5
namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {a b d p : ℕ}
variable (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
variable (A : DefSet (rawMixedSpace (M := M) 1 a) (C.base : Set M))
variable (hA : ∀ x : Fin 1 → VFType (M := M), {r : Fin a → CanonicalRV.RVSort M | (x,r) ∈ A.carrier}.Finite)
variable (ω : VolumeForm A)
variable (R : SpecialTransformations.Section5.DefSet (M := M) (C.base : Set M) 0 d)
variable (σ : Fin (p+1) → Fin d) (ε : Fin d)
variable (hR : ∀ t : Fin (p+1) → RV (M := M),
  {r : Fin d → RV (M := M) | (Fin.elim0,r) ∈ carrier R ∧ r ∘ σ=t}.Finite)
variable (hε : ∀ q : R, (q.val.2 ε).val ≠ iRVZero)
variable (Ξ : Set (Values.Gamma (M := M)))
variable (hNames : commonRealNames (⟨(C.base : Set M),Ξ⟩ : Base (M := M)) ⊆ (C.base : Set M))

theorem finite_coefficient_density_graph_source (δ : Fin a)
    (hω : ∀ q : A, ω.value q=q.val.2 δ) :
    nativeMixedVolumeDomain hc (finiteVolumeCoefficientFamily hc C A hA ω R σ ε hR hε).densityGraph.domain =
      constrainedUnarySource C Ξ hNames (nativeMixedVolumeDomain hc A)
        (independentRVDensityConstraint hc C Ξ hNames R δ ε) (Fin.castAdd 1 ∘ Fin.castAdd d) :=
  independent_rv_product_density_graph_source hc C Ξ hNames R δ ε A _
    (finite_volume_coefficient_density hc C A hA ω R σ ε hR hε δ hω)

theorem finite_coefficient_special_preparation_exists (δ : Fin a)
    (hω : ∀ q : A, ω.value q=q.val.2 δ)
    {B : SpecialTransformations.Section5.DefSet (M := M) (C.base : Set M) 1 b}
    (T : SpecialBijection (nativeMixedVolumeDomain hc A) B)
    (hT : GammaChainDefinable (⟨(C.base : Set M),Ξ⟩ : Base (M := M)) T.chain)
    (hB : SpecialTransformations.Section5.IsRVPullback (carrier B)) :
    Nonempty (RVLabelConstraintSpecialPreparation T
      (nativeMixedVolumeDomain hc (finiteVolumeCoefficientFamily hc C A hA ω R σ ε hR hε).densityGraph.domain)
      (independentRVDensityConstraint hc C Ξ hNames R δ ε) (Fin.castAdd 1 ∘ Fin.castAdd d)
      (⟨(C.base : Set M),Ξ⟩ : Base (M := M))) := by
  rw [finite_coefficient_density_graph_source hc C A hA ω R σ ε hR hε Ξ hNames δ hω]
  exact constrained_unary_special_preparation_exists C Ξ hNames T hT hB _ _
end IntegrationInACVF.Section7
