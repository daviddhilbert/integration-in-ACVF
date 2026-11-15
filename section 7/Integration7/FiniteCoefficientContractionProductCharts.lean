import Integration7.FiniteCoefficientSpecialPreparations
import Integration7.UnaryPreparedFiniteHeadObjects
import Integration7.FactoredHeadVolumeProductCharts
import Integration7.IndependentRVProductDensityHeadLabels

/-! The actual contraction of a coefficient times a finite-label unary
family is volume-isomorphic to the coefficient times its degree-one raw
prepared head. No selected unit coordinate or cancellation is used. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section5 (RV carrier headImage SpecialBijection GammaChainDefinable)
open IntegrationInACVF.Section5 IntegrationInACVF.Section6
namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {a b d p : ℕ}
variable (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
variable (Ξ : Set (Values.Gamma (M := M)))
variable (hNames : commonRealNames (⟨(C.base : Set M),Ξ⟩ : Base (M := M)) ⊆ (C.base : Set M))
variable (A : DefSet (rawMixedSpace (M := M) 1 a) (C.base : Set M))
variable (hA : ∀ x : Fin 1 → VFType (M := M), {r : Fin a → CanonicalRV.RVSort M | (x,r) ∈ A.carrier}.Finite)
variable (ω : VolumeForm A)
variable (R : SpecialTransformations.Section5.DefSet (M := M) (C.base : Set M) 0 d)
variable (σ : Fin (p+1) → Fin d) (ε : Fin d)
variable (hR : ∀ t : Fin (p+1) → RV (M := M),
  {r : Fin d → RV (M := M) | (Fin.elim0,r) ∈ carrier R ∧ r ∘ σ=t}.Finite)
variable (hε : ∀ q : R, (q.val.2 ε).val ≠ iRVZero)
variable (δ : Fin a) (hδ : ∀ q ∈ A.carrier, (q.2 δ).val ≠ iRVZero)
variable {B : SpecialTransformations.Section5.DefSet (M := M) (C.base : Set M) 1 b}
variable (T : SpecialBijection (nativeMixedVolumeDomain hc A) B)
variable (hB : SpecialTransformations.Section5.IsRVPullback (carrier B))
variable (hT : GammaChainDefinable (⟨(C.base : Set M),Ξ⟩ : Base (M := M)) T.chain)
variable (L : RVLabelConstraintSpecialPreparation T
  (nativeMixedVolumeDomain hc (finiteVolumeCoefficientFamily hc C A hA ω R σ ε hR hε).densityGraph.domain)
  (independentRVDensityConstraint hc C Ξ hNames R δ ε) (Fin.castAdd 1 ∘ Fin.castAdd d)
  (⟨(C.base : Set M),Ξ⟩ : Base (M := M)))

set_option maxHeartbeats 1600000 in
def finiteCoefficientContractionProductIso :
    RVVolumeIso
      ((finiteVolumeCoefficientFamily hc C A hA ω R σ ε hR hε).standardAppendObject hc Ξ
        (unarySpecialStandardContraction L.special L.pullback))
      ((nativeCoordinateDensityVolumeObject hc C R σ ε hR hε).prod
        (unaryPreparedFiniteHeadObject hc C Ξ T hB hT hA δ hδ)) := by
  let J := finiteVolumeCoefficientFamily hc C A hA ω R σ ε hR hε
  let Q := independentRVLabelConstraint C Ξ hNames a R
  let g := nativeRVLabelProduct hc Q (Fin.natAdd a ε) (Fin.castAdd d δ)
  let Φ := independentRVGraphFactorization C Ξ hNames a R g
  let hΦ := independent_rv_graph_factorization_bijective C Ξ hNames a R g
  let hOld := independent_rv_graph_factorization_old_labels C Ξ hNames a R g
  let χ : Fin d → Fin ((a+d)+1) := Fin.castAdd 1 ∘ Fin.natAdd a
  let hCoef := independent_rv_graph_factorization_coefficient_labels C Ξ hNames a R g
  let τ : Fin 1 → Fin (1+b) := Fin.castAdd b
  let δB := Fin.natAdd 1 (suffixIndex (special_chain_rvArity_le T.chain) δ)
  let hFinB := unary_prepared_finite_head_fibres C Ξ T hB hT hA
  let hδB := unary_prepared_head_density_nonzero C T hB δ hδ
  let U := J.standardAppendObject hc Ξ (unarySpecialStandardContraction L.special L.pullback)
  let W := factoredHeadProductVolumeObject hc C L R Φ hΦ hOld χ hCoef σ τ ε δB hR hFinB hε hδB
  have hUW : U.underlying.obj.domain.carrier=W.underlying.obj.domain.carrier := rfl
  have hCoord (u : U.underlying.obj.domain) :
      W.underlying.obj.value ⟨u.val,hUW.le u.property⟩=U.underlying.obj.value u := by
    let q : headImage L.target := ⟨(Fin.elim0,u.val),(mem_rawVolumeContractionLabels hc _ u.val).mp u.property⟩
    change u.val ∘ Fin.append (m := p+1) (n := 1) (L.headParameters ∘ χ ∘ σ)
      (L.headProjection ∘ τ) = u.val ∘ orderedAppendVolumeIndex
        (unarySpecialStandardContraction L.special L.pullback).program J.densityGraph.selected
    rw [unary_special_standard_append_index]
    funext i
    refine Fin.addCases (m := p+1) (n := 1) (fun j => ?_) (fun j => ?_) i
    · simp only [Function.comp_apply,Fin.append_left,headAppendVolumeIndex,headSelectedLabelIndex]
      exact L.carried_head_suffix q (χ (σ j))
    · have hj : j=0 := Subsingleton.elim _ _
      subst j
      simp only [Function.comp_apply,Fin.append_right,headAppendVolumeIndex,
        RVLabelConstraintSpecialPreparation.headProjection,τ,Fin.append_left]
      rfl
  have hForm (u : U.underlying.obj.domain) : W.form.value ⟨u.val,hUW.le u.property⟩=U.form.value u := by
    let q : headImage L.target := ⟨(Fin.elim0,u.val),(mem_rawVolumeContractionLabels hc _ u.val).mp u.property⟩
    calc
      W.form.value ⟨u.val,hUW.le u.property⟩ =
          u.val (L.headParameters (χ ε))*u.val (L.headProjection δB) :=
        factored_head_product_volume_density hc C L R Φ hΦ hOld χ hCoef σ τ ε δB hR hFinB hε hδB _
      _ = U.form.value u := by
        change _ = u.val (orderedAppendDensityIndex
          (unarySpecialStandardContraction L.special L.pullback).program (Fin.last (a+d)))
        rw [unary_special_standard_density_index]
        apply Subtype.ext
        rw [RVOperations.mul_val]
        exact (independent_rv_prepared_head_density_suffix hc C Ξ hNames R δ ε L q).symm
  let e : U.underlying ≅ W.underlying := rvFiniteIsoOfAmbient (U := U.underlying) (V := W.underlying)
    (rvIsoOfCarrierEq U.underlying.obj.domain W.underlying.obj.domain U.underlying.obj.volume W.underlying.obj.volume hUW hCoord)
  exact (RVVolumeIso.of_preserving_coordinates_full hc C e hCoord hForm).trans hc C
    (factoredHeadProductVolumeIso hc C L R Φ hΦ hOld χ hCoef σ τ ε δB hR hFinB hε hδB)
end IntegrationInACVF.Section7
