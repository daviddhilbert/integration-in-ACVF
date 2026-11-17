module

public import Integration7.NativeCoordinateCoefficientPreparations
public import Integration7.UnaryPreparedHeadVolumeObjects
public import Integration7.FactoredHeadAppendedVolumeCoordinates
public import Integration7.FactoredHeadVolumeProductCharts
public import Integration7.IndependentRVProductDensityHeadLabels

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! The specified contraction of an actual constant-coefficient family
is volume-isomorphic to the coefficient times the prepared fibre head.
The proof compares all coordinates and the original density literally. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section5 (RV carrier headImage SpecialBijection GammaChainDefinable)
open IntegrationInACVF.Section5 IntegrationInACVF.Section6
namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {a b d k p : ℕ}
variable (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
variable (Ξ : Set (Values.Gamma (M := M)))
variable (hNames : commonRealNames (⟨(C.base : Set M),Ξ⟩ : Base (M := M)) ⊆ (C.base : Set M))
variable (F : SelectedVFVolumeFamily C 1 a k)
variable (R : SpecialTransformations.Section5.DefSet (M := M) (C.base : Set M) 0 d)
variable (σ : Fin (p+1) → Fin d) (ε : Fin d)
variable (hR : ∀ t : Fin (p+1) → RV (M := M),
  {r : Fin d → RV (M := M) | (Fin.elim0,r) ∈ carrier R ∧ r ∘ σ=t}.Finite)
variable (hε : ∀ q : R, (q.val.2 ε).val ≠ iRVZero)
variable (δ : Fin a) (hδ : ∀ q ∈ F.domain.carrier, (q.2 δ).val ≠ iRVZero)
variable {B : SpecialTransformations.Section5.DefSet (M := M) (C.base : Set M) 1 b}
variable (T : SpecialBijection (nativeMixedVolumeDomain hc F.domain) B)
variable (hB : SpecialTransformations.Section5.IsRVPullback (carrier B))
variable (hT : GammaChainDefinable (⟨(C.base : Set M),Ξ⟩ : Base (M := M)) T.chain)
variable (L : RVLabelConstraintSpecialPreparation T
  (nativeMixedVolumeDomain hc (nativeCoordinateCoefficientFamily hc C F R σ ε hR hε).densityGraph.domain)
  (independentRVDensityConstraint hc C Ξ hNames R δ ε) (Fin.castAdd 1 ∘ Fin.castAdd d)
  (⟨(C.base : Set M),Ξ⟩ : Base (M := M)))

set_option maxHeartbeats 1600000 in
def coordinateCoefficientContractionProductIso :
    RVVolumeIso
      ((nativeCoordinateCoefficientFamily hc C F R σ ε hR hε).standardAppendObject hc Ξ
        (unarySpecialStandardContraction L.special L.pullback))
      ((nativeCoordinateDensityVolumeObject hc C R σ ε hR hε).prod
        (unaryPreparedHeadVolumeObject hc C Ξ T hB hT F.selected δ hδ F.finite_selected)) := by
  let J := nativeCoordinateCoefficientFamily hc C F R σ ε hR hε
  let Q := independentRVLabelConstraint C Ξ hNames a R
  let g := nativeRVLabelProduct hc Q (Fin.natAdd a ε) (Fin.castAdd d δ)
  let Φ := independentRVGraphFactorization C Ξ hNames a R g
  let hΦ := independent_rv_graph_factorization_bijective C Ξ hNames a R g
  let hOld := independent_rv_graph_factorization_old_labels C Ξ hNames a R g
  let χ : Fin d → Fin ((a+d)+1) := Fin.castAdd 1 ∘ Fin.natAdd a
  let hCoef := independent_rv_graph_factorization_coefficient_labels C Ξ hNames a R g
  let τ := headAppendVolumeIndex (unarySpecialHeadPreparation T hB) F.selected
  let δB := Fin.natAdd 1 (suffixIndex (special_chain_rvArity_le T.chain) δ)
  let hFinB := unary_prepared_head_selected_finite C Ξ T hB hT F.selected F.finite_selected
  let hδB := unary_prepared_head_density_nonzero C T hB δ hδ
  let U := J.standardAppendObject hc Ξ (unarySpecialStandardContraction L.special L.pullback)
  let W := factoredHeadProductVolumeObject hc C L R Φ hΦ hOld χ hCoef σ τ ε δB hR hFinB hε hδB
  have hUW : U.underlying.obj.domain.carrier=W.underlying.obj.domain.carrier := rfl
  have hCoord (u : U.underlying.obj.domain) :
      W.underlying.obj.value ⟨u.val,hUW.le u.property⟩=U.underlying.obj.value u := by
    let q : headImage L.target := ⟨(Fin.elim0,u.val),(mem_rawVolumeContractionLabels hc _ u.val).mp u.property⟩
    change u.val ∘ Fin.append (m := p+1) (n := (k+1)+1) (L.headParameters ∘ χ ∘ σ)
      (L.headProjection ∘ τ) = u.val ∘ orderedAppendVolumeIndex
        (unarySpecialStandardContraction L.special L.pullback).program J.densityGraph.selected
    rw [unary_special_standard_append_index]
    exact (factored_head_product_source_coordinates hc (Fin.castAdd 1) L hB σ F.selected u).symm
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
