module

public import Integration7.HKNativeZeroFiniteCoefficientPreparations
public import Integration7.FieldBaseUnaryVolumeIntegrals
public import Integration7.UnaryPreparedFiniteHeadObjects
public import Integration7.UnaryPreparedHeadVolumeObjects
public import Integration7.FactoredHeadAppendedVolumeCoordinates
public import Integration7.HKFactoredHeadZeroProductCharts
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
namespace IntegrationInACVF.Section7.HK
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {a b d k p : ℕ}
variable (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
variable (Ξ : Set (Values.Gamma (M := M)))
variable (hNames : commonRealNames (⟨(C.base : Set M),Ξ⟩ : Base (M := M)) ⊆ (C.base : Set M))
variable (F : ZeroVFVolumeFamily C 1 a)
variable (R : SpecialTransformations.Section5.DefSet (M := M) (C.base : Set M) 0 d)
variable (ε : Fin d)
variable (hR : (rawVolumeContractionLabels hc R).carrier.Finite)
variable (hε : ∀ q : R, (q.val.2 ε).val ≠ iRVZero)
variable (δ : Fin a) (hδ : ∀ q ∈ F.domain.carrier, (q.2 δ).val ≠ iRVZero)
variable {B : SpecialTransformations.Section5.DefSet (M := M) (C.base : Set M) 1 b}
variable (T : SpecialBijection (nativeMixedVolumeDomain hc F.domain) B)
variable (hB : SpecialTransformations.Section5.IsRVPullback (carrier B))
variable (hT : GammaChainDefinable (⟨(C.base : Set M),Ξ⟩ : Base (M := M)) T.chain)
variable (L : RVLabelConstraintSpecialPreparation T
  (nativeMixedVolumeDomain hc (nativeZeroFiniteCoefficientFamily hc C F R ε hR hε).fullVFObject.densityGraph.domain)
  (independentRVDensityConstraint hc C Ξ hNames R δ ε) (Fin.castAdd 1 ∘ Fin.castAdd d)
  (⟨(C.base : Set M),Ξ⟩ : Base (M := M)))

set_option maxHeartbeats 1600000 in
def zeroFiniteCoefficientContractionProductIso :
    RVVolumeIso
      (rawStandardVolumeObject hc C Ξ
        (nativeMixedVolumeDomain hc (nativeZeroFiniteCoefficientFamily hc C F R ε hR hε).fullVFObject.densityGraph.domain)
        (nativeZeroFiniteCoefficientFamily hc C F R ε hR hε).fullVFObject.densityGraph.finite_labels
        (Fin.last (a+d)) (unary_density_graph_label_nonzero
          (nativeZeroFiniteCoefficientFamily hc C F R ε hR hε).fullVFObject)
        (unarySpecialStandardContraction L.special L.pullback))
      (zeroProduct (nativeZeroDensityObject hc C R ε hR hε)
        (unaryPreparedFiniteHeadObject hc C Ξ T hB hT F.finite_labels δ hδ)) := by
  let J := nativeZeroFiniteCoefficientFamily hc C F R ε hR hε
  let Q := independentRVLabelConstraint C Ξ hNames a R
  let g := nativeRVLabelProduct hc Q (Fin.natAdd a ε) (Fin.castAdd d δ)
  let Φ := independentRVGraphFactorization C Ξ hNames a R g
  let hΦ := independent_rv_graph_factorization_bijective C Ξ hNames a R g
  let hOld := independent_rv_graph_factorization_old_labels C Ξ hNames a R g
  let χ : Fin d → Fin ((a+d)+1) := Fin.castAdd 1 ∘ Fin.natAdd a
  let hCoef := independent_rv_graph_factorization_coefficient_labels C Ξ hNames a R g
  let τ : Fin 1 → Fin (1+b) := Fin.castAdd b
  let δB := Fin.natAdd 1 (suffixIndex (special_chain_rvArity_le T.chain) δ)
  let hFinB := unary_prepared_finite_head_fibres C Ξ T hB hT F.finite_labels
  let hδB := unary_prepared_head_density_nonzero C T hB δ hδ
  let U := unaryPreparedFiniteHeadObject hc C Ξ L.special L.pullback L.gamma
    J.fullVFObject.densityGraph.finite_labels (Fin.last (a+d)) (unary_density_graph_label_nonzero J.fullVFObject)
  let W := factoredHeadZeroProductVolumeObject hc C L R Φ hΦ hOld τ ε δB hR hFinB hε hδB
  have hUW : U.underlying.obj.domain.carrier=W.underlying.obj.domain.carrier := rfl
  have hCoord (u : U.underlying.obj.domain) :
      W.underlying.obj.value ⟨u.val,hUW.le u.property⟩=U.underlying.obj.value u := by
    let q : headImage L.target := ⟨(Fin.elim0,u.val),(mem_rawVolumeContractionLabels hc _ u.val).mp u.property⟩
    change u.val ∘ (L.headProjection ∘ τ) = u.val ∘ Fin.castAdd L.arity
    funext i
    have hi : i=0 := Subsingleton.elim _ _
    subst i
    rfl
  have hForm (u : U.underlying.obj.domain) : W.form.value ⟨u.val,hUW.le u.property⟩=U.form.value u := by
    let q : headImage L.target := ⟨(Fin.elim0,u.val),(mem_rawVolumeContractionLabels hc _ u.val).mp u.property⟩
    calc
      W.form.value ⟨u.val,hUW.le u.property⟩ =
          u.val (L.headParameters (χ ε))*u.val (L.headProjection δB) :=
        factored_head_zero_product_volume_density hc C L R Φ hΦ hOld χ hCoef τ ε δB hR hFinB hε hδB _
      _ = U.form.value u := by
        change _ = u.val (Fin.natAdd 1 (suffixIndex
          (special_chain_rvArity_le L.special.chain) (Fin.last (a+d))))
        apply Subtype.ext
        rw [RVOperations.mul_val]
        exact (independent_rv_prepared_head_density_suffix hc C Ξ hNames R δ ε L q).symm
  let e : U.underlying ≅ W.underlying := rvFiniteIsoOfAmbient (U := U.underlying) (V := W.underlying)
    (rvIsoOfCarrierEq U.underlying.obj.domain W.underlying.obj.domain U.underlying.obj.volume W.underlying.obj.volume hUW hCoord)
  exact (unaryPreparedFiniteHeadIso hc C Ξ L.special L.pullback L.gamma
    J.fullVFObject.densityGraph.finite_labels (Fin.last (a+d)) (unary_density_graph_label_nonzero J.fullVFObject)).trans hc C
    ((RVVolumeIso.of_preserving_coordinates_full hc C e hCoord hForm).trans hc C
    (factoredHeadZeroProductVolumeIso hc C L R Φ hΦ hOld τ ε δB hR hFinB hε hδB))
end IntegrationInACVF.Section7.HK
