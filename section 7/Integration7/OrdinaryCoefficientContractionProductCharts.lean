module

public import Integration7.OrdinaryCoefficientSpecialPreparations
public import Integration7.NativeOrdinaryRVProductVolumeCharts
public import Integration7.UnaryPreparedHeadVolumeObjects
public import Integration7.IndependentHeadRetainedLabels

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! A degree-zero finite coefficient gives a genuine product chart for
an original-label retained-density contraction. Its contribution is an
ordinary RV[0] factor and the positive family's density is unchanged. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section5 (RV carrier headImage SpecialBijection GammaChainDefinable)
open IntegrationInACVF.Section5 IntegrationInACVF.Section6
namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {a b k : ℕ}
variable (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
variable (Ξ : Set (Values.Gamma (M := M)))
variable (hNames : commonRealNames (⟨(C.base : Set M),Ξ⟩ : Base (M := M)) ⊆ (C.base : Set M))
variable (F : SelectedVFVolumeFamily C 1 a k) (Z : RVFiniteObject (M := M) (C.base : Set M) 0)
variable (δ : Fin a) (hδ : ∀ q ∈ F.domain.carrier, (q.2 δ).val ≠ iRVZero)
variable {B : SpecialTransformations.Section5.DefSet (M := M) (C.base : Set M) 1 b}
variable (T : SpecialBijection (nativeMixedVolumeDomain hc F.domain) B)
variable (hB : SpecialTransformations.Section5.IsRVPullback (carrier B))
variable (hT : GammaChainDefinable (⟨(C.base : Set M),Ξ⟩ : Base (M := M)) T.chain)
variable (L : RVLabelConstraintSpecialPreparation T (nativeMixedVolumeDomain hc (F.prodZero Z).domain)
  (independentRVLabelConstraint C Ξ hNames a (ordinaryRVNativeDomain hc C Z))
  (Fin.castAdd Z.obj.arity) (⟨(C.base : Set M),Ξ⟩ : Base (M := M)))

include hδ in
theorem ordinary_coefficient_retained_density_nonzero
    (q : (F.prodZero Z).domain) : (q.val.2 (Fin.castAdd Z.obj.arity δ)).val ≠ iRVZero := by
  have h := (mem_mixed_rv_factor_domain F.domain Z.obj.domain q.val.1 q.val.2).mp q.property
  exact hδ (q.val.1,q.val.2 ∘ Fin.castAdd Z.obj.arity) h.1

set_option maxHeartbeats 1600000 in
def ordinaryCoefficientContractionProductIso :
    RVVolumeIso
      (standardAppendVolumeObject hc C Ξ (nativeMixedVolumeDomain hc (F.prodZero Z).domain)
        (F.prodZero Z).selected (Fin.castAdd Z.obj.arity δ)
        (fun q hq => ordinary_coefficient_retained_density_nonzero C F Z δ hδ ⟨q,hq⟩)
        (F.prodZero Z).finite_selected (unarySpecialStandardContraction L.special L.pullback))
      (PositiveRVVolumeObject.zero_prod
        (nativeOrdinaryRVObject hc C (ordinaryRVNativeDomain hc C Z) (ordinary_rv_native_labels_finite hc C Z))
        (unaryPreparedHeadVolumeObject hc C Ξ T hB hT F.selected δ hδ F.finite_selected)) := by
  let R := ordinaryRVNativeDomain hc C Z
  let hQ := independent_rv_label_constraint_mem C Ξ hNames a R
  let f := L.independentHeadProductMap R hQ
  let hf := L.independent_head_product_map_bijective R hQ
  let τ := headAppendVolumeIndex (unarySpecialHeadPreparation T hB) F.selected
  let δB := Fin.natAdd 1 (suffixIndex (special_chain_rvArity_le T.chain) δ)
  let hFinB := unary_prepared_head_selected_finite C Ξ T hB hT F.selected F.finite_selected
  let hδB := unary_prepared_head_density_nonzero C T hB δ hδ
  let hR := ordinary_rv_native_labels_finite hc C Z
  let J := F.prodZero Z
  let δJ := Fin.castAdd Z.obj.arity δ
  let hδJ := fun q hq => ordinary_coefficient_retained_density_nonzero C F Z δ hδ ⟨q,hq⟩
  let U := standardAppendVolumeObject hc C Ξ (nativeMixedVolumeDomain hc J.domain) J.selected δJ hδJ J.finite_selected
    (unarySpecialStandardContraction L.special L.pullback)
  let W := nativeOrdinaryRVProductVolumeChart hc C (headImage L.target) R (headImage B) f hf
    L.headProjection (fun _ => rfl) hR τ δB hFinB hδB
  have hUW : U.underlying.obj.domain.carrier=W.underlying.obj.domain.carrier := rfl
  have hCoord (u : U.underlying.obj.domain) :
      W.underlying.obj.value ⟨u.val,hUW.le u.property⟩=U.underlying.obj.value u := by
    let q : headImage L.target := ⟨(Fin.elim0,u.val),(mem_rawVolumeContractionLabels hc _ u.val).mp u.property⟩
    change u.val ∘ (L.headProjection ∘ τ)=u.val ∘ orderedAppendVolumeIndex
      (unarySpecialStandardContraction L.special L.pullback).program J.selected
    rw [unary_special_standard_append_index]
    funext i
    refine Fin.addCases (m := k+1) (n := 1) (fun j => ?_) (fun j => ?_) i
    · simp only [Function.comp_apply,τ,headAppendVolumeIndex,Fin.append_left]
      exact L.head_prepared_old_labels q (F.selected j)
    · have hj : j=0 := Subsingleton.elim _ _
      subst j
      simp only [Function.comp_apply,τ,headAppendVolumeIndex,Fin.append_right,
        RVLabelConstraintSpecialPreparation.headProjection,Fin.append_left]
      rfl
  have hForm (u : U.underlying.obj.domain) : W.form.value ⟨u.val,hUW.le u.property⟩=U.form.value u := by
    let q : headImage L.target := ⟨(Fin.elim0,u.val),(mem_rawVolumeContractionLabels hc _ u.val).mp u.property⟩
    have h := native_ordinary_rv_product_volume_chart_density hc C (headImage L.target) R (headImage B) f hf
      L.headProjection (fun _ => rfl) hR τ δB hFinB hδB ⟨u.val,hUW.le u.property⟩
    change W.form.value ⟨u.val,hUW.le u.property⟩=u.val (orderedAppendDensityIndex
      (unarySpecialStandardContraction L.special L.pullback).program δJ)
    rw [unary_special_standard_density_index]
    exact h.trans (L.head_prepared_old_labels q δ)
  let e : U.underlying ≅ W.underlying := rvFiniteIsoOfAmbient (U := U.underlying) (V := W.underlying)
    (rvIsoOfCarrierEq U.underlying.obj.domain W.underlying.obj.domain U.underlying.obj.volume W.underlying.obj.volume hUW hCoord)
  exact (RVVolumeIso.of_preserving_coordinates_full hc C e hCoord hForm).trans hc C
    (nativeOrdinaryRVProductVolumeChartIso hc C (headImage L.target) R (headImage B) f hf
      L.headProjection (fun _ => rfl) hR τ δB hFinB hδB)
end IntegrationInACVF.Section7
