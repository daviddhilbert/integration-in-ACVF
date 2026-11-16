module

public import Integration7.OrdinaryCoefficientContractionProductCharts
public import Integration7.UnaryPreparedFiniteHeadObjects
public import Integration7.OrdinaryVolumeFamilyScalarProducts

@[expose] public section

/-! The same finite-coefficient preparation compares raw unary
contractions with no old selected coordinates. The volume remains degree
one, so no cancellation of an artificially added unit is required. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section5 (VF RV carrier headImage SpecialBijection GammaChainDefinable)
open IntegrationInACVF.Section5 IntegrationInACVF.Section6
namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {a b k : ℕ}

theorem unary_special_standard_volume_index {S : Set M}
    {A : SpecialTransformations.Section5.DefSet (M := M) S 1 a}
    {B : SpecialTransformations.Section5.DefSet (M := M) S 1 b}
    (T : SpecialBijection A B) (hB : SpecialTransformations.Section5.IsRVPullback (carrier B)) :
    (unarySpecialStandardContraction T hB).volumeIndex=Fin.castAdd b := by
  funext i
  have hi : i=0 := Subsingleton.elim _ _
  subst i
  change (orderedCastSource (unarySpecialContractionProgram T hB) _).volumeIndex 0=Fin.castAdd b 0
  rw [orderedCastSource_volumeIndex]
  apply Fin.ext
  simp [unarySpecialContractionProgram,OrderedContractionProgram.volumeIndex,suffixIndex]

variable (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
variable (Ξ : Set (Values.Gamma (M := M)))
variable (hNames : commonRealNames (⟨(C.base : Set M),Ξ⟩ : Base (M := M)) ⊆ (C.base : Set M))
variable (F : SelectedVFVolumeFamily C 1 a k) (Z : RVFiniteObject (M := M) (C.base : Set M) 0)
variable (hfin : ∀ x : Fin 1 → VF (M := M), {r : Fin a → RV (M := M) | (x,r) ∈ F.domain.carrier}.Finite)
variable (δ : Fin a) (hδ : ∀ q ∈ F.domain.carrier, (q.2 δ).val ≠ iRVZero)
variable {B : SpecialTransformations.Section5.DefSet (M := M) (C.base : Set M) 1 b}
variable (T : SpecialBijection (nativeMixedVolumeDomain hc F.domain) B)
variable (hB : SpecialTransformations.Section5.IsRVPullback (carrier B))
variable (hT : GammaChainDefinable (⟨(C.base : Set M),Ξ⟩ : Base (M := M)) T.chain)
variable (L : RVLabelConstraintSpecialPreparation T (nativeMixedVolumeDomain hc (F.prodZero Z).domain)
  (independentRVLabelConstraint C Ξ hNames a (ordinaryRVNativeDomain hc C Z))
  (Fin.castAdd Z.obj.arity) (⟨(C.base : Set M),Ξ⟩ : Base (M := M)))

private def finiteProductLabels :=
  (({domain := F.domain,finite_labels := hfin} : OrdinaryVFVolumeFamily C 1 a).prodZero Z).finite_labels

set_option maxHeartbeats 1600000 in
def ordinaryFiniteCoefficientContractionIso :
    RVVolumeIso
      (rawStandardVolumeObject hc C Ξ (nativeMixedVolumeDomain hc (F.prodZero Z).domain)
        (finiteProductLabels C F Z hfin) (Fin.castAdd Z.obj.arity δ)
        (fun q hq => ordinary_coefficient_retained_density_nonzero C F Z δ hδ ⟨q,hq⟩)
        (unarySpecialStandardContraction L.special L.pullback))
      (PositiveRVVolumeObject.zero_prod
        (nativeOrdinaryRVObject hc C (ordinaryRVNativeDomain hc C Z) (ordinary_rv_native_labels_finite hc C Z))
        (unaryPreparedFiniteHeadObject hc C Ξ T hB hT hfin δ hδ)) := by
  let R := ordinaryRVNativeDomain hc C Z
  let hQ := independent_rv_label_constraint_mem C Ξ hNames a R
  let f := L.independentHeadProductMap R hQ
  let hf := L.independent_head_product_map_bijective R hQ
  let τ : Fin 1 → Fin (1+b) := Fin.castAdd b
  let δB := Fin.natAdd 1 (suffixIndex (special_chain_rvArity_le T.chain) δ)
  let hFinB := unary_prepared_finite_head_fibres C Ξ T hB hT hfin
  let hδB := unary_prepared_head_density_nonzero C T hB δ hδ
  let hR := ordinary_rv_native_labels_finite hc C Z
  let J := F.prodZero Z
  let δJ := Fin.castAdd Z.obj.arity δ
  let hδJ := fun q hq => ordinary_coefficient_retained_density_nonzero C F Z δ hδ ⟨q,hq⟩
  let hfinJ := finiteProductLabels C F Z hfin
  let S := unarySpecialStandardContraction L.special L.pullback
  let U := selectedStandardVolumeObject hc C Ξ (nativeMixedVolumeDomain hc J.domain) (Fin.elim0 : Fin 0 → Fin (a+Z.obj.arity))
    δJ hδJ (fun x _ => (hfinJ x).subset (fun _ h => h.1)) S
  let W := nativeOrdinaryRVProductVolumeChart hc C (headImage L.target) R (headImage B) f hf
    L.headProjection (fun _ => rfl) hR τ δB hFinB hδB
  have hUW : U.underlying.obj.domain.carrier=W.underlying.obj.domain.carrier := rfl
  have hCoord (u : U.underlying.obj.domain) :
      W.underlying.obj.value ⟨u.val,hUW.le u.property⟩=U.underlying.obj.value u := by
    change u.val ∘ (L.headProjection ∘ τ)=u.val ∘ selectedStandardVolumeIndex S Fin.elim0
    rw [unary_standard_empty_selected_index,unary_special_standard_volume_index]
    funext i
    have hi : i=0 := Subsingleton.elim _ _
    subst i
    rfl
  have hForm (u : U.underlying.obj.domain) : W.form.value ⟨u.val,hUW.le u.property⟩=U.form.value u := by
    let q : headImage L.target := ⟨(Fin.elim0,u.val),(mem_rawVolumeContractionLabels hc _ u.val).mp u.property⟩
    have h := native_ordinary_rv_product_volume_chart_density hc C (headImage L.target) R (headImage B) f hf
      L.headProjection (fun _ => rfl) hR τ δB hFinB hδB ⟨u.val,hUW.le u.property⟩
    change W.form.value ⟨u.val,hUW.le u.property⟩=u.val (suffixIndex S.program.rvArity_le δJ)
    rw [← standard_append_density_index,unary_special_standard_density_index]
    exact h.trans (L.head_prepared_old_labels q δ)
  let e : U.underlying ≅ W.underlying := rvFiniteIsoOfAmbient (U := U.underlying) (V := W.underlying)
    (rvIsoOfCarrierEq U.underlying.obj.domain W.underlying.obj.domain U.underlying.obj.volume W.underlying.obj.volume hUW hCoord)
  exact ((unaryRawSelectedVolumeIso hc C Ξ (nativeMixedVolumeDomain hc J.domain) hfinJ δJ hδJ S).symm hc C).trans hc C
    ((RVVolumeIso.of_preserving_coordinates_full hc C e hCoord hForm).trans hc C
      (nativeOrdinaryRVProductVolumeChartIso hc C (headImage L.target) R (headImage B) f hf
        L.headProjection (fun _ => rfl) hR τ δB hFinB hδB))
end IntegrationInACVF.Section7
