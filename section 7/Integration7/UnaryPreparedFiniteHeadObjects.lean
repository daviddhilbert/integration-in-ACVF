import Integration7.UnaryPreparedHeadVolumeObjects
import Integration7.UnaryUnitSelectedContractionCharts

/-! A finite-label unary source has a genuine degree-one prepared head
object without old selected coordinates. Its full coordinate-density
chart is the actual raw unary contraction. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section5 (VF RV carrier headImage SpecialBijection GammaChainDefinable)
open IntegrationInACVF.Section5 IntegrationInACVF.Section6
namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {a b : ℕ}
variable (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
variable (Ξ : Set (Values.Gamma (M := M)))
variable {A : SpecialTransformations.Section5.DefSet (M := M) (C.base : Set M) 1 a}
variable {B : SpecialTransformations.Section5.DefSet (M := M) (C.base : Set M) 1 b}
variable (T : SpecialBijection A B)
variable (hB : SpecialTransformations.Section5.IsRVPullback (carrier B))
variable (hT : GammaChainDefinable (⟨(C.base : Set M),Ξ⟩ : Base (M := M)) T.chain)
variable (hfin : ∀ x : Fin 1 → VF (M := M), {r : Fin a → RV (M := M) | (x,r) ∈ carrier A}.Finite)
variable (δ : Fin a) (hδ : ∀ q ∈ carrier A, (q.2 δ).val ≠ iRVZero)

include hB hT hfin in
theorem unary_prepared_finite_head_fibres (t : Fin 1 → RV (M := M)) :
    {r : Fin (1+b) → RV (M := M) | (Fin.elim0,r) ∈ carrier (headImage B) ∧
      r ∘ (Fin.castAdd b : Fin 1 → Fin (1+b))=t}.Finite := by
  have hΓ := gamma_unary_special_contraction_program T hB hT
  apply (head_selected_fibres_finite C.uncountable.le C.saturated C.small
    (unarySpecialHeadPreparation T hB) hΓ.1 hΓ.2.1 (Fin.elim0 : Fin 0 → Fin a)
    (fun x _ => (hfin x).subset (fun _ h => h.1)) Fin.elim0 t).subset
  rintro r ⟨hr,ht⟩
  refine ⟨hr,?_⟩
  funext i
  refine Fin.addCases (m := 1) (n := 0) (fun j => ?_) (fun j => Fin.elim0 j) i
  have hIndex : headVolumeIndex (unarySpecialHeadPreparation T hB) (Fin.elim0 : Fin 0 → Fin a)
      (Fin.castAdd 0 j)=Fin.castAdd b j := Fin.append_left _ _ j
  have hJ : (Fin.castAdd 0 j : Fin 1)=j := Fin.ext rfl
  change r (headVolumeIndex (unarySpecialHeadPreparation T hB) Fin.elim0 (Fin.castAdd 0 j)) = t (Fin.castAdd 0 j)
  rw [hIndex,hJ]
  exact congrFun ht j

def unaryPreparedFiniteHeadObject : PositiveRVVolumeObject (M := M) (C.base : Set M) 0 :=
  nativeCoordinateDensityVolumeObject hc C (headImage B) (Fin.castAdd b)
    (Fin.natAdd 1 (suffixIndex (special_chain_rvArity_le T.chain) δ))
    (unary_prepared_finite_head_fibres C Ξ T hB hT hfin)
    (unary_prepared_head_density_nonzero C T hB δ hδ)

def unaryPreparedFiniteHeadIso :
    RVVolumeIso
      (rawStandardVolumeObject hc C Ξ A hfin δ hδ (unarySpecialStandardContraction T hB))
      (unaryPreparedFiniteHeadObject hc C Ξ T hB hT hfin δ hδ) := by
  let S := unarySpecialStandardContraction T hB
  let U := selectedStandardVolumeObject hc C Ξ A (Fin.elim0 : Fin 0 → Fin a) δ hδ
    (fun x _ => (hfin x).subset (fun _ h => h.1)) S
  let V := unaryPreparedFiniteHeadObject hc C Ξ T hB hT hfin δ hδ
  have hUV : U.underlying.obj.domain.carrier=V.underlying.obj.domain.carrier := rfl
  have hCoord (u : U.underlying.obj.domain) :
      V.underlying.obj.value ⟨u.val,hUV.le u.property⟩=U.underlying.obj.value u := by
    change u.val ∘ Fin.castAdd b = u.val ∘ selectedStandardVolumeIndex S (Fin.elim0 : Fin 0 → Fin a)
    rw [unary_standard_empty_selected_index]
    funext i
    have hi : i=0 := Subsingleton.elim _ _
    subst i
    apply congrArg u.val
    change Fin.castAdd b 0=(orderedCastSource (unarySpecialContractionProgram T hB) _).volumeIndex 0
    rw [orderedCastSource_volumeIndex]
    apply Fin.ext
    simp [unarySpecialContractionProgram,OrderedContractionProgram.volumeIndex,suffixIndex]
  have hForm (u : U.underlying.obj.domain) : V.form.value ⟨u.val,hUV.le u.property⟩=U.form.value u := by
    change u.val (Fin.natAdd 1 (suffixIndex (special_chain_rvArity_le T.chain) δ)) =
      u.val (suffixIndex S.program.rvArity_le δ)
    rw [← standard_append_density_index,unary_special_standard_density_index]
  let e : U.underlying ≅ V.underlying := rvFiniteIsoOfAmbient (U := U.underlying) (V := V.underlying)
    (rvIsoOfCarrierEq U.underlying.obj.domain V.underlying.obj.domain U.underlying.obj.volume V.underlying.obj.volume hUV hCoord)
  exact (unaryRawSelectedVolumeIso hc C Ξ A hfin δ hδ S).symm hc C |>.trans hc C
    (RVVolumeIso.of_preserving_coordinates_full hc C e hCoord hForm)
end IntegrationInACVF.Section7
