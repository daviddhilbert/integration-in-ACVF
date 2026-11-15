import Integration7.UnarySpecialStandardContractions
import Integration7.NativeCoordinateDensityVolumeObjects
import Section4.RVIsoTools

/-! The actual appended standard contraction of a unary special
preparation is volume-isomorphic to the literal coordinate-density
object on its head image. Finiteness is proved from the original family. -/
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
variable (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
variable (Ξ : Set (Values.Gamma (M := M)))
variable {A : SpecialTransformations.Section5.DefSet (M := M) (C.base : Set M) 1 a}
variable {B : SpecialTransformations.Section5.DefSet (M := M) (C.base : Set M) 1 b}
variable (T : SpecialBijection A B)
variable (hB : SpecialTransformations.Section5.IsRVPullback (carrier B))
variable (hT : GammaChainDefinable (⟨(C.base : Set M),Ξ⟩ : Base (M := M)) T.chain)
variable (ρ : Fin (k+1) → Fin a) (δ : Fin a)
variable (hδ : ∀ q ∈ carrier A, (q.2 δ).val ≠ iRVZero)
variable (hfin : ∀ (x : Fin 1 → VF (M := M)) (t : Fin (k+1) → RV (M := M)),
  {r : Fin a → RV (M := M) | (x,r) ∈ carrier A ∧ r ∘ ρ=t}.Finite)

include hT hfin in
theorem unary_prepared_head_selected_finite (t : Fin ((k+1)+1) → RV (M := M)) :
    {r : Fin (1+b) → RV (M := M) | (Fin.elim0,r) ∈ carrier (headImage B) ∧
      r ∘ headAppendVolumeIndex (unarySpecialHeadPreparation T hB) ρ=t}.Finite := by
  have hΓ := gamma_unary_special_contraction_program T hB hT
  exact head_append_selected_fibres_finite C.uncountable.le C.saturated C.small
    (unarySpecialHeadPreparation T hB) hΓ.1 hΓ.2.1 ρ hfin Fin.elim0 t

include hB hδ in
theorem unary_prepared_head_density_nonzero (q : headImage B) :
    (q.val.2 (Fin.natAdd 1 (suffixIndex (special_chain_rvArity_le T.chain) δ))).val ≠ iRVZero :=
  head_retained_density_nonzero (unarySpecialHeadPreparation T hB) δ hδ q.val q.property

def unaryPreparedHeadVolumeObject : PositiveRVVolumeObject (M := M) (C.base : Set M) (k+1) :=
  nativeCoordinateDensityVolumeObject hc C (headImage B) (headAppendVolumeIndex (unarySpecialHeadPreparation T hB) ρ)
    (Fin.natAdd 1 (suffixIndex (special_chain_rvArity_le T.chain) δ))
    (unary_prepared_head_selected_finite C Ξ T hB hT ρ hfin)
    (unary_prepared_head_density_nonzero C T hB δ hδ)

def unaryPreparedHeadVolumeIso :
    RVVolumeIso (standardAppendVolumeObject hc C Ξ A ρ δ hδ hfin (unarySpecialStandardContraction T hB))
      (unaryPreparedHeadVolumeObject hc C Ξ T hB hT ρ δ hδ hfin) := by
  let U := standardAppendVolumeObject hc C Ξ A ρ δ hδ hfin (unarySpecialStandardContraction T hB)
  let V := unaryPreparedHeadVolumeObject hc C Ξ T hB hT ρ δ hδ hfin
  have hUV : U.underlying.obj.domain.carrier=V.underlying.obj.domain.carrier := rfl
  have hCoord (u : U.underlying.obj.domain) :
      V.underlying.obj.value ⟨u.val,hUV.le u.property⟩=U.underlying.obj.value u := by
    change u.val ∘ headAppendVolumeIndex (unarySpecialHeadPreparation T hB) ρ =
      u.val ∘ orderedAppendVolumeIndex (unarySpecialStandardContraction T hB).program ρ
    rw [unary_special_standard_append_index]
  have hForm (u : U.underlying.obj.domain) : V.form.value ⟨u.val,hUV.le u.property⟩=U.form.value u := by
    change u.val (Fin.natAdd 1 (suffixIndex (special_chain_rvArity_le T.chain) δ)) =
      u.val (orderedAppendDensityIndex (unarySpecialStandardContraction T hB).program δ)
    rw [unary_special_standard_density_index]
  let e : U.underlying ≅ V.underlying := rvFiniteIsoOfAmbient (U := U.underlying) (V := V.underlying)
    (rvIsoOfCarrierEq U.underlying.obj.domain V.underlying.obj.domain U.underlying.obj.volume V.underlying.obj.volume hUV hCoord)
  exact RVVolumeIso.of_preserving_coordinates_full hc C e hCoord hForm
end IntegrationInACVF.Section7
