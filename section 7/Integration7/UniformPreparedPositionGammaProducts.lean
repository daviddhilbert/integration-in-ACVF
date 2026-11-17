module

public import Integration7.UniformPositionLabelFibreSlopes
public import IntegrationSection4.BalancedSlope

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! The Gamma volume-product equation holds on the whole prepared
mixed positioning family. The actual cell and both paradigms are
recovered from each point's retained old labels. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section5
open IntegrationInACVF.Section4 IntegrationInACVF.Section5

namespace IntegrationInACVF.Section7.UniformMixedCellPresentation
variable {M : Type} [sM : LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {G : Base (M := M)} {S : Set M} {m u v : ℕ}
variable {A : DefSet (M := M) S 2 m}

def positionMapExtended (F : UniformMixedCellPresentation G (carrier A))
    (hNames : commonRealNames G ⊆ S) {R : Set M} (hSR : S ⊆ R) :
    Map (extendBase (VerticalOffsets.keyImage (gammaRVGraphRefinement A F.parameters hNames)) hSR)
      (extendBase (F.positionImage hNames) hSR) :=
  @SpecialTransformations.DefinableGeometry.Map.extend LRV M (@CanonicalStructure.normalize M sM)
    (pointSpace 1 (m+F.arity)) (pointSpace 1 (m+F.arity)) S R
    (VerticalOffsets.keyImage (gammaRVGraphRefinement A F.parameters hNames)) (F.positionImage hNames)
    (Map.toImage (F.positionMap hNames)) hSR

set_option maxHeartbeats 2000000 in
theorem prepared_position_gamma_products_over_extension
    (F : UniformMixedCellPresentation G (carrier A)) (hBalanced : F.BalancedRows)
    (hNames : commonRealNames G ⊆ S) {R : Set M} (hSR : S ⊆ R)
    (hNonzero : ∀ a : A, (F.vertical.projection a).val.2 F.vertical.paradigm_index ≠ rv (0 : VF (M := M)))
    {K' : DefSet (M := M) R 1 u} {E' : DefSet (M := M) R 1 v}
    (TK : SpecialBijection (extendBase (VerticalOffsets.keyImage (gammaRVGraphRefinement A F.parameters hNames)) hSR) K')
    (TE : SpecialBijection (extendBase (F.positionImage hNames) hSR) E')
    (hK' : IsRVPullback (carrier K')) (hE' : IsRVPullback (carrier E'))
    (hc : Contractible (unaryConjugate TK TE (F.positionMapExtended hNames hSR)))
    (hback : Contractible (Map.inverse (unaryConjugate TK TE (F.positionMapExtended hNames hSR))
      (unaryConjugate_bijective TK TE _ (F.position_to_image_bijective hBalanced hNames))))
    (a : K') (ha : vfAt a.val 0 ≠ 0) :
    ∃ b : A, ∃ r : RV (M := M),
      (TK.inverseMap a).val.2 = Fin.append b.val.2 (F.parameters.toFun b) ∧
      Cells.IsBalanced (mixedPairFibre F.parameters b) (F.localPosition b) r
        ((F.vertical.projection b).val.2 F.vertical.paradigm_index) ∧
      Values.vrv r*Values.vfValueHom
          (vfAt (unaryConjugate TK TE (F.positionMapExtended hNames hSR) a).val 0) =
        Values.vfValueHom (vfAt a.val 0)*Values.vrv ((F.vertical.projection b).val.2 F.vertical.paradigm_index) := by
  obtain ⟨b,hb⟩ := F.tail_key_source hNames (TK.inverseMap a)
  have hLabels := congrArg (fun p : VerticalOffsets.keyImage (gammaRVGraphRefinement A F.parameters hNames) => p.val.2) hb
  obtain ⟨r,hBal⟩ := hBalanced b
  have hBal' := hBal
  obtain ⟨_,_,hFib,_,s,hLin⟩ := hBal'
  have hbD : vfAt b.val 1 ∈ Cells.first (mixedPairFibre F.parameters b) := by
    refine ⟨(vfAt b.val 1,vfAt b.val 0),⟨b,?_,rfl⟩,rfl⟩
    funext i
    fin_cases i <;> rfl
  have hr : r ≠ rv (0 : VF (M := M)) := fun h =>
    hNonzero b ((BalancedFibres.paradigms_degenerate_together hFib (vfAt b.val 1) hbD).mp h)
  have hRatio := prepared_unary_gamma_value_ratio_on_fibre TK TE (F.positionMapExtended hNames hSR)
    (F.position_to_image_bijective hBalanced hNames) hK' hE' hc hback s a ha (by
      intro x y hx hy
      exact F.position_map_gamma_linear_of_centre hNames b s (F.centre_gamma_linear_of_row b s hLin)
        x y (hx.trans hLabels) (hy.trans hLabels))
  have hSlope := BalancedSlope.remark_4_6 hFib hr (vfAt b.val 1) hbD s hLin
  have hr0 : Values.vrv r ≠ 0 := by
    intro he
    apply hr
    apply Subtype.ext
    exact ((Values.vrv_eq_infinity_iff r).mp (he.trans Values.infinity_eq_zero.symm)).trans
      ((CanonicalRV.encodedRv_zero_iff (0 : VFType (M := M))).mpr rfl).symm
  refine ⟨b,r,hLabels,hBal,?_⟩
  rw [hRatio,hSlope]
  calc
    Values.vrv r*((Values.vrv ((F.vertical.projection b).val.2 F.vertical.paradigm_index)/Values.vrv r)*
        Values.vfValueHom (vfAt a.val 0)) =
      ((Values.vrv ((F.vertical.projection b).val.2 F.vertical.paradigm_index)/Values.vrv r)*Values.vrv r)*
        Values.vfValueHom (vfAt a.val 0) := by ac_rfl
    _ = _ := by rw [div_mul_cancel₀ _ hr0,mul_comm]

end IntegrationInACVF.Section7.UniformMixedCellPresentation
