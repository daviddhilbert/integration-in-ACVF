import Integration7.GammaDefinableNameContexts
import Integration7.NonbalancedCellContractionComparisons
import Integration7.BalancedCellOppositeOrderComparisons
import Integration7.NativeBalancedTranslationCommonNames
import Integration7.DegenerateCellContractionComparisons

/-! All actual definable two-cells compare in opposite contraction
orders. Their positioning and RV paradigms are obtained from the cell
data; a definably closed name context supplies the real presentations
and preserves independence over the original Gamma base. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section5
open IntegrationInACVF.Section5
open IntegrationInACVF.Section4 IntegrationInACVF.Section4.Cells

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {P : Base (M := M)} {d : ℕ}

set_option maxHeartbeats 1600000 in
theorem gamma_definable_named_cell_contraction_comparison
    (hc : CanonicalStructure.IsCanonical (M := M)) (C0 : BaseContext M)
    (hP0 : P.real ⊆ (C0.base : Set M)) (hBase : P.real = (C0.base : Set M))
    (hgamma : Cardinal.mk P.gamma < C0.κ)
    (γ : Values.Gamma (M := M)) (hγ : γ ∈ P.gamma) (hγ1 : 1 < γ) :
    let C := gammaDefinableNamesVolumeContext hc C0 P hP0 hgamma
    let hPC : P.real ⊆ (C.base : Set M) := fun _ hx =>
      gamma_definable_names_context_contains hc C0 P hP0 hgamma (Or.inl (hP0 hx))
    ∀ (Z : DefSet (M := M) (C.base : Set M) 2 0) (hZ : GammaSetDefinable P (carrier Z))
    (hDef : Cells.DefinableTwoCell P (nativeVFPairDomain Z))
    (z : Fin d → RV (M := M)) (hz : ∀ j, (z j).val ∈ (C.base : Set M))
    (hzΓ : DefinableOverBase P (fun _ : Fin d => .rv) {fun j => (z j).val})
    (j : Fin d) (η : RV (M := M)) (hj : z j = η) (hη0 : η ≠ 0)
    (T : StandardContraction (fixedRVLabelDomain Z z hz) (Equiv.refl _))
    (W : StandardContraction (fixedRVLabelDomain Z z hz) (Equiv.swap 0 1))
    (hT : GammaProgramDefinable P T.program) (hW : GammaProgramDefinable P W.program),
    let hsmall : Cardinal.mk P.real < C.κ := (Cardinal.mk_le_mk_of_subset hPC).trans_lt C.small
    let U := fixedLabelContractionGammaObject C.uncountable.le C.saturated hsmall hc C hPC Z hZ z hz hzΓ j η hj hη0 T hT
    let V := fixedLabelContractionGammaObject C.uncountable.le C.saturated hsmall hc C hPC Z hZ z hz hzΓ j η hj hη0 W hW
    ∃ (K : BaseContext M) (hCK : (C.base : Set M) ⊆ (K.base : Set M)),
      GammaVolumeBlowupEquivalent P (K.base : Set M) 1 (U.extend hCK) (V.extend hCK) := by
  intro C hPC Z hZ hDef z hz hzΓ j η hj hη0 T W hT hW hsmall U V
  classical
  obtain ⟨f,t,hCell,hPairΓ,hfΓ,htΓ,hParΓ⟩ := hDef
  have hNames : commonRealNames P ⊆ (C.base : Set M) := fun _ hx =>
    gamma_definable_names_context_contains hc C0 P hP0 hgamma (Or.inr hx)
  have hGeneric : ∀ {p : ℕ} (x : Fin p → VF (M := M)), AlgebraicIndependent (vfParameterField P.real) x →
      AlgebraicIndependent (vfParameterField (C.base : Set M)) x :=
    fun x hx => gamma_definable_names_context_preserves_independence hc C0 P hP0 hgamma hBase x hx
  have hη : η.val ∈ (C.base : Set M) := (congrArg (fun a : RV (M := M) => a.val ∈ (C.base : Set M)) hj).mp (hz j)
  by_cases ht : t = rv (0 : VF (M := M))
  · have hDeg := degenerate_cell_contractions_compare C.uncountable.le C.saturated hsmall hc C hPC Z hZ f t hCell
      (Or.inl ht) z hz hzΓ j η hj hη0 T W hT hW
    exact ⟨C,Set.Subset.refl _,hDeg.extend (Set.Subset.refl _)⟩
  · by_cases hBal : ∃ r, IsBalanced (nativeVFPairDomain Z) f r t
    · obtain ⟨r,hBal⟩ := hBal
      obtain ⟨p,hp⟩ := CellRectangles.nonempty hCell
      have ha : p.1 ∈ first (nativeVFPairDomain Z) := ⟨p,hp,rfl⟩
      have hr : r ≠ rv (0 : VF (M := M)) := fun he => ht
        ((BalancedFibres.paradigms_degenerate_together hBal.2.2.1 p.1 ha).mp he)
      have hrS : r.val ∈ (C.base : Set M) := gamma_definable_names_context_singleton hc C0 P hP0 hgamma (hParΓ r hBal)
      have htS : t.val ∈ (C.base : Set M) := gamma_definable_names_context_singleton hc C0 P hP0 hgamma htΓ
      have hr0 : r.val ≠ iRVZero := by
        intro he
        apply hr
        apply Subtype.ext
        exact he.trans ((CanonicalRV.encodedRv_zero_iff (0 : VFType (M := M))).mpr rfl).symm
      have ht0 : t.val ≠ iRVZero := by
        intro he
        apply ht
        apply Subtype.ext
        exact he.trans ((CanonicalRV.encodedRv_zero_iff (0 : VFType (M := M))).mpr rfl).symm
      obtain ⟨K,hKV,hKH⟩ := balanced_translation_centres_over_common_names hNames Z hZ hBal.2.2.1 hfΓ
      have hf := hfΓ.common_names.mono hNames
      exact balanced_cell_opposite_order_contraction_comparison C hgamma γ hγ hγ1 hPC hNames hGeneric hc
        Z hZ f r t hBal hf hfΓ hr hrS htS hr0 ht0 K hKH hKV z hz hzΓ η hη hη0 j hj T W hT hW
    · exact nonbalanced_cell_contraction_comparison hc C hgamma γ hγ hγ1 hPC hNames hGeneric Z hZ f t hCell ht hBal
        z hz hzΓ j η hj hη hη0 T W hT hW

end IntegrationInACVF.Section7
