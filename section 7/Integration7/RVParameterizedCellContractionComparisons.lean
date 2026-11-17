module

public import Integration7.GammaRVDefinableNameContexts
public import Integration7.NonbalancedCellContractionComparisons
public import Integration7.BalancedCellOppositeOrderComparisons
public import Integration7.NativeBalancedTranslationCommonNames
public import Integration7.DegenerateCellContractionComparisons

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

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
variable {P : Base (M := M)} {e d : ℕ}

set_option maxHeartbeats 1600000 in
theorem rv_parameterized_cell_contraction_comparison
    (hc : CanonicalStructure.IsCanonical (M := M)) (C0 : BaseContext M)
    (hP0 : P.real ⊆ (C0.base : Set M)) (hBase : P.real = (C0.base : Set M))
    (hgamma : Cardinal.mk P.gamma < C0.κ)
    (γ : Values.Gamma (M := M)) (hγ : γ ∈ P.gamma) (hγ1 : 1 < γ)
    (u : Fin e → RV (M := M)) :
    let C := gammaRVDefinableNamesVolumeContext hc C0 P hP0 hgamma u
    let B := RVLabelSlices.labelBase P u
    let hBC : B.real ⊆ (C.base : Set M) := fun _ hx =>
      gamma_rv_definable_names_context_contains hc C0 P hP0 hgamma u
        (hx.elim (fun h => Or.inl (Or.inl (hP0 h))) Or.inr)
    ∀ (Z : DefSet (M := M) (C.base : Set M) 2 0) (hZ : GammaSetDefinable B (carrier Z))
    (hDef : Cells.DefinableTwoCell B (nativeVFPairDomain Z))
    (z : Fin d → RV (M := M)) (hz : ∀ j, (z j).val ∈ (C.base : Set M))
    (hzΓ : DefinableOverBase B (fun _ : Fin d => .rv) {fun j => (z j).val})
    (j : Fin d) (η : RV (M := M)) (hj : z j = η) (hη0 : η ≠ 0)
    (T : StandardContraction (fixedRVLabelDomain Z z hz) (Equiv.refl _))
    (W : StandardContraction (fixedRVLabelDomain Z z hz) (Equiv.swap 0 1))
    (hT : GammaProgramDefinable B T.program) (hW : GammaProgramDefinable B W.program),
    let hsmall : Cardinal.mk B.real < C.κ := (Cardinal.mk_le_mk_of_subset hBC).trans_lt C.small
    let U := fixedLabelContractionGammaObject C.uncountable.le C.saturated hsmall hc C hBC Z hZ z hz hzΓ j η hj hη0 T hT
    let V := fixedLabelContractionGammaObject C.uncountable.le C.saturated hsmall hc C hBC Z hZ z hz hzΓ j η hj hη0 W hW
    ∃ (K : BaseContext M) (hCK : (C.base : Set M) ⊆ (K.base : Set M)),
      GammaVolumeBlowupEquivalent B (K.base : Set M) 1 (U.extend hCK) (V.extend hCK) := by
  intro C B hBC Z hZ hDef z hz hzΓ j η hj hη0 T W hT hW hsmall U V
  classical
  obtain ⟨f,t,hCell,hPairΓ,hfΓ,htΓ,hParΓ⟩ := hDef
  have hNames : commonRealNames B ⊆ (C.base : Set M) := by
    rintro y ((hy | hy) | hy)
    · exact gamma_rv_definable_names_context_contains hc C0 P hP0 hgamma u (Or.inl (Or.inl (hP0 hy)))
    · exact gamma_rv_definable_names_context_contains hc C0 P hP0 hgamma u (Or.inr hy)
    · exact gamma_rv_definable_names_context_contains hc C0 P hP0 hgamma u (Or.inl (Or.inr (Or.inr hy)))
  have hGeneric : ∀ {p : ℕ} (x : Fin p → VF (M := M)), AlgebraicIndependent (vfParameterField B.real) x →
      AlgebraicIndependent (vfParameterField (C.base : Set M)) x := by
    intro p x hx
    have huRV : ∀ y ∈ Set.range (fun i => (u i).val), iRV y := by
      rintro y ⟨i,rfl⟩
      exact (u i).property
    change AlgebraicIndependent (vfParameterField (P.real ∪ Set.range (fun i => (u i).val))) x at hx
    rw [vfParameterField_union_rv _ _ huRV] at hx
    exact gamma_rv_definable_names_context_preserves_independence hc C0 P hP0 hgamma u hBase x hx
  have hgammaB : Cardinal.mk B.gamma < C.κ := hgamma
  have hη : η.val ∈ (C.base : Set M) := (congrArg (fun a : RV (M := M) => a.val ∈ (C.base : Set M)) hj).mp (hz j)
  by_cases ht : t = rv (0 : VF (M := M))
  · have hDeg := degenerate_cell_contractions_compare C.uncountable.le C.saturated hsmall hc C hBC Z hZ f t hCell
      (Or.inl ht) z hz hzΓ j η hj hη0 T W hT hW
    exact ⟨C,Set.Subset.refl _,hDeg.extend (Set.Subset.refl _)⟩
  · by_cases hBal : ∃ r, IsBalanced (nativeVFPairDomain Z) f r t
    · obtain ⟨r,hBal⟩ := hBal
      obtain ⟨p,hp⟩ := CellRectangles.nonempty hCell
      have ha : p.1 ∈ first (nativeVFPairDomain Z) := ⟨p,hp,rfl⟩
      have hr : r ≠ rv (0 : VF (M := M)) := fun he => ht
        ((BalancedFibres.paradigms_degenerate_together hBal.2.2.1 p.1 ha).mp he)
      have hrS : r.val ∈ (C.base : Set M) := gamma_rv_definable_names_context_singleton hc C0 P hP0 hgamma u (hParΓ r hBal)
      have htS : t.val ∈ (C.base : Set M) := gamma_rv_definable_names_context_singleton hc C0 P hP0 hgamma u htΓ
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
      exact balanced_cell_opposite_order_contraction_comparison C hgammaB γ hγ hγ1 hBC hNames hGeneric hc
        Z hZ f r t hBal hf hfΓ hr hrS htS hr0 ht0 K hKH hKV z hz hzΓ η hη hη0 j hj T W hT hW
    · exact nonbalanced_cell_contraction_comparison hc C hgammaB γ hγ hγ1 hBC hNames hGeneric Z hZ f t hCell ht hBal
        z hz hzΓ j η hj hη hη0 T W hT hW


end IntegrationInACVF.Section7
