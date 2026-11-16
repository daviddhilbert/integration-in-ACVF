module

public import Integration7.FirstTwoStandardVolumeExchange
public import Integration7.VFStandardVolumeContractionObjects

@[expose] public section

/-! The explicit permutation formulation of Lemma7.7. Its native
statement allows any original Gamma base and retained density. The
volume-object statement uses the actual density graph and the existing
standard contraction objects, with the standing generated-base scope. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section5
open IntegrationInACVF.Section5 IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {n a : ℕ}

theorem lemma_7_7_native
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (hBC : B.real ⊆ (C.base : Set M)) (hNames : commonRealNames B ⊆ (C.base : Set M))
    (hgamma : Cardinal.mk B.gamma < C.κ) (hGenerated : VFGammaGeneratedBase B)
    (γ : Values.Gamma (M := M)) (hγ : γ ∈ B.gamma) (hγ1 : 1 < γ)
    (hGeneric : ∀ {p : ℕ} (y : Fin p → VF (M := M)),
      AlgebraicIndependent (vfParameterField B.real) y →
        AlgebraicIndependent (vfParameterField (C.base : Set M)) y)
    (A : DefSet (M := M) (C.base : Set M) (n+2) a)
    (hA : GammaSetDefinable B (carrier A))
    (hfin : ∀ y : Fin (n+2) → VF (M := M), {s : Fin a → RV (M := M) | (y,s) ∈ carrier A}.Finite)
    (δ : Fin a) (hδ : ∀ q : A, (q.val.2 δ).val ≠ iRVZero)
    {σ υ : Equiv.Perm (Fin (n+2))}
    (h0 : υ 0 = σ (0 : Fin (n+1)).succ) (h1 : υ (0 : Fin (n+1)).succ = σ 0)
    (hTail : ∀ j : Fin n, υ j.succ.succ = σ j.succ.succ)
    (T : StandardContraction A σ) (E : StandardContraction A υ)
    (hT : GammaProgramDefinable B T.program) (hE : GammaProgramDefinable B E.program) :
    let hsmall := (Cardinal.mk_le_mk_of_subset hBC).trans_lt C.small
    CommonContextVolumeEquivalent B C
      (retainedDensityContractionGammaObject C.uncountable.le C.saturated hsmall hc C hBC A hA hfin δ hδ T hT)
      (retainedDensityContractionGammaObject C.uncountable.le C.saturated hsmall hc C hBC A hA hfin δ hδ E hE) := by
  have hOrder : υ = (swapFirstTwo n).trans σ := by
    apply Equiv.ext
    intro j
    change υ j = σ (swapFirstTwo n j)
    cases j using Fin.cases with
    | zero => rw [swapFirstTwo_zero]; exact h0
    | succ j =>
      cases j using Fin.cases with
      | zero => rw [swapFirstTwo_one]; exact h1
      | succ j => rw [swapFirstTwo_tail]; exact hTail j
  subst υ
  exact first_two_standard_volume_exchange hc C hBC hNames hgamma hGenerated γ hγ hγ1 hGeneric
    A hA hfin δ hδ T E hT hE

theorem lemma_7_7
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (Ξ : Set (Values.Gamma (M := M))) (hΞ : Cardinal.mk Ξ < C.κ)
    (hGenerated : VFGammaGeneratedBase (⟨(C.base : Set M),Ξ⟩ : Base (M := M)))
    (hNames : commonRealNames (⟨(C.base : Set M),Ξ⟩ : Base (M := M)) ⊆ (C.base : Set M))
    (γ : Values.Gamma (M := M)) (hγ : γ ∈ Ξ) (hγ1 : 1 < γ)
    (U : PositiveVFVolumeObject (M := M) (C.base : Set M) (n+1))
    {σ υ : Equiv.Perm (Fin (n+2))}
    (h0 : υ 0 = σ (0 : Fin (n+1)).succ) (h1 : υ (0 : Fin (n+1)).succ = σ 0)
    (hTail : ∀ j : Fin n, υ j.succ.succ = σ j.succ.succ)
    (T : StandardContraction (nativeMixedVolumeDomain hc U.densityGraph.domain) σ)
    (E : StandardContraction (nativeMixedVolumeDomain hc U.densityGraph.domain) υ) :
    CommonContextVolumeEquivalent (⟨(C.base : Set M),Ξ⟩ : Base (M := M)) C
      ⟨U.standardContractionObject hc C Ξ T,U.standardContractionObject_gamma hc C Ξ T⟩
      ⟨U.standardContractionObject hc C Ξ E,U.standardContractionObject_gamma hc C Ξ E⟩ := by
  let G : Base (M := M) := ⟨(C.base : Set M),Ξ⟩
  let A := nativeMixedVolumeDomain hc U.densityGraph.domain
  have hA : GammaSetDefinable G (carrier A) := (gammaLogicInput G).real_set _ (setDefinable A)
  have hδ : ∀ q : A, (q.val.2 (Fin.last U.arity)).val ≠ iRVZero := by
    intro q
    apply (rv_nonzero_iff_raw _).mp
    intro h
    exact U.densityGraph.form.nonzero ⟨q.val,q.property⟩
      ((densityGraph_form_last U ⟨q.val,q.property⟩).trans h)
  exact lemma_7_7_native hc C (Set.Subset.refl _) hNames hΞ hGenerated γ hγ hγ1 (fun _ h => h)
    A hA U.densityGraph.finite_labels (Fin.last U.arity) hδ h0 h1 hTail T E
    (gamma_program_over_real_base G T.program) (gamma_program_over_real_base G E.program)

end IntegrationInACVF.Section7
