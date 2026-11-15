import Integration7.RectangleFamilyOppositeOrderComparisons

/-! The rectangle-family comparison covers every pair of actual
coordinate orders in VF dimension two. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section5
open IntegrationInACVF.Section5 IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7

theorem vf_two_order_cases (σ : Equiv.Perm (Fin 2)) : σ = Equiv.refl _ ∨ σ = Equiv.swap 0 1 := by
  have h0 : σ 0 = 0 ∨ σ 0 = 1 := by
    by_cases h : σ 0 = 0
    · exact Or.inl h
    · right
      apply Fin.ext
      have hn : (σ 0).val ≠ 0 := fun he => h (Fin.ext he)
      have hl := (σ 0).isLt
      omega
  rcases h0 with h0 | h0
  · left
    apply Equiv.ext
    intro i
    fin_cases i
    · exact h0
    · have h1 : σ 1 ≠ 0 := fun h => (by decide : (1 : Fin 2) ≠ 0) (σ.injective (h.trans h0.symm))
      apply Fin.ext
      have hn : (σ 1).val ≠ 0 := fun he => h1 (Fin.ext he)
      have hl := (σ 1).isLt
      change (σ 1).val = 1
      omega
  · right
    apply Equiv.ext
    intro i
    fin_cases i
    · exact h0
    · have h1 : σ 1 ≠ 1 := fun h => (by decide : (1 : Fin 2) ≠ 0) (σ.injective (h.trans h0.symm))
      apply Fin.ext
      have hn : (σ 1).val ≠ 1 := fun he => h1 (Fin.ext he)
      have hl := (σ 1).isLt
      change (σ 1).val = 0
      omega

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {G : Base (M := M)} {m : ℕ}

theorem rectangle_family_contractions_compare
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (hgamma : Cardinal.mk G.gamma < C.κ)
    (γ : Values.Gamma (M := M)) (hγ : γ ∈ G.gamma) (hγ1 : 1 < γ)
    (hGC : G.real ⊆ (C.base : Set M)) (hNames : commonRealNames G ⊆ (C.base : Set M))
    (hGeneric : ∀ {p : ℕ} (x : Fin p → VF (M := M)), AlgebraicIndependent (vfParameterField G.real) x →
      AlgebraicIndependent (vfParameterField (C.base : Set M)) x)
    (H : DefSet (M := M) (C.base : Set M) 2 m) (hH : GammaSetDefinable G (carrier H))
    (hfin : ∀ x : Fin 2 → VF (M := M), {r : Fin m → RV (M := M) | (x,r) ∈ carrier H}.Finite)
    (hRect : RectangularRVFibres (carrier H))
    (δ : Fin m) (hδ : ∀ p : H, (p.val.2 δ).val ≠ iRVZero)
    {σ τ : Equiv.Perm (Fin 2)} (T : StandardContraction H σ) (W : StandardContraction H τ)
    (hT : GammaProgramDefinable G T.program) (hW : GammaProgramDefinable G W.program) :
    let hsmall : Cardinal.mk G.real < C.κ := (Cardinal.mk_le_mk_of_subset hGC).trans_lt C.small
    let U := retainedDensityContractionGammaObject C.uncountable.le C.saturated hsmall hc C hGC H hH hfin δ hδ T hT
    let V := retainedDensityContractionGammaObject C.uncountable.le C.saturated hsmall hc C hGC H hH hfin δ hδ W hW
    ∃ K : BaseContext M, ∃ hCK : (C.base : Set M) ⊆ (K.base : Set M),
      GammaVolumeBlowupEquivalent G (K.base : Set M) 1 (U.extend hCK) (V.extend hCK) := by
  intro hsmall U V
  rcases vf_two_order_cases σ with rfl | rfl
  · rcases vf_two_order_cases τ with rfl | rfl
    · exact retained_density_same_order_contractions_compare hc C C.uncountable.le C.saturated hsmall
        hgamma γ hγ hγ1 hGC hGeneric H hH hfin δ hδ T W hT hW
    · exact rectangle_family_opposite_order_contractions_compare hc C hgamma γ hγ hγ1 hGC hNames hGeneric
        H hH hfin hRect δ hδ T W hT hW
  · rcases vf_two_order_cases τ with rfl | rfl
    · obtain ⟨K,hCK,h⟩ := rectangle_family_opposite_order_contractions_compare hc C hgamma γ hγ hγ1
        hGC hNames hGeneric H hH hfin hRect δ hδ W T hW hT
      exact ⟨K,hCK,h.symm hc K G⟩
    · exact retained_density_same_order_contractions_compare hc C C.uncountable.le C.saturated hsmall
        hgamma γ hγ hγ1 hGC hGeneric H hH hfin δ hδ T W hT hW

end IntegrationInACVF.Section7
