module

public import Integration7.RectangleFamilyConstructedVolumeComparison
public import Integration7.RetainedDensitySameOrderContractions
public import Integration7.VolumeContextJoins

@[expose] public section

/-! The whole shared-label rectangle case of Lemma7.7, for arbitrary
specified opposite-order contractions and nonconstant retained density. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section5
open IntegrationInACVF.Section5 IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {G : Base (M := M)} {m : ℕ}

set_option maxHeartbeats 2000000 in
theorem rectangle_family_opposite_order_contractions_compare
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
    (T : StandardContraction H (Equiv.refl _)) (W : StandardContraction H (Equiv.swap 0 1))
    (hT : GammaProgramDefinable G T.program) (hW : GammaProgramDefinable G W.program) :
    let hsmall : Cardinal.mk G.real < C.κ := (Cardinal.mk_le_mk_of_subset hGC).trans_lt C.small
    let U := retainedDensityContractionGammaObject C.uncountable.le C.saturated hsmall hc C hGC H hH hfin δ hδ T hT
    let V := retainedDensityContractionGammaObject C.uncountable.le C.saturated hsmall hc C hGC H hH hfin δ hδ W hW
    ∃ K : BaseContext M, ∃ hCK : (C.base : Set M) ⊆ (K.base : Set M),
      GammaVolumeBlowupEquivalent G (K.base : Set M) 1 (U.extend hCK) (V.extend hCK) := by
  intro hsmall U V
  obtain ⟨F⟩ := independent_rectangle_family_preparations_exists C hNames γ hγ hγ1 H hH hRect
  obtain ⟨KH,hCKH,hHead⟩ := retained_density_same_order_contractions_compare hc C C.uncountable.le
    C.saturated hsmall hgamma γ hγ hγ1 hGC hGeneric H hH hfin δ hδ T F.headContraction hT (F.head_contraction_gamma hH)
  obtain ⟨KL,hCKL,hTail⟩ := retained_density_same_order_contractions_compare hc C C.uncountable.le
    C.saturated hsmall hgamma γ hγ hγ1 hGC hGeneric H hH hfin δ hδ W F.tailContraction hW (F.tail_contraction_gamma hH)
  obtain ⟨KM,hCKM,hMiddle⟩ := F.constructed_volume_comparison C.uncountable.le C.saturated hsmall
    hc C hGC hH hfin δ hδ
  obtain ⟨K₀,hHK₀,hLK₀⟩ := volume_context_join_exists KH KL
  obtain ⟨K,hK₀K,hMK⟩ := volume_context_join_exists K₀ KM
  let hHK := hHK₀.trans hK₀K
  let hLK := hLK₀.trans hK₀K
  let hCK := hCKH.trans hHK
  exact ⟨K,hCK,(hHead.extend hHK).trans hc K G
    ((hMiddle.extend hMK).trans hc K G ((hTail.extend hLK).symm hc K G))⟩

end IntegrationInACVF.Section7
