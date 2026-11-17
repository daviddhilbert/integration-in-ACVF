module

public import Integration7.RectangleFamilyOrderProducers
public import Integration7.RetainedDensityRelativeContractions
public import Integration7.CanonicalPullbackVolumeClasses
public import Integration7.CommonContextVolumeEquivalences

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! A specified contraction of a rectangle family compares to the
actual key volume object of a rectangular pullback through a relatively
unary Jacobian-one preparation. All witness contexts are joined. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section9 SpecialTransformations.Section5
open IntegrationInACVF.Section5 IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7
variable {M : Type} [sM : LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {G : Base (M := M)} {a b : ℕ}

set_option maxHeartbeats 3000000 in
theorem rectangle_contraction_to_pullback_volume
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (hgamma : Cardinal.mk G.gamma < C.κ)
    (γ : Values.Gamma (M := M)) (hγ : γ ∈ G.gamma) (hγ1 : 1 < γ)
    (hGC : G.real ⊆ (C.base : Set M)) (hNames : commonRealNames G ⊆ (C.base : Set M))
    (hGeneric : ∀ {p : ℕ} (x : Fin p → VF (M := M)), AlgebraicIndependent (vfParameterField G.real) x →
      AlgebraicIndependent (vfParameterField (C.base : Set M)) x)
    (H : DefSet (M := M) (C.base : Set M) 2 a) (A : DefSet (M := M) (C.base : Set M) 2 b)
    (hH : GammaSetDefinable G (carrier H)) (hA : GammaSetDefinable G (carrier A))
    (hfinH : ∀ x : Fin 2 → VF (M := M), {r : Fin a → RV (M := M) | (x,r) ∈ carrier H}.Finite)
    (hfinA : ∀ x : Fin 2 → VF (M := M), {r : Fin b → RV (M := M) | (x,r) ∈ carrier A}.Finite)
    (hRectH : RectangularRVFibres (carrier H)) (hRectA : RectangularRVFibres (carrier A))
    (hPull : IsRVPullback (carrier A))
    (hAF : @SpecialTransformations.DefinableGeometry.Map.FiniteFibres LRV M
      (@CanonicalStructure.normalize M sM) _ _ (C.base : Set M) _ _ (rvObjectVolume (pullbackObject A)))
    (δ : Fin a) (ε : Fin b)
    (hδ : ∀ p : H, (p.val.2 δ).val ≠ iRVZero) (hε : ∀ p : A, (p.val.2 ε).val ≠ iRVZero)
    (f : Map H A) (hf : Function.Bijective f) (hfΓ : GammaGraphDefinable G (pointMapGraph f))
    (hLabels : ∀ p : H, (f p).val.2 ε = p.val.2 δ)
    (hJ : VFAlmostEverywhere (rawSpecialSet hc H)
      (fun p => HasMixedVFJacobianAt (rawSpecialMap hc f) p 1))
    (α : Equiv.Perm (Fin 2)) (hi : UnaryRelative f (α 0))
    {σ : Equiv.Perm (Fin 2)} (T : StandardContraction H σ) (hT : GammaProgramDefinable G T.program) :
    let hsmall := (Cardinal.mk_le_mk_of_subset hGC).trans_lt C.small
    CommonContextVolumeEquivalent G C
      (retainedDensityContractionGammaObject C.uncountable.le C.saturated hsmall hc C hGC H hH hfinH δ hδ T hT)
      (pullbackCoordinateGammaObject hc C hGC A hA hAF ε hε) := by
  intro hsmall
  obtain ⟨R,hR⟩ := rectangle_family_contraction_in_order_exists C hNames γ hγ hγ1 H hH hRectH α
  obtain ⟨E,hE⟩ := rectangle_family_contraction_in_order_exists C hNames γ hγ hγ1 A hA hRectA α
  obtain ⟨K,hK,D,hCD,hCanonical⟩ := pullback_canonical_contraction_volume_exists C.uncountable.le
    C.saturated hsmall hc C hGC A hA hPull hfinA hAF ε hε
  have hFirst := rectangle_family_contractions_compare hc C hgamma γ hγ hγ1 hGC hNames hGeneric
    H hH hfinH hRectH δ hδ T R hT hR
  have hMap := retained_density_relative_contractions_compare hc C C.uncountable.le C.saturated hsmall
    hgamma γ hγ hγ1 hGC hGeneric H A hH hA hfinH hfinA δ ε hδ hε f hf hfΓ hLabels hJ hi R E hR hE
  have hLast := rectangle_family_contractions_compare hc C hgamma γ hγ hγ1 hGC hNames hGeneric
    A hA hfinA hRectA ε hε E K hE hK
  have hBack := CommonContextVolumeEquivalent.symm hc ⟨D,hCD,hCanonical⟩
  exact CommonContextVolumeEquivalent.trans hc hFirst
    (CommonContextVolumeEquivalent.trans hc hMap (CommonContextVolumeEquivalent.trans hc hLast hBack))

end IntegrationInACVF.Section7
