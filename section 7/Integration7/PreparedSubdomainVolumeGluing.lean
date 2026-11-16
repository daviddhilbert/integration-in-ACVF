module

public import Integration7.PreparedSubdomainVolumeChains
public import Integration7.PreparedVolumePartitionGluing
public import Integration7.SmallPullbackVolumeObjects

@[expose] public section

/-! Glue the prepared factors on a cofull subdomain. The two discarded
complements need no bijection: both have empty essential volume objects. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 (vfDim rawRVSpace vfDim_eq_of_bijective)
open SpecialTransformations.Section9 SpecialTransformations.Section5
open IntegrationInACVF.Section5 IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n a b : ℕ}

theorem prepared_subdomain_volume_gluing
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (Ξ : Set (Values.Gamma (M := M))) (hΞ : Cardinal.mk Ξ < C.κ)
    (hGenerated : VFGammaGeneratedBase (⟨(C.base : Set M),Ξ⟩ : Base (M := M)))
    (hNames : commonRealNames (⟨(C.base : Set M),Ξ⟩ : Base (M := M)) ⊆ (C.base : Set M))
    (γ : Values.Gamma (M := M)) (hγ : γ ∈ Ξ) (hγ1 : 1 < γ)
    {A L : DefSet (M := M) (C.base : Set M) (n+1) a}
    {B K : DefSet (M := M) (C.base : Set M) (n+1) b}
    (hLA : carrier L ⊆ carrier A) (hKB : carrier K ⊆ carrier B)
    (ω : VolumeForm (rawSpecialSet hc A)) (π : VolumeForm (rawSpecialSet hc B))
    (δ : Fin a) (ε : Fin b) (hω : ∀ p, ω.value p = p.val.2 δ) (hπ : ∀ p, π.value p = p.val.2 ε)
    (hδ : ∀ p : A, (p.val.2 δ).val ≠ iRVZero) (hε : ∀ p : B, (p.val.2 ε).val ≠ iRVZero)
    (hfinA : ∀ x : Fin (n+1) → VF (M := M), {r : Fin a → RV (M := M) | (x,r) ∈ carrier A}.Finite)
    (hfinB : ∀ x : Fin (n+1) → VF (M := M), {r : Fin b → RV (M := M) | (x,r) ∈ carrier B}.Finite)
    (hsmallL : vfDim (SpecialTransformations.Section4.rawRVSpace (M := M) 1) (rawSpecialSet hc (nativeMixedDifference A L)) < n+1)
    (hsmallK : vfDim (SpecialTransformations.Section4.rawRVSpace (M := M) 1) (rawSpecialSet hc (nativeMixedDifference B K)) < n+1)
    (Q : NativeVolumeUnaryPartition hc C L K (ω.restrict hLA) (π.restrict hKB)) :
    letI := Q.finite
    ∀ (P : NativePreparedMixedPartition A (nativeCompletedPartition A L Q.source))
      (R : NativePreparedMixedPartition B (nativeCompletedPartition B K Q.target)),
    CommonContextVolumeEquivalent (⟨(C.base : Set M),Ξ⟩ : Base (M := M)) C
      (specialPullbackVolumeGammaObject hc C Ξ P.special P.pullback hfinA δ hδ)
      (specialPullbackVolumeGammaObject hc C Ξ R.special R.pullback hfinB ε hε) := by
  classical
  letI := Q.finite
  intro P R
  let ψ := specialRetainedVolumeForm hc P.special δ hδ
  let χ := specialRetainedVolumeForm hc R.special ε hε
  let δP := suffixIndex (special_chain_rvArity_le P.special.chain) δ
  let εR := suffixIndex (special_chain_rvArity_le R.special.chain) ε
  have hδP := special_retained_density_nonzero P.special δ hδ
  have hεR := special_retained_density_nonzero R.special ε hε
  have hfinP := special_target_finite_labels C Ξ P.special hfinA
  have hfinR := special_target_finite_labels C Ξ R.special hfinB
  have hPF := special_pullback_volume_finite C Ξ P.special P.pullback hfinA
  have hRF := special_pullback_volume_finite C Ξ R.special R.pullback hfinB
  have hPieces : ∀ i, CommonContextVolumeEquivalent (⟨(C.base : Set M),Ξ⟩ : Base (M := M)) C
      (finitePullbackVolumePiece hc C Ξ P.target hPF P.pieces P.subset δP hδP i)
      (finitePullbackVolumePiece hc C Ξ R.target hRF R.pieces R.subset εR hεR i) := by
    intro i
    cases i with
    | none =>
      apply CommonContextVolumeEquivalent.of_empty_essential hc C
      · apply pullback_volume_essential_empty_of_small_dimension hc C (P.pieces none) (P.piecePullback none)
          (pullback_finite_of_subset (P.subset none) hPF) δP (fun p => hδP ⟨p.val,P.subset none p.property⟩)
        have he := vfDim_eq_of_bijective (SpecialTransformations.Section4.rawRVSpace (M := M) 1)
          (rawSpecialMap hc (P.pieceSpecial none).toMap) (P.pieceSpecial none).bijective
        exact he ▸ hsmallL
      · apply pullback_volume_essential_empty_of_small_dimension hc C (R.pieces none) (R.piecePullback none)
          (pullback_finite_of_subset (R.subset none) hRF) εR (fun p => hεR ⟨p.val,R.subset none p.property⟩)
        have he := vfDim_eq_of_bijective (SpecialTransformations.Section4.rawRVSpace (M := M) 1)
          (rawSpecialMap hc (R.pieceSpecial none).toMap) (R.pieceSpecial none).bijective
        exact he ▸ hsmallK
    | some i =>
      obtain ⟨T,hT⟩ := prepared_subdomain_volume_chain_exists hc C hLA hKB ω π δ ε hω hπ hδ hε hfinA Q P R i
      exact pullback_unary_chain_volume_comparison hc C Ξ hΞ hGenerated hNames γ hγ hγ1
        (P.pieces (some i)) (R.pieces (some i)) (P.piecePullback (some i)) (R.piecePullback (some i))
        (fun x => (hfinP x).subset (fun _ h => P.subset (some i) h))
        (fun x => (hfinR x).subset (fun _ h => R.subset (some i) h))
        (pullback_finite_of_subset (P.subset (some i)) hPF) (pullback_finite_of_subset (R.subset (some i)) hRF)
        (ψ.restrict (P.subset (some i))) (χ.restrict (R.subset (some i)))
        δP εR (fun _ => rfl) (fun _ => rfl) T hT
  exact finite_pullback_volume_partition_gluing hc C Ξ P.target R.target hPF hRF
    P.pieces R.pieces P.subset R.subset P.disjoint R.disjoint P.piecePullback R.piecePullback
    δP εR hδP hεR hPieces Finset.univ P.cover R.cover

end IntegrationInACVF.Section7
