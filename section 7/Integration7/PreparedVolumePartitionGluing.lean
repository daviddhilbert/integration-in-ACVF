import Integration7.PreparedPieceVolumeChains
import Integration7.PullbackUnaryChainVolumeComparison
import Integration7.FinitePullbackVolumeGluing

/-! Glue the actual Section 5.6 factor chains after simultaneous special
preparation of both finite partitions, retaining the original densities. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section9 SpecialTransformations.Section5
open IntegrationInACVF.Section5 IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n a b : ℕ}

theorem prepared_volume_partition_gluing
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (Ξ : Set (Values.Gamma (M := M))) (hΞ : Cardinal.mk Ξ < C.κ)
    (hGenerated : VFGammaGeneratedBase (⟨(C.base : Set M),Ξ⟩ : Base (M := M)))
    (hNames : commonRealNames (⟨(C.base : Set M),Ξ⟩ : Base (M := M)) ⊆ (C.base : Set M))
    (γ : Values.Gamma (M := M)) (hγ : γ ∈ Ξ) (hγ1 : 1 < γ)
    {A : DefSet (M := M) (C.base : Set M) (n+1) a} {B : DefSet (M := M) (C.base : Set M) (n+1) b}
    (ω : VolumeForm (rawSpecialSet hc A)) (π : VolumeForm (rawSpecialSet hc B))
    (δ : Fin a) (ε : Fin b) (hω : ∀ p, ω.value p = p.val.2 δ) (hπ : ∀ p, π.value p = p.val.2 ε)
    (hδ : ∀ p : A, (p.val.2 δ).val ≠ iRVZero) (hε : ∀ p : B, (p.val.2 ε).val ≠ iRVZero)
    (hfinA : ∀ x : Fin (n+1) → VF (M := M), {r : Fin a → RV (M := M) | (x,r) ∈ carrier A}.Finite)
    (hfinB : ∀ x : Fin (n+1) → VF (M := M), {r : Fin b → RV (M := M) | (x,r) ∈ carrier B}.Finite)
    (Q : NativeVolumeUnaryPartition hc C A B ω π) :
    letI := Q.finite
    ∀ (P : NativePreparedMixedPartition A Q.source) (R : NativePreparedMixedPartition B Q.target),
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
    obtain ⟨T,hT⟩ := prepared_piece_volume_chain_exists hc C ω π δ ε hω hπ hδ hε hfinA Q P R i
    exact pullback_unary_chain_volume_comparison hc C Ξ hΞ hGenerated hNames γ hγ hγ1
      (P.pieces i) (R.pieces i) (P.piecePullback i) (R.piecePullback i)
      (fun x => (hfinP x).subset (fun _ h => P.subset i h))
      (fun x => (hfinR x).subset (fun _ h => R.subset i h))
      (pullback_finite_of_subset (P.subset i) hPF) (pullback_finite_of_subset (R.subset i) hRF)
      (ψ.restrict (P.subset i)) (χ.restrict (R.subset i)) δP εR (fun _ => rfl) (fun _ => rfl) T hT
  exact finite_pullback_volume_partition_gluing hc C Ξ P.target R.target hPF hRF
    P.pieces R.pieces P.subset R.subset P.disjoint R.disjoint P.piecePullback R.piecePullback
    δP εR hδP hεR hPieces Finset.univ P.cover R.cover

end IntegrationInACVF.Section7
