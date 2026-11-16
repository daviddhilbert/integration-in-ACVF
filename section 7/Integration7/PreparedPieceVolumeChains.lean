module

public import Integration7.NativeVolumeUnaryPartitions
public import Integration7.NativePreparedPartitionExistence
public import Integration7.SpecialPullbackVolumeObjects

@[expose] public section

/-! Conjugate each actual Section 5.6 volume factor chain by the
genuine special preparations of its source and target pieces. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section9 SpecialTransformations.Section5
open IntegrationInACVF.Section5 IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n a b : ℕ}

theorem prepared_piece_volume_chain_exists
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    {A : DefSet (M := M) (C.base : Set M) (n+1) a} {B : DefSet (M := M) (C.base : Set M) (n+1) b}
    (ω : VolumeForm (rawSpecialSet hc A)) (π : VolumeForm (rawSpecialSet hc B))
    (δ : Fin a) (ε : Fin b) (hω : ∀ p, ω.value p = p.val.2 δ) (hπ : ∀ p, π.value p = p.val.2 ε)
    (hδ : ∀ p : A, (p.val.2 δ).val ≠ iRVZero) (hε : ∀ p : B, (p.val.2 ε).val ≠ iRVZero)
    (hfinA : ∀ x : Fin (n+1) → VF (M := M), {r : Fin a → RV (M := M) | (x,r) ∈ carrier A}.Finite)
    (Q : NativeVolumeUnaryPartition hc C A B ω π) :
    letI := Q.finite
    ∀ (P : NativePreparedMixedPartition A Q.source) (R : NativePreparedMixedPartition B Q.target) (i : Q.index),
    let ψ := specialRetainedVolumeForm hc P.special δ hδ
    let χ := specialRetainedVolumeForm hc R.special ε hε
    ∃ T : UnaryChain (C.base : Set M) (n+1) (P.pieces i) (R.pieces i),
      unaryChainVolumeData hc T (ψ.restrict (P.subset i)) (χ.restrict (R.subset i)) := by
  letI := Q.finite
  intro P R i ψ χ
  let ωD : VolumeForm (rawSpecialSet hc (Q.source i)) := ω.restrict (Q.sourceSubset i)
  let πE : VolumeForm (rawSpecialSet hc (Q.target i)) := π.restrict (Q.targetSubset i)
  let ψP : VolumeForm (rawSpecialSet hc (P.pieces i)) := ψ.restrict (P.subset i)
  let χR : VolumeForm (rawSpecialSet hc (R.pieces i)) := χ.restrict (R.subset i)
  let tP := specialUnaryChain (Nat.zero_lt_succ n) (P.pieceSpecial i).chain
  let tR := specialUnaryChain (Nat.zero_lt_succ n) (R.pieceSpecial i).chain
  have hDensityP : ∀ p, ωD.value p = ψP.value ((rawSpecialMap hc (P.pieceSpecial i).toMap) p) := by
    intro p
    change ω.value ⟨p.val,Q.sourceSubset i p.property⟩ =
      ((rawSpecialMap hc (P.pieceSpecial i).toMap) p).val.2
        (suffixIndex (special_chain_rvArity_le P.special.chain) δ)
    rw [hω]
    exact (special_oldLabels (P.pieceSpecial i) ⟨p.val,p.property⟩ δ).symm
  have hDensityR : ∀ p, πE.value p = χR.value ((rawSpecialMap hc (R.pieceSpecial i).toMap) p) := by
    intro p
    change π.value ⟨p.val,Q.targetSubset i p.property⟩ =
      ((rawSpecialMap hc (R.pieceSpecial i).toMap) p).val.2
        (suffixIndex (special_chain_rvArity_le R.special.chain) ε)
    rw [hπ]
    exact (special_oldLabels (R.pieceSpecial i) ⟨p.val,p.property⟩ ε).symm
  have hP : unaryChainVolumeData hc tP ωD ψP := special_unary_chain_volume_data hc C (P.pieceSpecial i) ωD ψP hDensityP
  have hR : unaryChainVolumeData hc tR πE χR := special_unary_chain_volume_data hc C (R.pieceSpecial i) πE χR hDensityR
  have hfinD : ∀ x : Fin (n+1) → VF (M := M),
      {r : Fin a → RV (M := M) | (x,r) ∈ carrier (Q.source i)}.Finite :=
    fun x => (hfinA x).subset (fun _ h => Q.sourceSubset i h)
  have hfinP := special_target_finite_labels C ∅ (P.pieceSpecial i) hfinD
  have hInv := unary_chain_volume_data_inverse hc C tP ωD ψP hP hfinD
  have hTail := unary_chain_volume_data_append hc C (Q.chain i) tR ωD πE χR (Q.volume i) hR hfinD
  refine ⟨tP.inverse.append ((Q.chain i).append tR),?_⟩
  exact unary_chain_volume_data_append hc C tP.inverse ((Q.chain i).append tR) ψP ωD χR hInv hTail hfinP

end IntegrationInACVF.Section7
