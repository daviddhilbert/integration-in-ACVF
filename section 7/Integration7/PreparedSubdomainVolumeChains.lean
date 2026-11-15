import Integration7.NativeVolumeUnaryPartitions
import Integration7.NativeCompletedPartitions
import Integration7.NativePreparedMixedPartitions
import Integration7.SpecialConjugateVolumeChains

/-! The genuine factor chains on a subdomain survive preparation of
the ambient partition including its discarded complement. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section9 SpecialTransformations.Section5
open IntegrationInACVF.Section5

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n a b : ℕ}

theorem prepared_subdomain_volume_chain_exists
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    {A L : DefSet (M := M) (C.base : Set M) (n+1) a}
    {B K : DefSet (M := M) (C.base : Set M) (n+1) b}
    (hLA : carrier L ⊆ carrier A) (hKB : carrier K ⊆ carrier B)
    (ω : VolumeForm (rawSpecialSet hc A)) (π : VolumeForm (rawSpecialSet hc B))
    (δ : Fin a) (ε : Fin b) (hω : ∀ p, ω.value p = p.val.2 δ) (hπ : ∀ p, π.value p = p.val.2 ε)
    (hδ : ∀ p : A, (p.val.2 δ).val ≠ iRVZero) (hε : ∀ p : B, (p.val.2 ε).val ≠ iRVZero)
    (hfinA : ∀ x : Fin (n+1) → VF (M := M), {r : Fin a → RV (M := M) | (x,r) ∈ carrier A}.Finite)
    (Q : NativeVolumeUnaryPartition hc C L K (ω.restrict hLA) (π.restrict hKB)) :
    letI := Q.finite
    ∀ (P : NativePreparedMixedPartition A (nativeCompletedPartition A L Q.source))
      (R : NativePreparedMixedPartition B (nativeCompletedPartition B K Q.target)) (i : Q.index),
    let ψ := specialRetainedVolumeForm hc P.special δ hδ
    let χ := specialRetainedVolumeForm hc R.special ε hε
    ∃ T : UnaryChain (C.base : Set M) (n+1) (P.pieces (some i)) (R.pieces (some i)),
      unaryChainVolumeData hc T (ψ.restrict (P.subset (some i))) (χ.restrict (R.subset (some i))) := by
  letI := Q.finite
  intro P R i ψ χ
  let ωD : VolumeForm (rawSpecialSet hc (Q.source i)) := ω.restrict ((Q.sourceSubset i).trans hLA)
  let πE : VolumeForm (rawSpecialSet hc (Q.target i)) := π.restrict ((Q.targetSubset i).trans hKB)
  let ψP : VolumeForm (rawSpecialSet hc (P.pieces (some i))) := ψ.restrict (P.subset (some i))
  let χR : VolumeForm (rawSpecialSet hc (R.pieces (some i))) := χ.restrict (R.subset (some i))
  apply special_conjugate_volume_chain_exists hc C (P.pieceSpecial (some i)) (R.pieceSpecial (some i))
    ωD πE ψP χR ?_ ?_ (fun x => (hfinA x).subset (fun _ h => hLA (Q.sourceSubset i h)))
    (Q.chain i) (Q.volume i)
  · intro p
    change ω.value ⟨p.val,hLA (Q.sourceSubset i p.property)⟩ =
      ((rawSpecialMap hc (P.pieceSpecial (some i)).toMap) p).val.2
        (suffixIndex (special_chain_rvArity_le P.special.chain) δ)
    rw [hω]
    exact (special_oldLabels (P.pieceSpecial (some i)) ⟨p.val,p.property⟩ δ).symm
  · intro p
    change π.value ⟨p.val,hKB (Q.targetSubset i p.property)⟩ =
      ((rawSpecialMap hc (R.pieceSpecial (some i)).toMap) p).val.2
        (suffixIndex (special_chain_rvArity_le R.special.chain) ε)
    rw [hπ]
    exact (special_oldLabels (R.pieceSpecial (some i)) ⟨p.val,p.property⟩ ε).symm

end IntegrationInACVF.Section7
