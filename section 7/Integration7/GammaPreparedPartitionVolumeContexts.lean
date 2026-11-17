module

public import Integration7.GammaFiniteMembershipVolumeContexts
public import Integration7.GammaNativePreparedMixedPartitions

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! Simultaneous pullback preparation of a finite definable partition
in a genuine small containing context, with original-Gamma certificates
on the full map and each piece. No generation hypothesis is imposed on
the term context containing the presented sets. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section5
open IntegrationInACVF.Section5 IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {n a : ℕ} {ι : Type} [Fintype ι]

theorem gamma_prepared_partition_in_volume_context
    (C : BaseContext M) (P : Base (M := M)) (hPC : P.real ⊆ (C.base : Set M))
    (A : DefSet (M := M) (C.base : Set M) n a) (hAP : IsRVPullback (carrier A))
    (hA : GammaSetDefinable P (carrier A))
    (D : ι → DefSet (M := M) (C.base : Set M) n a)
    (hDA : ∀ i, carrier (D i) ⊆ carrier A)
    (hDisj : ∀ i j, i ≠ j → Disjoint (carrier (D i)) (carrier (D j)))
    (hCover : carrier A = nativeMixedFiniteUnionSet D Finset.univ)
    (hD : ∀ i, GammaSetDefinable P (carrier (D i))) :
    ∃ E : BaseContext M, ∃ hCE : (C.base : Set M) ⊆ (E.base : Set M),
    ∃ Q : NativePreparedMixedPartition (extendBase A hCE) (fun i => extendBase (D i) hCE),
      GammaChainDefinable P Q.special.chain ∧ ∀ i, GammaChainDefinable P (Q.pieceSpecial i).chain := by
  obtain ⟨E,hCE,r,W,T,hT,hWP,hFlags⟩ := gamma_finite_membership_preparation_in_volume_context
    C P hPC A hAP hA D Finset.univ (fun i _ => hD i)
  obtain ⟨Q,hQ,hPieces⟩ := gamma_native_prepared_partition_of_membership
    (extendBase A hCE) (fun i => extendBase (D i) hCE) hDA hDisj hCover hD T hT hWP
    (fun i => hFlags i (Finset.mem_univ i))
  exact ⟨E,hCE,Q,hQ,hPieces⟩

end IntegrationInACVF.Section7
