import Integration7.HeadTailPermutedPreparations
import Integration7.HeadTailVolumeSelectors

/-! Keep an actual chosen head preparation while prescribing any order
for its remaining contraction program. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section5
open IntegrationInACVF.Section5 IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {S : Set M} {n a : ℕ} {A : DefSet (M := M) S (n+1) a}

def headTailAppendedStandardProgram (σ : Equiv.Perm (Fin (n+1)))
    (T : HeadPreparation (vfPermutationImage A σ)) (τ : Equiv.Perm (Fin n))
    (D : StandardContraction T.contractedSet τ) : StandardContraction A ((headTailPerm τ).trans σ) :=
  standardFromProgram A _
    (.step (T.permuteTail τ) (orderedCastSource D.program (T.permute_tail_contracted_set τ).symm))
    (vfPermutationImage_trans A σ (headTailPerm τ))

end IntegrationInACVF.Section7
