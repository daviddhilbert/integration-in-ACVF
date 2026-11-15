import Integration7.NativeFiniteMixedUnions
import IntegrationSection5.RelativeSpecialRestriction

/-! Finite partition preparation over the actual original real context.
Each prepared piece has its own genuine special bijection from the
specified source piece and is an actual RV pullback. -/
noncomputable section
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section5

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

structure NativePreparedMixedPartition {S : Set M} {n a : ℕ} {ι : Type} [Fintype ι]
    (A : DefSet (M := M) S n a) (D : ι → DefSet (M := M) S n a) where
  arity : ℕ
  target : DefSet (M := M) S n arity
  special : SpecialBijection A target
  pullback : IsRVPullback (carrier target)
  pieces : ι → DefSet (M := M) S n arity
  pieceSpecial : ∀ i, SpecialBijection (D i) (pieces i)
  piecePullback : ∀ i, IsRVPullback (carrier (pieces i))
  subset : ∀ i, carrier (pieces i) ⊆ carrier target
  disjoint : ∀ i j, i ≠ j → Disjoint (carrier (pieces i)) (carrier (pieces j))
  cover : carrier target = nativeMixedFiniteUnionSet pieces Finset.univ

end IntegrationInACVF.Section7
