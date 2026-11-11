import IntegrationSection5.GammaUnaryPartition
import IntegrationSection5.UnaryChainExtension

/-! A single common internal real presentation for every actual factor of
a finite original-Gamma partition. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section5 SpecialTransformations.Section3
namespace IntegrationInACVF.Section5
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {G : GammaParameters.Base (M := M)} {n m w : ℕ}
variable {A : Set (Point (M := M) n m)} {B : Set (Point (M := M) n w)}

structure RealizedUnaryPartition (S : Set M) (e : GammaIso G A B) (Q : GammaUnaryPartition e) where
  codes : Set M
  contains : S ⊆ codes
  source : Q.pieces → DefSet (M := M) codes n m
  target : Q.pieces → DefSet (M := M) codes n w
  source_eq : ∀ D : Q.pieces, carrier (source D) = D.val
  chains : ∀ D : Q.pieces, UnaryChain codes n (source D) (target D)
  gamma : ∀ D : Q.pieces, GammaUnaryChainDefinable G (chains D)
  agrees : ∀ D : Q.pieces, ∀ a : source D,
    ((chains D).toMap a).val =
      (e.equiv ⟨a.val,Q.subset D.val D.property (source_eq D ▸ a.property)⟩).val

theorem GammaUnaryPartition.realize (e : GammaIso G A B) (Q : GammaUnaryPartition e) (S : Set M) :
    Nonempty (RealizedUnaryPartition S e Q) := by
  choose C T hT using fun D : Q.pieces => Q.factors D.val D.property
  choose R hSR hAr hCr t htG ht using fun D : Q.pieces => (T D).realize S
  let U := S ∪ ⋃ D : Q.pieces, R D
  have hRU (D : Q.pieces) : R D ⊆ U := fun _ h => Or.inr (Set.mem_iUnion.mpr ⟨D,h⟩)
  let src (D : Q.pieces) : DefSet (M := M) U n m :=
    extendBase (@PresentedSet.mk M sM (pointSpace n m) (R D) D.val (hAr D)) (hRU D)
  let tgt (D : Q.pieces) : DefSet (M := M) U n w :=
    extendBase (@PresentedSet.mk M sM (pointSpace n w) (R D) (C D) (hCr D)) (hRU D)
  let ts (D : Q.pieces) : UnaryChain U n (src D) (tgt D) := (t D).extendBase (hRU D)
  refine ⟨{ codes := U
            contains := Set.subset_union_left
            source := src
            target := tgt
            source_eq := fun _ => rfl
            chains := ts
            gamma := fun D => (t D).extendBase_gamma (hRU D) (htG D)
            agrees := ?_ }⟩
  intro D a
  exact ((t D).extendBase_val (hRU D) a).trans ((ht D a).trans (hT D a))

end IntegrationInACVF.Section5
