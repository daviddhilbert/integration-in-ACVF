import IntegrationSection6.GroupifiedCongruence
import IntegrationSection6.CompletionLocalization

/-! The algebraic conclusion of6.22 for the single positive relation
[a]_1 = 1 + [b]_1. The geometric assertion that this generates Isp is separate. -/

noncomputable section
open Algebra

namespace IntegrationInACVF.Section6.BasicRelationEmbedding

variable {A : ℕ → Type*} [∀ k, AddCommMonoid (A k)] [DirectSum.GCommSemiring A]
local notation "G" => GrothendieckAddGroup

def congruence (a b : A 1) : RingCon (DirectSum ℕ A) :=
  ringConGen (fun x y => x = DirectSum.of A 1 a ∧ y = 1 + DirectSum.of A 1 b)

theorem groupified_ideal (a b : A 1) :
    GroupifiedCongruence.relationIdeal (congruence a b) = CompletionLocalization.relationIdeal a b := by
  rw [congruence,GroupifiedCongruence.relationIdeal_singleton,CompletionLocalization.relationIdeal]
  congr 1
  congr 1
  rw [map_add,map_one]
  change CompletionLocalization.homogeneous 1 a - (1 + CompletionLocalization.homogeneous 1 b) =
    (CompletionLocalization.homogeneous 1 a - CompletionLocalization.homogeneous 1 b) - 1
  ring

def quotientComparison (a b : A 1) :
    G (congruence a b).Quotient ≃+*
      (CompletionLocalization.Ring A ⧸ CompletionLocalization.relationIdeal a b) :=
  (GroupifiedCongruence.quotientEquiv (congruence a b)).symm.trans
    (Ideal.quotEquivOfEq (groupified_ideal a b))

@[simp] theorem quotientComparison_of (a b : A 1) (k : ℕ) (x : A k) :
    quotientComparison a b (GrothendieckAddGroup.ofRingHom
      ((congruence a b).mk' (DirectSum.of A k x))) =
    Ideal.Quotient.mk (CompletionLocalization.relationIdeal a b)
      (CompletionLocalization.homogeneous k x) := by
  rw [← GroupifiedCongruence.quotientEquiv_of (congruence a b) (DirectSum.of A k x)]
  change (Ideal.quotEquivOfEq (groupified_ideal a b))
    ((GroupifiedCongruence.quotientEquiv (congruence a b)).symm
      ((GroupifiedCongruence.quotientEquiv (congruence a b)) _)) = _
  rw [RingEquiv.symm_apply_apply]
  rfl

/-- Canonical injective ring map, with j=[a]_1-[b]_1. -/
def embedding (a b : A 1) : G (congruence a b).Quotient →+* CompletionLocalization.Target a b :=
  (CompletionLocalization.quotientEmbedding a b).comp (quotientComparison a b).toRingHom

theorem embedding_injective (a b : A 1) : Function.Injective (embedding a b) :=
  (CompletionLocalization.quotientEmbedding_injective a b).comp (quotientComparison a b).injective

@[simp] theorem embedding_of_homogeneous (a b : A 1) (k : ℕ) (x : A k) :
    embedding a b (GrothendieckAddGroup.ofRingHom
      ((congruence a b).mk' (DirectSum.of A k x))) =
      algebraMap (CompletionLocalization.Ring A) (CompletionLocalization.Target a b)
        (CompletionLocalization.homogeneous k x) *
          IsLocalization.Away.invSelf (CompletionLocalization.pivot a b) ^ k := by
  change CompletionLocalization.quotientEmbedding a b (quotientComparison a b _) = _
  rw [quotientComparison_of,CompletionLocalization.quotientEmbedding_mk_homogeneous]

end IntegrationInACVF.Section6.BasicRelationEmbedding
