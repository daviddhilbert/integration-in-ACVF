import IntegrationSection5.HeadPreparation
import IntegrationSection5.RelativeLabelPreservation

/-! Successive actual coordinate preparations in the identity order. Each
step drops the prepared head VF coordinate and retains its RV value. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.DefinableGeometry.Space.prod
  SpecialTransformations.Section4.realSpace SpecialTransformations.Milestone0.sortEval
  SpecialTransformations.Section4.vfSpace SpecialTransformations.Section4.rvSpace
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section5
namespace IntegrationInACVF.Section5
variable {M : Type} [sM : LRV.Structure M] [M ⊨ Axioms.ACVF]

inductive OrderedContractionProgram (S : Set M) : {n m l : ℕ} →
    DefSet (M := M) S n m → DefSet (M := M) S 0 l → Type where
  | zero {m : ℕ} (A : DefSet (M := M) S 0 m) : OrderedContractionProgram S A A
  | step {n m l : ℕ} {A : DefSet (M := M) S (n+1) m} {U : DefSet (M := M) S 0 l}
      (T : HeadPreparation A) (tail : OrderedContractionProgram S T.contractedSet U) :
      OrderedContractionProgram S A U

namespace OrderedContractionProgram
variable {S : Set M} {n m l : ℕ}
variable {A : DefSet (M := M) S n m} {U : DefSet (M := M) S 0 l}

def toMap {a b c : ℕ} {X : DefSet (M := M) S a b} {Y : DefSet (M := M) S 0 c} :
    OrderedContractionProgram S X Y → Map X Y
  | .zero A => Map.id A
  | .step T tail => Map.comp tail.toMap T.contractionMap

theorem surjective (T : OrderedContractionProgram S A U) : Function.Surjective T.toMap := by
  induction T with
  | zero A => exact Function.surjective_id
  | step T tail ih => exact ih.comp T.contractionMap_surjective

theorem rvArity_le (T : OrderedContractionProgram S A U) : m ≤ l := by
  induction T with
  | zero A => exact le_rfl
  | step T tail ih =>
    have h := specialRelative_rvArity_le T.special
    change 1+T.arity ≤ _ at ih
    omega

theorem oldLabels (T : OrderedContractionProgram S A U) (a : A) (j : Fin m) :
    (T.toMap a).val.2 (suffixIndex T.rvArity_le j) = a.val.2 j := by
  induction T with
  | zero A =>
    apply congrArg a.val.2
    apply Fin.ext
    simp [suffixIndex]
  | @step n m l A U T tail ih =>
    let hT := specialRelative_rvArity_le T.special
    let k := Fin.natAdd 1 (suffixIndex hT j)
    have htail := tail.rvArity_le
    have hindex : suffixIndex htail k = suffixIndex (step T tail |>.rvArity_le) j := by
      apply Fin.ext
      change l-(1+T.arity)+(1+(T.arity-m+j.val)) = l-m+j.val
      omega
    have h := ih (T.contractionMap a) k
    rw [hindex] at h
    change (tail.toMap (T.contractionMap a)).val.2 (suffixIndex (step T tail |>.rvArity_le) j) = _
    refine h.trans ?_
    have hk := congrArg (fun p : Point (M := M) n (1+T.arity) => p.2 k)
      (headKeyMap_apply T.target (T.map a))
    exact hk.trans (by
      change Fin.append (fun _ : Fin 1 => rv (vfAt (T.map a).val 0)) (T.map a).val.2
        (Fin.natAdd 1 (suffixIndex hT j)) = a.val.2 j
      rw [Fin.append_right]
      exact specialRelative_oldLabels T.special a j)

def volumeIndex {a b c : ℕ} {X : DefSet (M := M) S a b} {Y : DefSet (M := M) S 0 c} :
    OrderedContractionProgram S X Y → Fin a → Fin c
  | .zero _,i => Fin.elim0 i
  | .step _ tail,i => Fin.cases (suffixIndex tail.rvArity_le 0) tail.volumeIndex i

theorem volumeIndex_before_oldLabels (T : OrderedContractionProgram S A U) (i : Fin n) :
    (T.volumeIndex i).val < l-m := by
  induction T with
  | zero A => exact Fin.elim0 i
  | @step n m l A U T tail ih =>
    have hT := specialRelative_rvArity_le T.special
    have htail := tail.rvArity_le
    cases i using Fin.cases with
    | zero =>
      change l-(1+T.arity)+0 < l-m
      omega
    | succ i =>
      have h := ih i
      change (tail.volumeIndex i).val < l-(1+T.arity) at h
      exact h.trans_le (Nat.sub_le_sub_left (by omega) l)

theorem volumeIndex_injective (T : OrderedContractionProgram S A U) :
    Function.Injective T.volumeIndex := by
  induction T with
  | zero A => intro i; exact Fin.elim0 i
  | @step n m l A U T tail ih =>
    intro i j he
    cases i using Fin.cases with
    | zero =>
      cases j using Fin.cases with
      | zero => rfl
      | succ j =>
        have hj := tail.volumeIndex_before_oldLabels j
        have h := congrArg Fin.val he
        change l-(1+T.arity)+0 = (tail.volumeIndex j).val at h
        omega
    | succ i =>
      cases j using Fin.cases with
      | zero =>
        have hi := tail.volumeIndex_before_oldLabels i
        have h := congrArg Fin.val he
        change (tail.volumeIndex i).val = l-(1+T.arity)+0 at h
        omega
      | succ j => exact congrArg Fin.succ (ih he)

end OrderedContractionProgram
end IntegrationInACVF.Section5
