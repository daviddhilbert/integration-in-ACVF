import IntegrationSection5.PartialNaturalMap
import IntegrationSection6.GammaVFCoordinateIsomorphisms

/-! Reorder frozen-first family coordinates into the active-first order
of the checked Section5 partial contraction programs. -/
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section4 SpecialTransformations.Section5
open IntegrationInACVF.Section5
namespace IntegrationInACVF.Section6

def activeFrozenIndex (p n : ℕ) (j : Fin (p+n)) : Fin (p+n) :=
  if h : j.val < n then ⟨p+j.val,by omega⟩ else ⟨j.val-n,by omega⟩

def frozenActiveIndex (p n : ℕ) (j : Fin (p+n)) : Fin (p+n) :=
  if h : j.val < p then ⟨n+j.val,by omega⟩ else ⟨j.val-p,by omega⟩

def activeFrozenShuffle (p n : ℕ) : Equiv.Perm (Fin (p+n)) where
  toFun := activeFrozenIndex p n
  invFun := frozenActiveIndex p n
  left_inv j := by
    unfold activeFrozenIndex frozenActiveIndex
    split_ifs with h₁ h₂ h₂
    · change p+j.val < p at h₂
      omega
    · apply Fin.ext
      change p+j.val-p = j.val
      omega
    · apply Fin.ext
      change n+(j.val-n) = j.val
      omega
    · change ¬j.val-n < p at h₂
      have hj := j.isLt
      omega
  right_inv j := by
    unfold activeFrozenIndex frozenActiveIndex
    split_ifs with h₁ h₂ h₂
    · change n+j.val < n at h₂
      omega
    · apply Fin.ext
      change n+j.val-n = j.val
      omega
    · apply Fin.ext
      change p+(j.val-p) = j.val
      omega
    · change ¬j.val-p < n at h₂
      have hj := j.isLt
      omega

theorem activeFrozenShuffle_val (p n : ℕ) (j : Fin (p+n)) :
    (activeFrozenShuffle p n j).val = if j.val < n then p+j.val else j.val-n := by
  change (activeFrozenIndex p n j).val = _
  unfold activeFrozenIndex
  split_ifs <;> rfl

theorem frozenIndex_val (p n : ℕ) (j : Fin p) : (frozenIndex p n j).val = n+j.val := by
  induction n with
  | zero => simp [frozenIndex]
  | succ n ih => simp only [frozenIndex,Fin.val_succ,ih]; omega

theorem activeFrozenShuffle_active (p n : ℕ) (j : Fin n) :
    activeFrozenShuffle p n (activeIndex p n j) = Fin.natAdd p j := by
  apply Fin.ext
  rw [activeFrozenShuffle_val]
  change (if j.val < n then p+j.val else j.val-n) = p+j.val
  rw [if_pos j.isLt]

theorem activeFrozenShuffle_frozen (p n : ℕ) (j : Fin p) :
    activeFrozenShuffle p n (frozenIndex p n j) = Fin.castAdd n j := by
  apply Fin.ext
  rw [activeFrozenShuffle_val,frozenIndex_val]
  rw [if_neg (by omega)]
  change n+j.val-n = j.val
  omega

end IntegrationInACVF.Section6
