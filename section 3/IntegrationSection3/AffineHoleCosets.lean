module

public import IntegrationSection3.InfiniteCosets
public import Mathlib.Data.Finset.Card

@[expose] public section

/-! The finite affine construction used to produce an additional maximal
hole from two distinct ones. It is independent of representatives in the
small-ball cosets. All ordered pairs can therefore be used without naming
one hole over the parameter base. -/

open Set

namespace IntegrationInACVF.Section3.AffineHoleCosets

variable {K Γ : Type*} [Field K] [LinearOrderedCommGroupWithZero Γ]

def affine (a b : K) (n : ℕ) : K := a + (n : K) * (b-a)

theorem congr (H : AddSubgroup K) {a a' b b' : K}
    (ha : QuotientAddGroup.mk' H a' = QuotientAddGroup.mk' H a)
    (hb : QuotientAddGroup.mk' H b' = QuotientAddGroup.mk' H b) (n : ℕ) :
    QuotientAddGroup.mk' H (affine a' b' n) = QuotientAddGroup.mk' H (affine a b n) := by
  simp only [affine,← nsmul_eq_mul,map_add,map_nsmul,map_sub,ha,hb]

theorem cosets_injective (v : Valuation K Γ)
    (hunit : ∀ n : ℕ, n ≠ 0 → v (n : K) = 1)
    (H : AddSubgroup K) (r a b : K)
    (hH : ∀ x : K, x ∈ H ↔ v x < v r) (hba : v (b-a) = v r) :
    Function.Injective (fun n => QuotientAddGroup.mk' H (affine a b n)) := by
  intro n m he
  by_contra hne
  have hd := QuotientAddGroup.eq_iff_sub_mem.mp he
  have hlt := (hH _).mp hd
  have hdif : affine a b n - affine a b m = ((n : K)-(m : K))*(b-a) := by
    unfold affine
    ring
  rw [hdif,map_mul,InfiniteCosets.map_nat_difference v hunit n m hne,one_mul,hba] at hlt
  exact lt_irrefl _ hlt

theorem affine_mem_closed (v : Valuation K Γ)
    (hunit : ∀ n : ℕ, n ≠ 0 → v (n : K) = 1)
    (r a b : K) (hba : v (b-a) ≤ v r) (n : ℕ) :
    v (affine a b n-a) ≤ v r := by
  unfold affine
  rw [add_sub_cancel_left,map_mul]
  by_cases hn : n = 0
  · subst n
    simp only [Nat.cast_zero,map_zero,zero_mul]
    exact zero_le
  · rw [hunit n hn,one_mul]
    exact hba

/-- The first N+1 distinct classes cannot all lie in a family of size at
most N. This is a finite construction, rather than an infinite union. -/
theorem exists_new_coset (v : Valuation K Γ)
    (hunit : ∀ n : ℕ, n ≠ 0 → v (n : K) = 1)
    (H : AddSubgroup K) (r a b : K)
    (hH : ∀ x : K, x ∈ H ↔ v x < v r) (hba : v (b-a) = v r)
    (F : Finset (K ⧸ H)) (N : ℕ) (hcard : F.card ≤ N) :
    ∃ n ≤ N, QuotientAddGroup.mk' H (affine a b n) ∉ F := by
  classical
  let f := fun n => QuotientAddGroup.mk' H (affine a b n)
  have hinj := cosets_injective v hunit H r a b hH hba
  have hsize : F.card < ((Finset.range (N+1)).image f).card := by
    rw [Finset.card_image_of_injective _ hinj,Finset.card_range]
    exact Nat.lt_succ_of_le hcard
  obtain ⟨q,hq,hqF⟩ := Finset.exists_mem_notMem_of_card_lt_card hsize
  obtain ⟨n,hn,rfl⟩ := Finset.mem_image.mp hq
  exact ⟨n,Nat.le_of_lt_succ (Finset.mem_range.mp hn),hqF⟩

end IntegrationInACVF.Section3.AffineHoleCosets
