module

public import IntegrationSection3.AffineHoleCosets
public import Mathlib.Data.Finset.Prod

@[expose] public section

/-! Finite affine closure of maximal-hole classes in the actual additive
quotient. It uses all ordered pairs and finitely many natural multiples.
The construction does not select a hole or one of its representatives. -/

namespace IntegrationInACVF.Section3.AffineHoleClosure

variable {K Γ : Type*} [Field K] [LinearOrderedCommGroupWithZero Γ]

def step (H : AddSubgroup K) (a b : K ⧸ H) (n : ℕ) : K ⧸ H := a + n • (b-a)

noncomputable def closure (H : AddSubgroup K) (F : Finset (K ⧸ H)) (N : ℕ) : Finset (K ⧸ H) := by
  classical
  exact F ∪ (F.product F).biUnion (fun p =>
    if p.1 ≠ p.2 then Finset.univ.image (fun n : Fin (N+1) => step H p.1 p.2 n.val) else ∅)

theorem mk_step (H : AddSubgroup K) (a b : K) (n : ℕ) :
    QuotientAddGroup.mk' H (AffineHoleCosets.affine a b n) =
      step H (QuotientAddGroup.mk' H a) (QuotientAddGroup.mk' H b) n := by
  simp only [step,AffineHoleCosets.affine,← nsmul_eq_mul,map_add,map_nsmul,map_sub]

theorem subset_closure (H : AddSubgroup K) (F : Finset (K ⧸ H)) (N : ℕ) :
    F ⊆ closure H F N := by
  classical
  intro a ha
  exact Finset.mem_union_left _ ha

theorem step_mem_closure (H : AddSubgroup K) (F : Finset (K ⧸ H)) (N : ℕ)
    (a b : K ⧸ H) (ha : a ∈ F) (hb : b ∈ F) (hab : a ≠ b) (n : ℕ) (hn : n ≤ N) :
    step H a b n ∈ closure H F N := by
  classical
  apply Finset.mem_union_right
  apply Finset.mem_biUnion.mpr
  refine ⟨(a,b),Finset.mem_product.mpr ⟨ha,hb⟩,?_⟩
  rw [ite_eq_left hab]
  exact Finset.mem_image.mpr ⟨⟨n,Nat.lt_succ_of_le hn⟩,Finset.mem_univ _,rfl⟩

theorem closure_strict (v : Valuation K Γ)
    (hunit : ∀ n : ℕ, n ≠ 0 → v (n : K) = 1)
    (H : AddSubgroup K) (r a b : K) (hH : ∀ x : K, x ∈ H ↔ v x < v r)
    (hba : v (b-a) = v r) (F : Finset (K ⧸ H)) (N : ℕ) (hcard : F.card ≤ N)
    (ha : QuotientAddGroup.mk' H a ∈ F) (hb : QuotientAddGroup.mk' H b ∈ F)
    (hab : QuotientAddGroup.mk' H a ≠ QuotientAddGroup.mk' H b) : F ⊂ closure H F N := by
  obtain ⟨n,hn,hnew⟩ := AffineHoleCosets.exists_new_coset v hunit H r a b hH hba F N hcard
  have hmem : QuotientAddGroup.mk' H (AffineHoleCosets.affine a b n) ∈ closure H F N := by
    rw [mk_step]
    exact step_mem_closure H F N _ _ ha hb hab n hn
  refine ⟨subset_closure H F N,?_⟩
  intro hrev
  exact hnew (hrev hmem)

theorem affine_mem_closed_parent (v : Valuation K Γ)
    (hunit : ∀ n : ℕ, n ≠ 0 → v (n : K) = 1)
    (r c a b : K) (ha : v (a-c) ≤ v r) (hb : v (b-c) ≤ v r) (n : ℕ) :
    v (AffineHoleCosets.affine a b n-c) ≤ v r := by
  have hba : v (b-a) ≤ v r := by
    have he : b-a = (b-c)-(a-c) := by ring
    rw [he]
    exact (v.map_sub _ _).trans (max_le hb ha)
  have hstep := AffineHoleCosets.affine_mem_closed v hunit r a b hba n
  have he : AffineHoleCosets.affine a b n-c = (AffineHoleCosets.affine a b n-a)+(a-c) := by ring
  rw [he]
  exact (v.map_add _ _).trans (max_le hstep ha)

/-- The finite affine closure stays among the small-ball classes of the
same parent closed ball. The statement quantifies representatives only in
the geometry proof; closure itself is defined on quotient classes. -/
theorem closure_stays_in_parent (v : Valuation K Γ)
    (hunit : ∀ n : ℕ, n ≠ 0 → v (n : K) = 1)
    (H : AddSubgroup K) (r c : K) (F : Finset (K ⧸ H)) (N : ℕ)
    (hF : ∀ q ∈ F, ∃ a : K, v (a-c) ≤ v r ∧ QuotientAddGroup.mk' H a = q) :
    ∀ q ∈ closure H F N, ∃ a : K, v (a-c) ≤ v r ∧ QuotientAddGroup.mk' H a = q := by
  classical
  intro q hq
  rcases Finset.mem_union.mp hq with hq | hq
  · exact hF q hq
  · obtain ⟨p,hp,hqp⟩ := Finset.mem_biUnion.mp hq
    obtain ⟨hp1,hp2⟩ := Finset.mem_product.mp hp
    by_cases hne : p.1 ≠ p.2
    · rw [ite_eq_left hne] at hqp
      obtain ⟨n,_,rfl⟩ := Finset.mem_image.mp hqp
      obtain ⟨a,ha,haq⟩ := hF p.1 hp1
      obtain ⟨b,hb,hbq⟩ := hF p.2 hp2
      refine ⟨AffineHoleCosets.affine a b n.val,affine_mem_closed_parent v hunit r c a b ha hb n.val,?_⟩
      rw [mk_step,haq,hbq]
    · rw [ite_eq_right hne] at hqp
      exact (Finset.notMem_empty _ hqp).elim

end IntegrationInACVF.Section3.AffineHoleClosure
