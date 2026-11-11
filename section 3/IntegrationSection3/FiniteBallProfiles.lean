module

public import IntegrationSection3.BallSupport
public import Mathlib.Order.Preorder.Finite

@[expose] public section

/-! Maximal membership profiles in a laminar family with a finite hitting
set. The hitting points may be arbitrary; maximal profiles are defined
intrinsically, without naming them. -/

open Set Classical

namespace IntegrationInACVF.Section3.FiniteBallProfiles

variable {X J : Type*}

def profile (T : Set J) (U : J → Set X) (x : X) : Set J :=
  {j | j ∈ T ∧ x ∈ U j}

def IsTerminal (T : Set J) (U : J → Set X) (x : X) : Prop :=
  (profile T U x).Nonempty ∧
    ∀ y, profile T U x ⊆ profile T U y → profile T U y ⊆ profile T U x

def profileClass (T : Set J) (U : J → Set X) (x : X) : Set X :=
  {y | profile T U y = profile T U x}

theorem finite_avoidance (T : Set J) (U : J → Set X)
    (hLam : ∀ i ∈ T, ∀ j ∈ T, U i ⊆ U j ∨ U j ⊆ U i ∨ Disjoint (U i) (U j))
    (x : X) (hne : (profile T U x).Nonempty) (F : Finset X)
    (hAvoid : ∀ c ∈ F, ∃ j ∈ T, x ∈ U j ∧ c ∉ U j) :
    ∃ j ∈ T, x ∈ U j ∧ ∀ c ∈ F, c ∉ U j := by
  classical
  induction F using Finset.induction_on with
  | empty =>
    obtain ⟨j,hj,hxj⟩ := hne
    exact ⟨j,hj,hxj,by simp⟩
  | @insert c F hc ih =>
    obtain ⟨i,hi,hxi,hFi⟩ := ih (fun d hd => hAvoid d (Finset.mem_insert_of_mem hd))
    obtain ⟨j,hj,hxj,hcj⟩ := hAvoid c (Finset.mem_insert_self c F)
    rcases hLam i hi j hj with hij | hji | hDis
    · refine ⟨i,hi,hxi,?_⟩
      intro d hd
      rcases Finset.mem_insert.mp hd with rfl | hd
      · exact fun hci => hcj (hij hci)
      · exact hFi d hd
    · refine ⟨j,hj,hxj,?_⟩
      intro d hd
      rcases Finset.mem_insert.mp hd with rfl | hd
      · exact hcj
      · exact fun hdj => hFi d hd (hji hdj)
    · exact (Set.disjoint_left.mp hDis hxi hxj).elim

theorem exists_dominating_point (T : Set J) (U : J → Set X)
    (hLam : ∀ i ∈ T, ∀ j ∈ T, U i ⊆ U j ∨ U j ⊆ U i ∨ Disjoint (U i) (U j))
    (F : Finset X) (hHit : ∀ j ∈ T, ∃ c ∈ F, c ∈ U j)
    (x : X) (hne : (profile T U x).Nonempty) :
    ∃ c ∈ F, profile T U x ⊆ profile T U c := by
  classical
  by_contra hn
  have hAvoid (c : X) (hc : c ∈ F) : ∃ j ∈ T, x ∈ U j ∧ c ∉ U j := by
    have hnot : ¬ profile T U x ⊆ profile T U c := fun hsub => hn ⟨c,hc,hsub⟩
    obtain ⟨j,⟨hj,hxj⟩,hnj⟩ := Set.not_subset.mp hnot
    exact ⟨j,hj,hxj,fun hcj => hnj ⟨hj,hcj⟩⟩
  obtain ⟨j,hj,_,hAvoidAll⟩ := finite_avoidance T U hLam x hne F hAvoid
  obtain ⟨c,hc,hcj⟩ := hHit j hj
  exact hAvoidAll c hc hcj

theorem terminal_class_hits (T : Set J) (U : J → Set X)
    (hLam : ∀ i ∈ T, ∀ j ∈ T, U i ⊆ U j ∨ U j ⊆ U i ∨ Disjoint (U i) (U j))
    (F : Finset X) (hHit : ∀ j ∈ T, ∃ c ∈ F, c ∈ U j)
    (x : X) (hx : IsTerminal T U x) : ∃ c ∈ F, c ∈ profileClass T U x := by
  obtain ⟨c,hc,hsub⟩ := exists_dominating_point T U hLam F hHit x hx.1
  exact ⟨c,hc,Set.Subset.antisymm (hx.2 c hsub) hsub⟩

theorem exists_terminal_in_ball (T : Set J) (U : J → Set X)
    (hLam : ∀ i ∈ T, ∀ j ∈ T, U i ⊆ U j ∨ U j ⊆ U i ∨ Disjoint (U i) (U j))
    (F : Finset X) (hHit : ∀ j ∈ T, ∃ c ∈ F, c ∈ U j)
    (j : J) (hj : j ∈ T) : ∃ c ∈ F, c ∈ U j ∧ IsTerminal T U c := by
  classical
  let G := F.filter (fun x => x ∈ U j)
  obtain ⟨d,hd,hdj⟩ := hHit j hj
  have hG : G.Nonempty := ⟨d,Finset.mem_filter.mpr ⟨hd,hdj⟩⟩
  obtain ⟨c,hc,hmax⟩ := Finset.exists_maximalFor (profile T U) G hG
  obtain ⟨hcF,hcj⟩ := Finset.mem_filter.mp hc
  refine ⟨c,hcF,hcj,⟨⟨j,hj,hcj⟩,?_⟩⟩
  intro y hcy
  have hyj : y ∈ U j := (hcy ⟨hj,hcj⟩).2
  obtain ⟨e,he,hye⟩ := exists_dominating_point T U hLam F hHit y ⟨j,hj,hyj⟩
  have hej : e ∈ U j := (hye ⟨hj,hyj⟩).2
  have hec := hmax (Finset.mem_filter.mpr ⟨he,hej⟩) (hcy.trans hye)
  exact hye.trans hec

theorem terminal_class_intersection (T : Set J) (U : J → Set X)
    (x : X) (hx : IsTerminal T U x) :
    profileClass T U x = {y | ∀ j ∈ T, x ∈ U j → y ∈ U j} := by
  ext y
  constructor
  · intro he j hj hxj
    have hsub : profile T U x ⊆ profile T U y := (Set.Subset.antisymm_iff.mp he).2
    exact (hsub ⟨hj,hxj⟩).2
  · intro hy
    have hsub : profile T U x ⊆ profile T U y := fun j hj => ⟨hj.1,hy j hj.1 hj.2⟩
    exact Set.Subset.antisymm (hx.2 y hsub) hsub

theorem finite_terminal_classes (T : Set J) (U : J → Set X)
    (hLam : ∀ i ∈ T, ∀ j ∈ T, U i ⊆ U j ∨ U j ⊆ U i ∨ Disjoint (U i) (U j))
    (F : Finset X) (hHit : ∀ j ∈ T, ∃ c ∈ F, c ∈ U j) :
    {C | ∃ x, IsTerminal T U x ∧ profileClass T U x = C}.Finite := by
  apply (F.finite_toSet.image (profileClass T U)).subset
  rintro C ⟨x,hx,rfl⟩
  obtain ⟨c,hc,he⟩ := terminal_class_hits T U hLam F hHit x hx
  refine ⟨c,hc,?_⟩
  ext y
  change (profile T U y = profile T U c) ↔ (profile T U y = profile T U x)
  change profile T U c = profile T U x at he
  rw [he]

end IntegrationInACVF.Section3.FiniteBallProfiles
