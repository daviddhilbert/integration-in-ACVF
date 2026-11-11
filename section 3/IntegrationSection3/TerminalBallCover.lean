module

public import IntegrationSection3.FiniteBallProfiles

@[expose] public section

/-! A ball covered by finitely many terminal profile classes is one
whole class. Classes are intersections of balls; they are not assumed
to be ordinary balls in advance. -/

open Set Classical
open IntegrationInACVF.Section3.FiniteBallProfiles

namespace IntegrationInACVF.Section3.TerminalBallCover

variable {X J : Type*}

theorem ball_eq_terminal_class (T : Set J) (U : J → Set X)
    (hLam : ∀ i ∈ T, ∀ j ∈ T, U i ⊆ U j ∨ U j ⊆ U i ∨ Disjoint (U i) (U j))
    (F : Finset X) (hHit : ∀ j ∈ T, ∃ c ∈ F, c ∈ U j)
    (j : J) (hj : j ∈ T)
    (hAvoid : ∀ H : Finset (Set X),
      (∀ D ∈ H, ∃ k ∈ T, D = U k ∧ D ⊂ U j) →
      ∃ x ∈ U j, ∀ D ∈ H, x ∉ D)
    (hTerminal : ∀ x ∈ U j, IsTerminal T U x) :
    ∃ x, IsTerminal T U x ∧ U j = profileClass T U x := by
  classical
  let C : Set (Set X) := {D | ∃ x, IsTerminal T U x ∧ profileClass T U x = D}
  have hCfin : C.Finite := finite_terminal_classes T U hLam F hHit
  let K := hCfin.toFinset.filter (fun D => (D ∩ U j).Nonempty)
  have hKcover (x : X) (hx : x ∈ U j) : ∃ D ∈ K, x ∈ D := by
    let D := profileClass T U x
    have hxD : x ∈ D := rfl
    exact ⟨D,Finset.mem_filter.mpr
      ⟨hCfin.mem_toFinset.mpr ⟨x,hTerminal x hx,rfl⟩,x,hxD,hx⟩,hxD⟩
  have hClassSub (D : Set X) (hD : D ∈ K) : D ⊆ U j := by
    obtain ⟨hDC,a,haD,haj⟩ := Finset.mem_filter.mp hD
    obtain ⟨x,_,he⟩ := hCfin.mem_toFinset.mp hDC
    intro y hy
    have hax : profile T U a = profile T U x := (Set.ext_iff.mp he a).mpr haD
    have hyx : profile T U y = profile T U x := (Set.ext_iff.mp he y).mpr hy
    have hajP : j ∈ profile T U a := ⟨hj,haj⟩
    have hyjP : j ∈ profile T U y := by rw [hyx,← hax]; exact hajP
    exact hyjP.2
  by_cases hOne : ∃ D ∈ K, U j ⊆ D
  · obtain ⟨D,hD,hsub⟩ := hOne
    obtain ⟨x,hx,he⟩ := hCfin.mem_toFinset.mp (Finset.mem_filter.mp hD).1
    exact ⟨x,hx,(Set.Subset.antisymm hsub (hClassSub D hD)).trans he.symm⟩
  · have hData (D : K) : ∃ k ∈ T, D.val ⊆ U k ∧ U k ⊂ U j := by
      obtain ⟨x,hx,he⟩ := hCfin.mem_toFinset.mp (Finset.mem_filter.mp D.property).1
      have hNot : ¬ U j ⊆ D.val := fun hsub => hOne ⟨D.val,D.property,hsub⟩
      obtain ⟨w,hwj,hwD⟩ := Set.not_subset.mp hNot
      have hWitness : ∃ k ∈ T, x ∈ U k ∧ w ∉ U k := by
        by_contra hn
        apply hwD
        rw [← he,terminal_class_intersection T U x hx]
        intro k hk hxk
        by_contra hwk
        exact hn ⟨k,hk,hxk,hwk⟩
      obtain ⟨k,hk,hxk,hwk⟩ := hWitness
      have hDk : D.val ⊆ U k := by
        intro y hy
        have hyx : profile T U y = profile T U x := (Set.ext_iff.mp he y).mpr hy
        have hxkP : k ∈ profile T U x := ⟨hk,hxk⟩
        have hykP : k ∈ profile T U y := by rw [hyx]; exact hxkP
        exact hykP.2
      have hSub : U k ⊆ U j := by
        rcases hLam k hk j hj with hkj | hjk | hd
        · exact hkj
        · exact (hwk (hjk hwj)).elim
        · obtain ⟨a,haD,haj⟩ := (Finset.mem_filter.mp D.property).2
          exact (Set.disjoint_left.mp hd (hDk haD) haj).elim
      exact ⟨k,hk,hDk,Set.ssubset_iff_subset_ne.mpr
        ⟨hSub,fun heq => hwk (heq.symm ▸ hwj)⟩⟩
    choose k hk hDk hProper using hData
    let H := Finset.univ.image (fun D : K => U (k D))
    have hH (D : Set X) (hD : D ∈ H) : ∃ k ∈ T, D = U k ∧ D ⊂ U j := by
      obtain ⟨E,_,rfl⟩ := Finset.mem_image.mp hD
      exact ⟨k E,hk E,rfl,hProper E⟩
    obtain ⟨x,hx,hAvoidAll⟩ := hAvoid H hH
    obtain ⟨D,hD,hxD⟩ := hKcover x hx
    exact (hAvoidAll (U (k ⟨D,hD⟩))
      (Finset.mem_image.mpr ⟨⟨D,hD⟩,Finset.mem_univ _,rfl⟩) (hDk ⟨D,hD⟩ hxD)).elim

end IntegrationInACVF.Section3.TerminalBallCover
