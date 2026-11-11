module

public import Mathlib.Data.Set.Function

@[expose] public section

/-! Actual coordinate-deletion and insertion maps for mixed VF/RV
tuples. The other coordinates retain their original index types. -/

open Set Classical

namespace IntegrationInACVF.Section3.CoordinateSlices

variable {X ι : Type*}

def Other (i : ι) := {j : ι // j ≠ i}

def tail (i : ι) (x : ι → X) : Other i → X := fun j => x j.val

noncomputable def insert (i : ι) (u : Other i → X) (a : X) : ι → X := by
  classical
  exact fun j => if h : j = i then a else u ⟨j,h⟩

theorem insert_same (i : ι) (u : Other i → X) (a : X) : insert i u a i = a := by
  classical
  simp [insert]

theorem insert_other (i : ι) (u : Other i → X) (a : X) (j : Other i) :
    insert i u a j.val = u j := by
  classical
  simp [insert,j.property]
  rfl

theorem tail_insert (i : ι) (u : Other i → X) (a : X) : tail i (insert i u a) = u := by
  funext j
  exact insert_other i u a j

theorem insert_tail (i : ι) (x : ι → X) : insert i (tail i x) (x i) = x := by
  classical
  funext j
  by_cases h : j = i
  · subst j
    exact insert_same i (tail i x) (x i)
  · exact insert_other i (tail i x) (x i) ⟨j,h⟩

theorem eq_of_tail_and_coordinate (i : ι) {x y : ι → X}
    (hTail : tail i x = tail i y) (hCoord : x i = y i) : x = y := by
  calc
    x = insert i (tail i x) (x i) := (insert_tail i x).symm
    _ = insert i (tail i y) (y i) := by rw [hTail,hCoord]
    _ = y := insert_tail i y

end IntegrationInACVF.Section3.CoordinateSlices
