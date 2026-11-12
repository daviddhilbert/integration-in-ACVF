import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Set.Finite.Lattice

/-! Deleting a coordinate preserves finite fibres when the image has
finite slices in that coordinate. This is the finite-category ingredient
for factoring an admissible elementary relation. -/
namespace IntegrationInACVF.Section6

theorem finite_fibres_coordinate_deletion {X Y : Type*} {n : ℕ}
    (f : X → Fin (n+1) → Y) (i : Fin (n+1)) (y₀ : Y)
    (hf : ∀ t, {x | f x = t}.Finite)
    (hs : ∀ t : Fin (n+1) → Y, {r | (∃ x, f x = r) ∧ ∀ j, j ≠ i → r j = t j}.Finite)
    (t : Fin n → Y) : {x | (fun j => f x (i.succAbove j)) = t}.Finite := by
  let T : Set (Fin (n+1) → Y) := {r | (∃ x, f x = r) ∧ ∀ j, j ≠ i → r j = Fin.insertNth (α := fun _ : Fin (n+1) => Y) i y₀ t j}
  have hT : T.Finite := hs (Fin.insertNth (α := fun _ : Fin (n+1) => Y) i y₀ t)
  apply (hT.biUnion (fun r _ => hf r)).subset
  intro x hx
  have hr : f x ∈ T := by
    refine ⟨⟨x,rfl⟩,?_⟩
    refine (Fin.forall_iff_succAbove (P := fun j => j ≠ i → f x j =
      Fin.insertNth (α := fun _ : Fin (n+1) => Y) i y₀ t j) i).mpr ?_
    refine ⟨fun h => (h rfl).elim,fun j _ => ?_⟩
    exact (congrFun hx j).trans (Fin.insertNth_apply_succAbove (α := fun _ : Fin (n+1) => Y) i y₀ t j).symm
  exact Set.mem_iUnion.mpr ⟨f x,Set.mem_iUnion.mpr ⟨hr,rfl⟩⟩

end IntegrationInACVF.Section6
