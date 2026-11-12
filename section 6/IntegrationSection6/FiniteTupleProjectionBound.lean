import Mathlib.Data.Set.Card
import Mathlib.SetTheory.Cardinal.Finite

/-! A finite tuple family is bounded by the product of its finite
coordinate images. This reduces tuple-fibre compactness to scalar rows. -/
noncomputable section
namespace IntegrationInACVF.Section6
open Classical

theorem finite_tuple_ncard_le_coordinate_product {Y : Type*} {m : ℕ}
    (T : Set (Fin m → Y)) (hT : T.Finite) :
    T.ncard ≤ ∏ j : Fin m, ((fun b : Fin m → Y => b j) '' T).ncard := by
  let C (j : Fin m) := (fun b : Fin m → Y => b j) '' T
  have hC (j : Fin m) : (C j).Finite := hT.image _
  letI (j : Fin m) : Finite (C j) := (hC j).to_subtype
  let f (b : T) : ∀ j : Fin m, C j := fun j => ⟨b.val j,⟨b.val,b.property,rfl⟩⟩
  have hf : Function.Injective f := by
    intro a b hab
    apply Subtype.ext
    funext j
    exact congrArg (fun q : C j => q.val) (congrFun hab j)
  have h := Nat.card_le_card_of_injective f hf
  simpa only [Nat.card_coe_set_eq,Nat.card_pi] using h

end IntegrationInACVF.Section6
