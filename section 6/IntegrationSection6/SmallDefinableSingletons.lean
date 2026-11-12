import CanonicalCountable
import Mathlib.ModelTheory.Encoding
import Mathlib.ModelTheory.Definability

/-! Counting unique definable elements in the inherited countable language. -/
noncomputable section
open Classical FirstOrder FirstOrder.Language Cardinal
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
namespace IntegrationInACVF.Section6
variable {M : Type} [LRV.Structure M]

theorem small_injective_definable_sets {κ : Cardinal} (hκ : Cardinal.aleph0 < κ)
    (S : Set M) {I : Type} (f : I → Set M) (hS : Cardinal.mk S < κ)
    (hinjf : Function.Injective f) (hf : ∀ i, S.Definable₁ LRV (f i)) : Cardinal.mk I < κ := by
  have hchoice (i : I) : ∃ φ : LRV.Formula (S ⊕ Fin 1),
      {v : Fin 1 → M | v 0 ∈ f i} = {v | φ.Realize (Sum.elim Subtype.val v)} :=
    Set.definable_iff_exists_formula_sum.mp (hf i)
  choose F hF using hchoice
  have hinj : Function.Injective F := by
    intro i j h
    apply hinjf
    have he : {v : Fin 1 → M | v 0 ∈ f i} = {v : Fin 1 → M | v 0 ∈ f j} :=
      (hF i).trans ((congrArg (fun φ : LRV.Formula (S ⊕ Fin 1) =>
        {v : Fin 1 → M | φ.Realize (Sum.elim Subtype.val v)}) h).trans (hF j).symm)
    ext x
    exact Set.ext_iff.mp he (fun _ => x)
  have hvars : Cardinal.mk (S ⊕ Fin 1) < κ := by
    simp only [Cardinal.mk_sum,Cardinal.lift_id]
    exact Cardinal.add_lt_of_lt hκ.le hS ((Cardinal.mk_lt_aleph0 (α := Fin 1)).trans hκ)
  have hlang : LRV.card < κ := (Cardinal.mk_le_aleph0 (α := LRV.Symbols)).trans_lt hκ
  have hformula : Cardinal.mk (LRV.Formula (S ⊕ Fin 1)) < κ := by
    have hi : Cardinal.mk (LRV.Formula (S ⊕ Fin 1)) ≤
        Cardinal.mk (Σ n, LRV.BoundedFormula (S ⊕ Fin 1) n) :=
      Cardinal.mk_le_of_injective (f := fun φ => (⟨0,φ⟩ : Σ n, LRV.BoundedFormula (S ⊕ Fin 1) n))
        (by intro x y h; exact Sigma.mk.inj_iff.mp h |>.2 |> eq_of_heq)
    have hb := @FirstOrder.Language.BoundedFormula.card_le LRV (S ⊕ Fin 1)
    simp only [Cardinal.lift_id] at hb
    exact hi.trans_lt (hb.trans_lt (max_lt hκ (Cardinal.add_lt_of_lt hκ.le hvars hlang)))
  exact (Cardinal.mk_le_of_injective hinj).trans_lt hformula

theorem small_definable_singletons {κ : Cardinal} (hκ : Cardinal.aleph0 < κ)
    (S X : Set M) (hS : Cardinal.mk S < κ)
    (hX : ∀ x ∈ X, S.Definable₁ LRV {x}) : Cardinal.mk X < κ :=
  small_injective_definable_sets hκ S (fun x : X => {x.val}) hS
    (fun x y h => Subtype.ext (Set.singleton_injective h)) (fun x => hX x.val x.property)

end IntegrationInACVF.Section6
