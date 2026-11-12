import IntegrationSection6.GammaSchemaRowAgreement
import IntegrationSection6.GammaFamilyBijectionValidity

/-! First-order map validity transports across literal rows, even when
VF parameters are replaced by RV keys of a different arity. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
namespace IntegrationInACVF.Section6
variable {M : Type} [sM : LRV.Structure M]
variable {p q a b : ℕ} {sp : Fin p → SortTag} {sq : Fin q → SortTag} {sy : Fin b → SortTag}

theorem finiteMapRowValid_of_rows
    {D : Set (Fin (p+a) → M)} {E : Set (Fin (q+a) → M)}
    {V : Set (Fin ((p+a)+b) → M)} {W : Set (Fin ((q+a)+b) → M)}
    {z : Fin p → M} {t : Fin q → M} {bound : ℕ}
    (ht : ∀ j, sortEval (sq j) (t j))
    (hD : ∀ x, Fin.append z x ∈ D ↔ Fin.append t x ∈ E)
    (hV : ∀ x y, Fin.append (Fin.append z x) y ∈ V ↔ Fin.append (Fin.append t x) y ∈ W)
    (h : finiteMapRowValid sp sy D V bound z) : finiteMapRowValid sq sy E W bound t := by
  refine ⟨ht,?_,?_,?_⟩
  · intro x hx
    exact (existsUnique_congr (fun y => hV x y)).mp (h.2.1 x ((hD x).mpr hx))
  · intro x y hxy
    exact (hD x).mp (h.2.2.1 x y ((hV x y).mpr hxy))
  · intro y hy
    have he : {x | Fin.append (Fin.append t x) y ∈ W} = {x | Fin.append (Fin.append z x) y ∈ V} :=
      Set.ext (fun x => (hV x y).symm)
    rw [he]
    exact h.2.2.2 y hy

theorem bijectiveMapRowValid_of_rows
    {D : Set (Fin (p+a) → M)} {E : Set (Fin (p+b) → M)}
    {D' : Set (Fin (q+a) → M)} {E' : Set (Fin (q+b) → M)}
    {V : Set (Fin ((p+a)+b) → M)} {W : Set (Fin ((q+a)+b) → M)}
    {z : Fin p → M} {t : Fin q → M}
    (ht : ∀ j, sortEval (sq j) (t j))
    (hD : ∀ x, Fin.append z x ∈ D ↔ Fin.append t x ∈ D')
    (hE : ∀ y, Fin.append z y ∈ E ↔ Fin.append t y ∈ E')
    (hV : ∀ x y, Fin.append (Fin.append z x) y ∈ V ↔ Fin.append (Fin.append t x) y ∈ W)
    (h : bijectiveMapRowValid sp sy D E V z) : bijectiveMapRowValid sq sy D' E' W t := by
  refine ⟨finiteMapRowValid_of_rows ht hD hV h.1,?_⟩
  intro y
  exact (hE y).symm.trans ((h.2 y).trans (exists_congr (fun x => hV x y)))

end IntegrationInACVF.Section6
