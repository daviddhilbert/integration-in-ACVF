import IntegrationSection6.GammaParameterRecoding

/-! Raw formula rows are exactly their properly typed RV tuple rows.
These bridges expose improper tuples as false using full Gamma properness. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
namespace IntegrationInACVF.Section6
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {p q a b : ℕ} {sp : Fin p → SortTag} {sq : Fin q → SortTag}

theorem GammaDomainFormula.row_typed_iff (D : GammaDomainFormula B p a sp) (z : Fin p → M) (x : Fin a → M) :
    Fin.append z x ∈ D.val ↔ ∃ u : Fin a → RV (M := M),
      Fin.append z (fun j => (u j).val) ∈ D.val ∧ (fun j => (u j).val) = x := by
  constructor
  · intro hx
    have hxs (j : Fin a) : iRV (x j) := by
      simpa only [Fin.append_right,sortEval,iRV] using D.property.proper _ hx (Fin.natAdd p j)
    exact ⟨fun j => ⟨x j,hxs j⟩,hx,rfl⟩
  · rintro ⟨u,hu,rfl⟩
    exact hu

theorem GammaRelationFormula.row_typed_iff (R : GammaRelationFormula B p a b sp)
    (z : Fin p → M) (x : Fin a → M) (y : Fin b → M) :
    Fin.append (Fin.append z x) y ∈ R.val ↔
      ∃ u : Fin a → RV (M := M), ∃ v : Fin b → RV (M := M),
        Fin.append (Fin.append z (fun j => (u j).val)) (fun j => (v j).val) ∈ R.val ∧
        (fun j => (u j).val) = x ∧ (fun j => (v j).val) = y := by
  constructor
  · intro hxy
    have hxs (j : Fin a) : iRV (x j) := by
      simpa only [Fin.append_left,Fin.append_right,sortEval,iRV] using
        R.property.proper _ hxy (Fin.castAdd b (Fin.natAdd p j))
    have hys (j : Fin b) : iRV (y j) := by
      simpa only [Fin.append_right,sortEval,iRV] using R.property.proper _ hxy (Fin.natAdd (p+a) j)
    exact ⟨fun j => ⟨x j,hxs j⟩,fun j => ⟨y j,hys j⟩,hxy,rfl,rfl⟩
  · rintro ⟨u,v,hxy,rfl,rfl⟩
    exact hxy

theorem gammaDomainRows_agree_of_typed (D : GammaDomainFormula B p a sp)
    (E : GammaDomainFormula B q a sq) (z : Fin p → M) (t : Fin q → M)
    (h : ∀ x : Fin a → RV (M := M),
      Fin.append z (fun j => (x j).val) ∈ D.val ↔ Fin.append t (fun j => (x j).val) ∈ E.val) :
    ∀ x : Fin a → M, Fin.append z x ∈ D.val ↔ Fin.append t x ∈ E.val := by
  intro x
  rw [GammaDomainFormula.row_typed_iff,GammaDomainFormula.row_typed_iff]
  exact exists_congr (fun u => and_congr (h u) Iff.rfl)

theorem gammaRelationRows_agree_of_typed (R : GammaRelationFormula B p a b sp)
    (S : GammaRelationFormula B q a b sq) (z : Fin p → M) (t : Fin q → M)
    (h : ∀ (x : Fin a → RV (M := M)) (y : Fin b → RV (M := M)),
      Fin.append (Fin.append z (fun j => (x j).val)) (fun j => (y j).val) ∈ R.val ↔
      Fin.append (Fin.append t (fun j => (x j).val)) (fun j => (y j).val) ∈ S.val) :
    ∀ x y, Fin.append (Fin.append z x) y ∈ R.val ↔ Fin.append (Fin.append t x) y ∈ S.val := by
  intro x y
  rw [GammaRelationFormula.row_typed_iff,GammaRelationFormula.row_typed_iff]
  exact exists_congr (fun u => exists_congr (fun v => and_congr (h u v) Iff.rfl))

end IntegrationInACVF.Section6
