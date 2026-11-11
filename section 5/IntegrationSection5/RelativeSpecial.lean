import IntegrationSection5.FibreFocusImage

/-! Definition 5.4 with actual fibrewise special bijections. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section5
namespace IntegrationInACVF.Section5
variable {M : Type} [sM : LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {S : Set M} {n m l : ℕ}
variable {A : DefSet (M := M) S n m} {B : DefSet (M := M) S n l}

/-- Every other VF coordinate is fixed and each actual coordinate-fibre map
is represented by a special bijection over the base naming those coordinates. -/
def SpecialRelative (f : Map A B) (i : Fin n) : Prop :=
  ∃ hi : UnaryRelative f i, ∀ u : Fin n → VF (M := M),
    ∃ T : SpecialBijection (coordinateFibre A i u) (coordinateFibre B i u),
      ∀ p, T.toMap p = coordinateFibreMap f i hi u p

def RelativelySpecial (f : Map A B) : Prop := ∃ i, SpecialRelative f i

theorem specialRelative_unaryRelative {f : Map A B} {i : Fin n} (h : SpecialRelative f i) :
    UnaryRelative f i := h.choose

theorem specialRelative_id (A : DefSet (M := M) S n m) (i : Fin n) :
    SpecialRelative (Map.id A) i := by
  refine ⟨unaryRelative_id i,fun u => ⟨SpecialBijection.refl _,?_⟩⟩
  intro p
  apply Subtype.ext
  exact (coordinateProject_insert i u p.val).symm

theorem centripetal_unaryRelative {i : Fin n} {k : Fin m} (D : Focus A i k) :
    UnaryRelative (SpecialBijection.centripetal D).toMap i := by
  intro a j hj
  exact D.toFocusGeometry.eta_other a.val j hj

theorem centripetal_specialRelative {i : Fin n} {k : Fin m} (D : Focus A i k) :
    SpecialRelative (SpecialBijection.centripetal D).toMap i := by
  refine ⟨centripetal_unaryRelative D,fun u => ⟨fibreCentripetal D u,?_⟩⟩
  intro p
  apply Subtype.ext
  apply coordinateInsert_injective i u
  rw [fibreCentripetal_apply,coordinateFibreMap_insert]
  rfl

theorem centripetal_relativelySpecial {i : Fin n} {k : Fin m} (D : Focus A i k) :
    RelativelySpecial (SpecialBijection.centripetal D).toMap := ⟨i,centripetal_specialRelative D⟩

end IntegrationInACVF.Section5
