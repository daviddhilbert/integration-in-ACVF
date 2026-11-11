import IntegrationSection5.RelativeFibreBijection
import Section5.VerticalConstruction

/-! Original RV labels are a fixed suffix throughout actual special maps.
This gives a uniform label projection even when fibre witnesses vary. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.DefinableGeometry.Space.prod
  SpecialTransformations.Section4.realSpace SpecialTransformations.Milestone0.sortEval
  SpecialTransformations.Section4.vfSpace SpecialTransformations.Section4.rvSpace
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section5
namespace IntegrationInACVF.Section5
variable {M : Type} [sM : LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {S : Set M} {n m l : ℕ} {A : DefSet (M := M) S n m} {B : DefSet (M := M) S n l}

theorem special_chain_rvArity_le (T : Chain S n A B) : m ≤ l := by
  induction T with
  | nil A => exact le_rfl
  | cons p tail ih => cases p <;> omega

def suffixIndex (h : m ≤ l) (j : Fin m) : Fin l := ⟨l-m+j.val,by omega⟩

theorem special_chain_labelIndex (T : Chain S n A B) (j : Fin m) :
    T.labelIndex j = suffixIndex (special_chain_rvArity_le T) j := by
  apply Fin.ext
  induction T with
  | nil A => simp [Chain.labelIndex,suffixIndex]
  | @cons a b c A B C p tail ih =>
    have hle := special_chain_rvArity_le tail
    cases p with
    | canonical A =>
      change (tail.labelIndex (Fin.natAdd n j)).val = c-a+j.val
      rw [ih]
      change c-(n+a)+(n+j.val) = c-a+j.val
      omega
    | centripetal D => exact ih j

theorem special_oldLabels (T : SpecialBijection A B) (a : A) (j : Fin m) :
    (T.toMap a).val.2 (suffixIndex (special_chain_rvArity_le T.chain) j) = a.val.2 j := by
  rw [← special_chain_labelIndex T.chain]
  exact T.chain.labelIndex_apply a j

theorem specialRelative_rvArity_le {f : Map A B} {i : Fin n} (hf : SpecialRelative f i) : m ≤ l := by
  obtain ⟨hi,hT⟩ := hf
  obtain ⟨T,_⟩ := hT (fun _ => 0)
  exact special_chain_rvArity_le T.chain

theorem specialRelative_oldLabels {f : Map A B} {i : Fin n} (hf : SpecialRelative f i)
    (a : A) (j : Fin m) :
    (f a).val.2 (suffixIndex (specialRelative_rvArity_le hf) j) = a.val.2 j := by
  obtain ⟨hi,hT⟩ := hf
  let u := a.val.1
  have hRestore : coordinateInsert i u (coordinateProject i a.val) = a.val :=
    coordinateInsert_project i u a.val (fun _ _ => rfl)
  let p : coordinateFibre A i u := ⟨coordinateProject i a.val,by
    change coordinateInsert i u (coordinateProject i a.val) ∈ carrier A
    rw [hRestore]
    exact a.property⟩
  obtain ⟨T,hT⟩ := hT u
  have h := special_oldLabels T p j
  rw [hT p,coordinateFibreMap_apply] at h
  have hax : (⟨coordinateInsert i u p.val,p.property⟩ : A) = a := Subtype.ext hRestore
  rw [hax] at h
  exact h

end IntegrationInACVF.Section5
