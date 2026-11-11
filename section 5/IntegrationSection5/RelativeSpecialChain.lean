import IntegrationSection5.CoordinateCanonicalFibre
import Mathlib.Data.List.OfFn
import Mathlib.Data.List.FinRange

/-! Finite compositions retaining the actual relatively special factors. -/
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
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

inductive RelativeSpecialChain (S : Set M) (n : ℕ) : {m l : ℕ} →
    DefSet (M := M) S n m → DefSet (M := M) S n l → Type where
  | nil {m : ℕ} (A : DefSet (M := M) S n m) : RelativeSpecialChain S n A A
  | cons {m l k : ℕ} {A : DefSet (M := M) S n m} {B : DefSet (M := M) S n l}
      {C : DefSet (M := M) S n k} (i : Fin n) (f : Map A B)
      (bijective : Function.Bijective f) (special : SpecialRelative f i)
      (tail : RelativeSpecialChain S n B C) : RelativeSpecialChain S n A C

namespace RelativeSpecialChain
variable {S : Set M} {n m l k : ℕ}
variable {A : DefSet (M := M) S n m} {B : DefSet (M := M) S n l} {C : DefSet (M := M) S n k}

def toMap {a b : ℕ} {X : DefSet (M := M) S n a} {Y : DefSet (M := M) S n b} :
    RelativeSpecialChain S n X Y → Map X Y
  | .nil A => Map.id A
  | .cons _ f _ _ tail => Map.comp tail.toMap f

theorem bijective (t : RelativeSpecialChain S n A B) : Function.Bijective t.toMap := by
  induction t with
  | nil A => exact Function.bijective_id
  | cons i f hf hi tail ih => exact ih.comp hf

def append {a b c : ℕ} {X : DefSet (M := M) S n a} {Y : DefSet (M := M) S n b}
    {Z : DefSet (M := M) S n c} :
    RelativeSpecialChain S n X Y → RelativeSpecialChain S n Y Z → RelativeSpecialChain S n X Z
  | .nil _,u => u
  | .cons i f hf hi tail,u => .cons i f hf hi (tail.append u)

theorem append_toMap (t : RelativeSpecialChain S n A B) (u : RelativeSpecialChain S n B C) :
    (t.append u).toMap = Map.comp u.toMap t.toMap := by
  induction t with
  | nil A => apply Map.ext; intro a; rfl
  | cons i f hf hi tail ih =>
    apply Map.ext
    intro a
    change (tail.append u).toMap (f a) = _
    rw [ih]
    rfl

def castTarget {C : DefSet (M := M) S n l} (t : RelativeSpecialChain S n A B) (h : B = C) :
    RelativeSpecialChain S n A C := h ▸ t

theorem castTarget_val {C : DefSet (M := M) S n l} (t : RelativeSpecialChain S n A B)
    (h : B = C) (p : A) : ((t.castTarget h).toMap p).val = (t.toMap p).val := by
  subst C
  rfl
end RelativeSpecialChain

variable {S : Set M} {n m : ℕ}

abbrev pointRVList {a b : ℕ} (p : Point (M := M) a b) : List (RV (M := M)) := List.ofFn p.2

/-- Descending coordinates prepend their RV values, leaving the desired
ascending coordinate order after all factors have been applied. -/
theorem coordinateCanonical_sequence (A : DefSet (M := M) S n m) (is : List (Fin n)) :
    ∃ l, ∃ B : DefSet (M := M) S n l, ∃ t : RelativeSpecialChain S n A B,
      l = is.length + m ∧ ∀ a : A, (t.toMap a).val.1 = a.val.1 ∧
        pointRVList (t.toMap a).val = is.reverse.map (fun i => @rv M sM hM (vfAt a.val i)) ++ pointRVList a.val := by
  induction is generalizing m with
  | nil =>
    refine ⟨m,A,.nil A,by simp,?_⟩
    intro a
    exact ⟨rfl,rfl⟩
  | cons i is ih =>
    obtain ⟨l,B,t,hl,ht⟩ := ih (coordinateCanonicalImage A i)
    refine ⟨l,B,.cons i (coordinateCanonicalBijection A i)
      (coordinateCanonicalBijection_bijective A i) (coordinateCanonical_specialRelative A i) t,by simp only [List.length_cons]; omega,?_⟩
    intro a
    obtain ⟨hv,hr⟩ := ht (coordinateCanonicalBijection A i a)
    refine ⟨hv,?_⟩
    change pointRVList (t.toMap (coordinateCanonicalBijection A i a)).val = _
    rw [hr]
    change is.reverse.map (fun j => @rv M sM hM (vfAt a.val j)) ++
      List.ofFn (Fin.append (fun _ : Fin 1 => @rv M sM hM (vfAt a.val i)) a.val.2) = _
    simp [pointRVList,List.reverse_cons,List.map_append,List.ofFn_fin_append,List.append_assoc]

end IntegrationInACVF.Section5
