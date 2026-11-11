import IntegrationSection4.RelativeGammaPreparation
import IntegrationSection4.DefinableDescent

/-! Uniform positioning functions obtained by descending the inverse
vertical displacement. Every centre is an actual VF value and every
parameter remains in the original base of the ambient map. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false

set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.DefinableGeometry.Space.prod
  SpecialTransformations.Section4.realSpace SpecialTransformations.Milestone0.sortEval
  SpecialTransformations.Section4.vfSpace SpecialTransformations.Section4.rvSpace

open Set Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section5

namespace IntegrationInACVF.Section4.VerticalOffsets

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {S : Set M} {n m l : ℕ}
variable {A : DefSet (M := M) S (n+1) m} {B : DefSet (M := M) S (n+1) l}

def headMap (A : DefSet (M := M) S (n+1) m) :
    Map A (PresentedSet.univ (SpecialTransformations.Section4.vfSpace 1) S) :=
  Map.ofCodes A (fun p => ![vfAt p 0]) (fun z _ => z (.inl 0))
    (fun _ => rawProj S (.inl 0 : Fin (n+1) ⊕ Fin m))
    (fun c _ => c.property.1 0) (by
      intro c
      funext i
      fin_cases i
      apply Subtype.ext
      rfl)

def keyMap (B : DefSet (M := M) S (n+1) l) := dropHeadMap (id : Fin l → Fin l) B

def keyImage (B : DefSet (M := M) S (n+1) l) := Map.image (keyMap B)

def toKey (B : DefSet (M := M) S (n+1) l) : B → keyImage B := Map.toImage (keyMap B)

def displacementMap (T : RelativeBijection A B) :
    Map B (PresentedSet.univ (SpecialTransformations.Section4.vfSpace 1) S) :=
  Map.comp (headMap _) (Map.comp (subtractMap 0 _) (Map.pair T.inverseMap (headMap B)))

theorem displacement_apply (T : RelativeBijection A B) (b : B) :
    (displacementMap T b).val 0 = vfAt (T.inverseMap b).val 0-vfAt b.val 0 := rfl

theorem displacement_constant (T : RelativeBijection A B) (a b : B)
    (he : keyMap B a = keyMap B b) : displacementMap T a = displacementMap T b := by
  have he' : dropHead id a.val = dropHead id b.val := congrArg Subtype.val he
  have ht : TailEq a.val b.val := fun i => congrArg (fun p : Point (M := M) n l => vfAt p i) he'
  have hl : a.val.2 = b.val.2 := congrArg (fun p : Point (M := M) n l => p.2) he'
  have hd := T.inverse_affine a b ht hl
  apply Subtype.ext
  funext i
  fin_cases i
  change (displacementMap T a).val 0 = (displacementMap T b).val 0
  rw [displacement_apply,displacement_apply]
  linear_combination hd

def offsetMap (T : RelativeBijection A B) :
    Map (keyImage B) (PresentedSet.univ (SpecialTransformations.Section4.vfSpace 1) S) :=
  @DefinableDescent.descendMap LRV M (CanonicalStructure.normalize (M := M))
    _ _ _ S _ _ _ (keyMap B) (displacementMap T) (displacement_constant T)

def offsetValue (T : RelativeBijection A B) (u : keyImage B) : VF (M := M) := (offsetMap T u).val 0

theorem offsetValue_eq (T : RelativeBijection A B) (b : B) :
    offsetValue T (toKey B b) = vfAt (T.inverseMap b).val 0-vfAt b.val 0 := by
  have h := @DefinableDescent.descendMap_spec LRV M (CanonicalStructure.normalize (M := M))
    _ _ _ S _ _ _ (keyMap B) (displacementMap T) (displacement_constant T) b
  exact (congrArg (fun p => p.val 0) h).trans (displacement_apply T b)

def headBody (T : RelativeBijection A B) (b : B) : Set (VF (M := M)) :=
  (fun p : Point (M := M) (n+1) m => vfAt p 0) '' T.inverseSlice b

/-- The complete inverse vertical piece is an RV fibre translated by its
uniform definable positioning value, including the absorbing zero fibre. -/
theorem inverse_head_translate (T : RelativeBijection A B)
    (hB : HeadSaturated (carrier B)) (b : B) :
    headBody T b = (fun x => x+offsetValue T (toKey B b)) ''
      {x : VF (M := M) | rv x = rv (vfAt b.val 0)} := by
  ext y
  constructor
  · rintro ⟨p,⟨a,ha,he,ht⟩,hpy⟩
    have hd := T.inverse_affine (T.toMap a) b ht (((sameRV_iff _ _).mp he).2)
    rw [T.inverse_apply] at hd
    refine ⟨vfAt (T.toMap a).val 0,((sameRV_iff _ _).mp he).1 0,?_⟩
    rw [offsetValue_eq]
    have hay : vfAt a.val 0 = y := (congrArg (fun p : Point (M := M) (n+1) m => vfAt p 0) ha).trans hpy
    rw [hay] at hd
    linear_combination -hd
  · rintro ⟨x,hx,rfl⟩
    let c : B := ⟨replace 0 b.val x,hB b.val b.property x hx⟩
    have hcRV : SameRV c.val b.val := (sameRV_replace 0 b.val x hx).symm
    have hcTail : TailEq c.val b.val := by intro i; simp [c,replace,vfAt,Fin.succ_ne_zero]
    have hd := T.inverse_affine c b hcTail (((sameRV_iff _ _).mp hcRV).2)
    refine ⟨(T.inverseMap c).val,⟨T.inverseMap c,rfl,?_,?_⟩,?_⟩
    · simpa only [T.apply_inverse] using hcRV
    · simpa only [T.apply_inverse] using hcTail
    · rw [offsetValue_eq]
      change vfAt (T.inverseMap c).val 0 = x+(vfAt (T.inverseMap b).val 0-vfAt b.val 0)
      change vfAt (T.inverseMap c).val 0-vfAt (T.inverseMap b).val 0 = x-vfAt b.val 0 at hd
      linear_combination hd

end IntegrationInACVF.Section4.VerticalOffsets
