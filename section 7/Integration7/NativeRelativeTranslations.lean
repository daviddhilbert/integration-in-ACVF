module

public import Integration7.NativeVolumeDomains
public import IntegrationSection5.RelativelyUnary
public import Section4.Products

@[expose] public section

/-! An actual definable centre map independent of the active coordinate
gives an injective relatively unary translation onto its actual image. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.DefinableGeometry.Space.prod
  SpecialTransformations.Section4.realSpace SpecialTransformations.Milestone0.sortEval
  SpecialTransformations.Section4.vfSpace SpecialTransformations.Section4.rvSpace
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section5
open IntegrationInACVF.Section5

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {S : Set M} {n a : ℕ}

def relativeTranslationMap (A : DefSet (M := M) S n a) (i : Fin n)
    (c : Map A (PresentedSet.univ (SpecialTransformations.Section4.vfSpace 1) S)) :
    Map A (PresentedSet.univ (pointSpace n a) S) :=
  Map.comp (subtractMap i (PresentedSet.prod A (PresentedSet.univ (SpecialTransformations.Section4.vfSpace 1) S)))
    (Map.pair (Map.id A) c)

theorem relative_translation_map_value (A : DefSet (M := M) S n a) (i : Fin n)
    (c : Map A (PresentedSet.univ (SpecialTransformations.Section4.vfSpace 1) S)) (p : A) :
    (relativeTranslationMap A i c p).val = replace i p.val
      ((show VFType (M := M) from p.val.1 i)-(show VFType (M := M) from (c p).val 0)) := rfl

theorem relative_translation_erase (A : DefSet (M := M) S n a) (i : Fin n)
    (c : Map A (PresentedSet.univ (SpecialTransformations.Section4.vfSpace 1) S)) (p : A) :
    erase i (relativeTranslationMap A i c p).val = erase i p.val := by
  exact Prod.ext (Function.update_idem _ _ _) rfl

theorem relative_translation_unary_relative (A : DefSet (M := M) S n a) (i : Fin n)
    (c : Map A (PresentedSet.univ (SpecialTransformations.Section4.vfSpace 1) S)) :
    UnaryRelative (relativeTranslationMap A i c) i := by
  intro p j hj
  exact Function.update_of_ne hj _ _

theorem relative_translation_map_injective (A : DefSet (M := M) S n a) (i : Fin n)
    (c : Map A (PresentedSet.univ (SpecialTransformations.Section4.vfSpace 1) S))
    (hC : ∀ p q : A, erase i p.val = erase i q.val → (c p).val 0 = (c q).val 0) :
    Function.Injective (relativeTranslationMap A i c) := by
  intro p q h
  have he : erase i p.val = erase i q.val := (relative_translation_erase A i c p).symm.trans
    ((congrArg (fun z => erase i z.val) h).trans (relative_translation_erase A i c q))
  have hc := hC p q he
  have hAct := congrArg (fun z => z.val.1 i) h
  rw [relative_translation_map_value,relative_translation_map_value] at hAct
  simp only [replace,Function.update_self] at hAct
  rw [hc] at hAct
  apply Subtype.ext
  refine Prod.ext ?_ (congrArg (fun z => z.val.2) h)
  funext j
  by_cases hj : j = i
  · subst j
    have hh := congrArg (fun z : VFType (M := M) => z+(show VFType (M := M) from (c q).val 0)) hAct
    simpa only [sub_add_cancel] using hh
  · exact ((relative_translation_unary_relative A i c) p j hj).symm.trans
      ((congrArg (fun z => z.val.1 j) h).trans ((relative_translation_unary_relative A i c) q j hj))

def relativeTranslationImage (A : DefSet (M := M) S n a) (i : Fin n)
    (c : Map A (PresentedSet.univ (SpecialTransformations.Section4.vfSpace 1) S)) :
    DefSet (M := M) S n a := Map.image (relativeTranslationMap A i c)

def relativeTranslationToImage (A : DefSet (M := M) S n a) (i : Fin n)
    (c : Map A (PresentedSet.univ (SpecialTransformations.Section4.vfSpace 1) S)) :
    Map A (relativeTranslationImage A i c) := Map.toImage (relativeTranslationMap A i c)

theorem relative_translation_to_image_bijective (A : DefSet (M := M) S n a) (i : Fin n)
    (c : Map A (PresentedSet.univ (SpecialTransformations.Section4.vfSpace 1) S))
    (hC : ∀ p q : A, erase i p.val = erase i q.val → (c p).val 0 = (c q).val 0) :
    Function.Bijective (relativeTranslationToImage A i c) := by
  refine ⟨?_,?_⟩
  · intro p q h
    have he : (relativeTranslationMap A i c p).val = (relativeTranslationMap A i c q).val :=
      congrArg (fun z : relativeTranslationImage A i c => z.val) h
    exact relative_translation_map_injective A i c hC (Subtype.ext he)
  · rintro ⟨z,p,rfl⟩
    exact ⟨p,rfl⟩

end IntegrationInACVF.Section7
