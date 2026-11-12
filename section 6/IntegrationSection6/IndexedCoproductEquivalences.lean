import IntegrationSection6.GammaGraphCoproducts
import IntegrationSection6.IndexedEquivalences
import Mathlib.Logic.Equiv.Sum

/-! Explicit label equivalences for indexed tagged coproducts. Indexed
sums distribute over the two native RV tags, with parameters retained in
each summand. No finiteness of the index set is required. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.DefinableGeometry.Space.prod
  SpecialTransformations.Section4.realSpace SpecialTransformations.Milestone0.sortEval
  SpecialTransformations.Section4.vfSpace SpecialTransformations.Section4.rvSpace
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
namespace IntegrationInACVF.Section6
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {p a b : ℕ}
local notation "N" => (@CanonicalStructure.normalize M sM)
local notation "hN" => (@CanonicalStructure.normalized_model M sM hM)

def graphCoprodEquiv (D : Set (Fin a → RV (M := M))) (E : Set (Fin b → RV (M := M))) :
    (D ⊕ E) ≃ graphCoprodDomain D E :=
  Equiv.ofBijective
    (Sum.elim (fun x => ⟨@rvLeftTag M N hN a b x.val,Or.inl ⟨x.val,x.property,rfl⟩⟩)
      (fun y => ⟨@rvRightTag M N hN b a y.val,Or.inr ⟨y.val,y.property,rfl⟩⟩)) (by
    constructor
    · intro x y hxy
      cases x with
      | inl x =>
        cases y with
        | inl y => exact congrArg Sum.inl (Subtype.ext (@rvLeftTag_injective M N hN a b _ _ (congrArg Subtype.val hxy)))
        | inr y => exact False.elim (@rvTag_disjoint M N hN a b x.val y.val (congrArg Subtype.val hxy))
      | inr x =>
        cases y with
        | inl y => exact False.elim (@rvTag_disjoint M N hN a b y.val x.val (congrArg Subtype.val hxy).symm)
        | inr y => exact congrArg Sum.inr (Subtype.ext (@rvRightTag_injective M N hN b a _ _ (congrArg Subtype.val hxy)))
    · rintro ⟨w,hw⟩
      rcases hw with ⟨x,hx,hw⟩ | ⟨y,hy,hw⟩
      · exact ⟨Sum.inl ⟨x,hx⟩,Subtype.ext hw⟩
      · exact ⟨Sum.inr ⟨y,hy⟩,Subtype.ext hw⟩)

def indexedCoprodEquiv (T : Set (Fin p → RV (M := M)))
    (D : (Fin p → RV (M := M)) → Set (Fin a → RV (M := M)))
    (E : (Fin p → RV (M := M)) → Set (Fin b → RV (M := M))) :
    indexedDomain T (fun t => graphCoprodDomain (D t) (E t)) ≃
      graphCoprodDomain (indexedDomain T D) (indexedDomain T E) :=
  (indexedSigmaEquiv T (fun t => graphCoprodDomain (D t) (E t))).trans
    ((Equiv.sigmaCongrRight (fun t : T => (graphCoprodEquiv (D t.val) (E t.val)).symm)).trans
      ((Equiv.sigmaSumDistrib (fun t : T => D t.val) (fun t : T => E t.val)).trans
        ((Equiv.sumCongr (indexedSigmaEquiv T D).symm (indexedSigmaEquiv T E).symm).trans
          (graphCoprodEquiv (indexedDomain T D) (indexedDomain T E)))))

def indexedCoprodLeft (T : Set (Fin p → RV (M := M)))
    (D : (Fin p → RV (M := M)) → Set (Fin a → RV (M := M)))
    (E : (Fin p → RV (M := M)) → Set (Fin b → RV (M := M))) (t : T) (x : D t.val) :
    indexedDomain T (fun t => graphCoprodDomain (D t) (E t)) :=
  (indexedSigmaEquiv T (fun t => graphCoprodDomain (D t) (E t))).symm
    ⟨t,graphCoprodEquiv (D t.val) (E t.val) (.inl x)⟩

def indexedCoprodRight (T : Set (Fin p → RV (M := M)))
    (D : (Fin p → RV (M := M)) → Set (Fin a → RV (M := M)))
    (E : (Fin p → RV (M := M)) → Set (Fin b → RV (M := M))) (t : T) (y : E t.val) :
    indexedDomain T (fun t => graphCoprodDomain (D t) (E t)) :=
  (indexedSigmaEquiv T (fun t => graphCoprodDomain (D t) (E t))).symm
    ⟨t,graphCoprodEquiv (D t.val) (E t.val) (.inr y)⟩

theorem indexedCoprodEquiv_left (T : Set (Fin p → RV (M := M)))
    (D : (Fin p → RV (M := M)) → Set (Fin a → RV (M := M)))
    (E : (Fin p → RV (M := M)) → Set (Fin b → RV (M := M))) (t : T) (x : D t.val) :
    (indexedCoprodEquiv T D E (indexedCoprodLeft T D E t x)).val =
      @rvLeftTag M N hN (p+a) (p+b) (Fin.append t.val x.val) := by
  unfold indexedCoprodEquiv indexedCoprodLeft
  simp only [Equiv.trans_apply,Equiv.apply_symm_apply]
  simp only [Equiv.sigmaCongrRight_apply,Equiv.symm_apply_apply]
  rfl

theorem indexedCoprodEquiv_right (T : Set (Fin p → RV (M := M)))
    (D : (Fin p → RV (M := M)) → Set (Fin a → RV (M := M)))
    (E : (Fin p → RV (M := M)) → Set (Fin b → RV (M := M))) (t : T) (y : E t.val) :
    (indexedCoprodEquiv T D E (indexedCoprodRight T D E t y)).val =
      @rvRightTag M N hN (p+b) (p+a) (Fin.append t.val y.val) := by
  unfold indexedCoprodEquiv indexedCoprodRight
  simp only [Equiv.trans_apply,Equiv.apply_symm_apply]
  simp only [Equiv.sigmaCongrRight_apply,Equiv.symm_apply_apply]
  rfl

theorem indexedCoprod_cases (T : Set (Fin p → RV (M := M)))
    (D : (Fin p → RV (M := M)) → Set (Fin a → RV (M := M)))
    (E : (Fin p → RV (M := M)) → Set (Fin b → RV (M := M)))
    (w : indexedDomain T (fun t => graphCoprodDomain (D t) (E t))) :
    (∃ t x, w = indexedCoprodLeft T D E t x) ∨ ∃ t y, w = indexedCoprodRight T D E t y := by
  obtain ⟨⟨t,z⟩,rfl⟩ := (indexedSigmaEquiv T (fun t => graphCoprodDomain (D t) (E t))).symm.surjective w
  obtain ⟨s,rfl⟩ := (graphCoprodEquiv (D t.val) (E t.val)).surjective z
  cases s with
  | inl x => exact Or.inl ⟨t,x,rfl⟩
  | inr y => exact Or.inr ⟨t,y,rfl⟩

end IntegrationInACVF.Section6
