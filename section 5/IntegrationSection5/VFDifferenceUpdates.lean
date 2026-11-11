import IntegrationSection5.UnaryFactorizations
import Section5.TransformGeometry

/-! Actual definable one-coordinate subtraction updates and their inverses. -/
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
variable {S : Set M} {n m : ℕ}

def vfDifferenceUpdate (i a b : Fin n) (q : Point (M := M) n m) : Point (M := M) n m :=
  replace i q (vfAt q a - vfAt q b)

def vfDifferenceMap (S : Set M) (m : ℕ) (i a b : Fin n) :
    Map (PresentedSet.univ (pointSpace (M := M) n m) S)
      (PresentedSet.univ (pointSpace n m) S) :=
  Map.ofCodes _ (vfDifferenceUpdate i a b)
    (fun z => Sum.elim (fun k => if k = i then subCode (z (.inl a)) (z (.inl b)) else z (.inl k))
      (fun k => z (.inr k)))
    (by
      intro k
      cases k with
      | inl k =>
        by_cases hk : k = i
        · simpa [hk] using subCode_definable S (.inl a : Fin n ⊕ Fin m) (.inl b)
        · simpa [hk] using rawProj S (.inl k : Fin n ⊕ Fin m)
      | inr k => exact rawProj S (.inr k : Fin n ⊕ Fin m))
    (by
      intro c
      refine ⟨?_,c.property.2⟩
      intro k
      by_cases hk : k = i
      · simp only [Function.comp_apply,Sum.elim_inl,if_pos hk]
        let x : VF (M := M) := ⟨c.val (.inl a),c.property.1 a⟩
        let y : VF (M := M) := ⟨c.val (.inl b),c.property.1 b⟩
        change iVF (subCode x.val y.val)
        rw [subCode_eq]
        exact (x-y).property
      · simpa only [Function.comp_apply,Sum.elim_inl,if_neg hk] using c.property.1 k)
    (by
      intro c
      refine Prod.ext ?_ rfl
      funext k
      apply Subtype.ext
      by_cases hk : k = i
      · subst k
        simpa [vfDifferenceUpdate,replace,vfAt] using
          subCode_eq (⟨c.val (.inl a),c.property.1 a⟩ : VF (M := M))
            (⟨c.val (.inl b),c.property.1 b⟩ : VF (M := M))
      · simp [vfDifferenceUpdate,replace,vfAt,hk])

theorem vfDifferenceMap_apply (S : Set M) (m : ℕ) (i a b : Fin n)
    (q : PresentedSet.univ (pointSpace (M := M) n m) S) :
    (vfDifferenceMap S m i a b q).val = vfDifferenceUpdate i a b q.val := rfl

theorem vfDifferenceMap_unary (S : Set M) (m : ℕ) (i a b : Fin n) :
    UnaryRelative (vfDifferenceMap (M := M) S m i a b) i := by
  intro q k hk
  change (Function.update q.val.1 i _ k) = _
  exact Function.update_of_ne hk _ _

theorem vfDifference_shear_inverse (i j : Fin n) (hij : i ≠ j) (q : Point (M := M) n m) :
    vfDifferenceUpdate i i j (replace i q (vfAt q i + vfAt q j)) = q := by
  refine Prod.ext ?_ rfl
  funext k
  by_cases hk : k = i
  · subst k
    simp [vfDifferenceUpdate,replace,vfAt,Ne.symm hij]
  · simp [vfDifferenceUpdate,replace,hk]

theorem vfDifference_shear_leftInverse (i j : Fin n) (hij : i ≠ j) (q : Point (M := M) n m) :
    replace i (vfDifferenceUpdate i i j q)
      (vfAt (vfDifferenceUpdate i i j q) i + vfAt (vfDifferenceUpdate i i j q) j) = q := by
  refine Prod.ext ?_ rfl
  funext k
  by_cases hk : k = i
  · subst k
    simp [vfDifferenceUpdate,replace,vfAt,Ne.symm hij]
  · simp [vfDifferenceUpdate,replace,hk]

theorem vfDifferenceMap_shear_bijective (S : Set M) (m : ℕ) (i j : Fin n) (hij : i ≠ j) :
    Function.Bijective (vfDifferenceMap (M := M) S m i i j) := by
  let inv (q : PresentedSet.univ (pointSpace (M := M) n m) S) :
      PresentedSet.univ (pointSpace (M := M) n m) S :=
    ⟨replace i q.val (vfAt q.val i + vfAt q.val j),Set.mem_univ _⟩
  apply Function.bijective_iff_has_inverse.mpr
  refine ⟨inv,?_,?_⟩
  · intro q
    exact Subtype.ext (vfDifference_shear_leftInverse i j hij q.val)
  · intro q
    exact Subtype.ext (vfDifference_shear_inverse i j hij q.val)

theorem vfDifference_reflection_involutive (i j : Fin n) (hij : i ≠ j) :
    Function.Involutive (vfDifferenceUpdate (M := M) (m := m) j i j) := by
  intro q
  refine Prod.ext ?_ rfl
  funext k
  by_cases hk : k = j
  · subst k
    simp [vfDifferenceUpdate,replace,vfAt,hij]
  · simp [vfDifferenceUpdate,replace,hk]

theorem vfDifferenceMap_reflection_bijective (S : Set M) (m : ℕ) (i j : Fin n) (hij : i ≠ j) :
    Function.Bijective (vfDifferenceMap (M := M) S m j i j) := by
  apply Function.Involutive.bijective
  intro q
  exact Subtype.ext (vfDifference_reflection_involutive i j hij q.val)

end IntegrationInACVF.Section5
