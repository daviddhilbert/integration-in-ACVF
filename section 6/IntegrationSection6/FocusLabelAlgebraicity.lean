import IntegrationSection6.FocusCenterAlgebraicity
import IntegrationSection6.SortedParameterElimination
import IntegrationSection6.ActualRVFibreDefinability
import Section3.RVOperations
import Section3.SmallFiniteParameters

/-! Algebraicity of the active RV coordinate of an RV-pullback carrying
a full-locus focus. The active VF representative is absent from the base. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.DefinableGeometry.Space.prod
  SpecialTransformations.Section4.realSpace SpecialTransformations.Milestone0.sortEval
  SpecialTransformations.Section4.vfSpace SpecialTransformations.Section4.rvSpace

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section5 SpecialTransformations.Section3

namespace IntegrationInACVF.Section6

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {S : Set M} {n m : ℕ}

/-- Full-locus focus data force exactly the algebraic dependence used in
Definition 6.1, in the actual original structure. -/
theorem fullFocus_label_algebraic
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (hsmall : Cardinal.mk S < κ) {A : DefSet (M := M) S n m}
    {j : Fin n} {k : Fin m} (D : Focus A j k)
    (hA : IsRVPullback (carrier A)) (hfull : carrier A ⊆ D.locus)
    (p : A) :
    AlgebraicAt (S ∪ {b | ∃ i : Fin n, i ≠ j ∧ (rv (p.val.1 i)).val = b})
      .rv (rv (p.val.1 j)).val := by
  let t : Fin n → CanonicalRV.RVSort M := fun i => rv ((erase j p.val).1 i)
  have hd : AlgebraicAt (S ∪ Set.range (SpecialTransformations.Section4.rvValues t))
      .rv (rv (p.val.1 j)).val := by
    apply corollary_3_2_vf hκ hs S (SpecialTransformations.Section4.rvValues t)
      (small_union_range hκ S hsmall _) (tupleRVFibre (SpecialTransformations.Section4.rvValues t))
      _ .rv (actualRVFibre_definable S t)
      (SpecialTransformations.Section4.rvTupleFibre_nonempty t) (Set.Subset.refl _)
    intro z hz
    let zVF : Fin n → VF (M := M) := fun i => ⟨z i, (hz i).1⟩
    have hzrv (i : Fin n) : rv (zVF i) = t i := Subtype.ext (hz i).2
    have hzj : zVF j = 0 := by
      apply (CanonicalRV.encodedRv_zero_iff (zVF j)).mp
      have htj : t j = rv (0 : VF (M := M)) := by simp [t,erase,replace]
      have he : rv (zVF j) = 0 := (hzrv j).trans (htj.trans RVOperations.rv_zero)
      exact (congrArg Subtype.val he).trans RVOperations.zero_val
    let q : Point (M := M) n m := (Function.update zVF j (p.val.1 j), p.val.2)
    have hsame : SameRV p.val q := by
      apply (sameRV_iff _ _).mpr
      refine ⟨?_, rfl⟩
      intro i
      by_cases hi : i = j
      · subst i; simp [q]
      · have he := hzrv i
        simpa [q, t, erase, replace, hi] using he.symm
    have hqA : q ∈ carrier A := (isRVPullback_iff _).mp hA p.val p.property q hsame
    let a : D.active := ⟨q, hqA, hfull hqA⟩
    have he : (erase j q).1 = zVF := by
      funext i
      by_cases hi : i = j
      · subst i; simp [erase, replace, q, hzj]
      · simp [erase, replace, q, hi]
    have halg := center_algebraic_erased D a
    have hrv := D.toFocusGeometry.center_sameRV q a.property
    change rv (D.center q) = rv (q.1 j) at hrv
    have hqj : q.1 j = p.val.1 j := by simp [q]
    rw [hqj] at hrv
    rw [congrArg Subtype.val hrv] at halg
    change AlgebraicAt (S ∪ Set.range (fun i => ((erase j q).1 i).val)) .rv _ at halg
    rw [he] at halg
    exact halg
  apply algebraicAt_eliminate_sorted_parameters hd
  intro b hb τ hbτ
  rcases hb with hb | ⟨i, rfl⟩
  · exact (definableClosureAt_of_mem (A := S ∪ {b | ∃ i : Fin n, i ≠ j ∧ (rv (p.val.1 i)).val = b}) (σ := τ) (x := b) (Or.inl hb) hbτ).algebraic
  · by_cases hi : i = j
    · subst i
      have htj : t j = rv (0 : VF (M := M)) := by simp [t, erase, replace]
      change sortEval τ (t j).val at hbτ
      change AlgebraicAt (S ∪ {b | ∃ i : Fin n, i ≠ j ∧ (rv (p.val.1 i)).val = b}) τ (t j).val
      rw [htj] at hbτ ⊢
      have hτ : τ = .rv := CanonicalStructure.sort_unique hM hbτ (rv (0 : VF (M := M))).property
      subst τ
      apply (SpecialTransformations.Section4.algebraicAt_rv_of_vf (0 : VF (M := M)))
      exact (definableClosureAt_function_symbol _ Fn.vfZero Fin.elim0
        (fun i => i.elim0) (fun i => i.elim0)).algebraic
    · have hti : t i = rv (p.val.1 i) := by simp [t, erase, replace, hi]
      exact (definableClosureAt_of_mem (A := S ∪ {b | ∃ i : Fin n, i ≠ j ∧ (rv (p.val.1 i)).val = b})
        (σ := τ) (x := (t i).val)
        (Or.inr ⟨i, hi, congrArg Subtype.val hti.symm⟩) hbτ).algebraic

end IntegrationInACVF.Section6
