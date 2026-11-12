import IntegrationSection6.TranslatedFibres
import Section5.Core

/-! Actual focus maps on one RV fibre are subtraction by one constant
centre. This identifies their whole image, including the centre itself. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.DefinableGeometry.Space.prod
  SpecialTransformations.Section4.realSpace SpecialTransformations.Milestone0.sortEval
  SpecialTransformations.Section4.vfSpace SpecialTransformations.Section4.rvSpace

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section5

namespace IntegrationInACVF.Section6

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {S : Set M} {n m : ℕ}
variable {A : DefSet (M := M) S n m} {j : Fin n} {k : Fin m}

theorem erase_replace (p : Point (M := M) n m) (j : Fin n) (a : VF (M := M)) :
    erase j (replace j p a) = erase j p := by
  simp only [erase,replace,Function.update_idem]

theorem replace_mem_pullback (hA : IsRVPullback (carrier A)) (p : A)
    (a : VF (M := M)) (ha : rv a = rv (p.val.1 j)) :
    replace j p.val a ∈ carrier A := by
  apply (isRVPullback_iff _).mp hA p.val p.property
  apply (sameRV_iff _ _).mpr
  refine ⟨?_,rfl⟩
  intro i
  by_cases hi : i = j
  · subst i; simpa [replace] using ha.symm
  · simp [replace,hi]

/-- Independence is used on the whole original RV fibre, not just at a
chosen field representative. -/
theorem fullFocus_eta_replace (D : Focus A j k)
    (hA : IsRVPullback (carrier A)) (hfull : carrier A ⊆ D.locus)
    (p : A) (a : VF (M := M)) (ha : rv a = rv (p.val.1 j)) :
    D.toFocusGeometry.eta (replace j p.val a) =
      replace j p.val (a - D.center p.val) := by
  have hq := replace_mem_pullback hA p a ha
  have hc := D.independent (replace j p.val a) ⟨hq,hfull hq⟩
    p.val ⟨p.property,hfull p.property⟩ (erase_replace p.val j a)
  rw [FocusGeometry.eta, if_pos (hfull hq)]
  simp only [replace,Function.update_self,Function.update_idem]
  rw [show D.center (Function.update p.val.1 j a,p.val.2) = D.center p.val from hc]

/-- The centre belongs to the original active RV class. -/
theorem fullFocus_center_nonzero (D : Focus A j k) (hfull : carrier A ⊆ D.locus)
    (p : A) (hp : p.val.1 j ≠ (0 : VF (M := M))) : D.center p.val ≠ 0 := by
  have hc := D.toFocusGeometry.center_sameRV p.val ⟨p.property,hfull p.property⟩
  intro hz
  have hrv : CanonicalRV.encodedRv (p.val.1 j) = 0 := by
    change rv (D.center p.val) = rv (p.val.1 j) at hc
    rw [hz] at hc
    exact hc.symm.trans RVOperations.rv_zero
  exact (RVOperations.rv_ne_zero _).mpr hp hrv

/-- The explicit quotient parameter produces every blowup fibre point.
All unmodified field coordinates and old RV labels are retained. -/
theorem fullFocus_fibre_surjective (D : Focus A j k)
    (hA : IsRVPullback (carrier A)) (hfull : carrier A ⊆ D.locus)
    (p : A) (hp : p.val.1 j ≠ (0 : VF (M := M)))
    (b : VF (M := M)) (s : CanonicalRV.RVSort M)
    (hbs : CanonicalRV.encodedRv b = s * CanonicalRV.encodedRv (p.val.1 j))
    (hs : RVOperations.absoluteHom s < 1) :
    ∃ a : A, erase j a.val = erase j p.val ∧
      D.toFocusGeometry.eta a.val = replace j p.val b := by
  have hc := D.toFocusGeometry.center_sameRV p.val ⟨p.property,hfull p.property⟩
  let c := D.center p.val
  have hc0 : c ≠ 0 := fullFocus_center_nonzero D hfull p hp
  let q : translatedFibre (CanonicalRV.encodedRv c) := ⟨(b,s),by
    constructor
    · change rv c = rv (p.val.1 j) at hc
      exact hbs.trans (congrArg (fun t => s*t) hc.symm)
    · exact hs⟩
  let a0 := (translatedFibreEquiv c hc0).symm q
  have ha0 : rv a0.val = rv (p.val.1 j) := a0.property.trans hc
  let a : A := ⟨replace j p.val a0.val,replace_mem_pullback hA p a0.val ha0⟩
  refine ⟨a,erase_replace _ _ _,?_⟩
  rw [fullFocus_eta_replace D hA hfull p a0.val ha0]
  change replace j p.val ((b+c)-c) = replace j p.val b
  rw [add_sub_cancel_right]

end IntegrationInACVF.Section6
