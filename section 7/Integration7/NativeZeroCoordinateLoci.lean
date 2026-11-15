import Integration7.GammaMixedCoordinatePredicates
import Section5.RootConstruction

/-! Zero-coordinate loci are definable without naming VF zero as a
parameter. An actual real-definable erasure map exhibits the locus. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.DefinableGeometry.Space.prod
  SpecialTransformations.Section4.realSpace SpecialTransformations.Milestone0.sortEval
  SpecialTransformations.Section4.vfSpace SpecialTransformations.Section4.rvSpace
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section5

namespace IntegrationInACVF.Section7
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {G : Base (M := M)} {S : Set M} {n m : ℕ}

def nativeEraseMap (A : DefSet (M := M) S n m) (i : Fin n) :
    Map A (PresentedSet.univ (pointSpace n m) S) :=
  Map.ofCodes A (@erase M sM hM n m i)
    (fun z => Sum.elim (fun j => if j=i then @iVFZero M sM else z (.inl j)) (fun j => z (.inr j)))
    (by
      intro j
      cases j with
      | inl j =>
        by_cases hj : j=i
        · simpa only [hj,ite_true,Sum.elim_inl] using (zeroCode_definable (M := M) (sM := sM) (α := Fin n ⊕ Fin m) S)
        · simpa only [hj,ite_false,Sum.elim_inl] using (rawProj S (.inl j : Fin n ⊕ Fin m))
      | inr j => exact rawProj S (.inr j : Fin n ⊕ Fin m))
    (by
      intro c
      refine ⟨?_,c.property.2⟩
      intro j
      by_cases hj : j=i
      · simpa only [hj,ite_true,Function.comp_apply,Sum.elim_inl,sortEval,iVF] using (vf_zero_mem hM)
      · simpa only [hj,ite_false,Function.comp_apply,Sum.elim_inl,sortEval,iVF] using c.property.1 j)
    (by
      intro c
      apply Prod.ext
      · funext j
        apply Subtype.ext
        by_cases hj : j=i
        · subst j
          simp only [erase,replace,Function.update_self]
          simp only [Function.comp_apply,Sum.elim_inl,ite_true]
          exact (CanonicalStructure.normalize_fun Fn.vfZero Fin.elim0 (fun i => i.elim0)).symm
        · simp only [erase,replace,Function.update_of_ne hj]
          simp only [Function.comp_apply,Sum.elim_inl,hj,ite_false]
      · rfl)

theorem native_erase_map_value (A : DefSet (M := M) S n m) (i : Fin n) (p : A) :
    (nativeEraseMap A i p).val = erase i p.val := rfl

theorem gamma_zero_vf_coordinate (G : Base (M := M)) (i : Fin n) :
    GammaSetDefinable G {p : Point (M := M) n m | vfAt p i = 0} := by
  let A := PresentedSet.univ (pointSpace (M := M) n m) G.real
  have h := (gammaLogicInput G).image_graph ((gammaLogicInput G).real_map_graph (nativeEraseMap A i))
  convert h using 1
  ext p
  constructor
  · intro hp
    refine ⟨p,⟨p,Set.mem_univ _⟩,rfl,?_⟩
    change replace i p 0 = p
    have hv : (0 : VF (M := M)) = vfAt p i := hp.symm
    exact Prod.ext (by rw [hv]; exact Function.update_eq_self _ _) rfl
  · rintro ⟨q,a,rfl,ha⟩
    have hv := congrArg (fun z : Point (M := M) n m => vfAt z i) ha
    change Function.update a.val.1 i (0 : VF (M := M)) i = vfAt p i at hv
    exact (Function.update_self _ _ _).symm.trans hv |>.symm

end IntegrationInACVF.Section7
