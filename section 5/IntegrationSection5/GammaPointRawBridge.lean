import IntegrationSection5.GammaFullBaseBridge
import IntegrationSection5.GammaGraphOperations
import Section5.VerticalConstruction

/-! Full-base tuple predicates and the invariant Gamma certificates describe
the same original mixed point sets. Only the finite coordinate indexing changes. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.DefinableGeometry.Space.prod
  SpecialTransformations.Section4.realSpace SpecialTransformations.Milestone0.sortEval
  SpecialTransformations.Section4.vfSpace SpecialTransformations.Section4.rvSpace

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section5 SpecialTransformations.Section3
open IntegrationInACVF.Section3ACVF

namespace IntegrationInACVF.Section5
variable {M : Type} [sM : LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {P : GammaParameters.Base (M := M)} {n m : ℕ}

theorem pointValues_eq_gammaPointCode (p : Point (M := M) n m) :
    pointValues p = gammaPointCode p ∘ finSumFinEquiv := by
  funext i
  cases i <;> simp only [Function.comp_apply,finSumFinEquiv_apply_left,
    finSumFinEquiv_apply_right,gammaPointCode,pointValues,Fin.append_left,Fin.append_right,vfAt,Sum.elim_inl,Sum.elim_inr]

theorem pointValues_image_iff (A : Set (Point (M := M) n m)) (z : Fin n ⊕ Fin m → M) :
    z ∈ pointValues '' A ↔ z ∘ finSumFinEquiv.symm ∈ gammaPointCode '' A := by
  constructor
  · rintro ⟨p,hp,rfl⟩
    refine ⟨p,hp,?_⟩
    rw [pointValues_eq_gammaPointCode]
    funext i
    simp only [Function.comp_apply,Equiv.apply_symm_apply]
  · rintro ⟨p,hp,he⟩
    refine ⟨p,hp,?_⟩
    rw [pointValues_eq_gammaPointCode,he]
    funext i
    simp only [Function.comp_apply,Equiv.symm_apply_apply]

theorem gammaPointCode_sorted (p : Point (M := M) n m) :
    ∀ i, @sortEval M sM (gammaPointSort n m i) (gammaPointCode p i) := by
  intro i
  cases i using Fin.addCases with
  | left i => simpa only [gammaPointSort,gammaPointCode,Fin.append_left,vfAt,sortEval,iVF] using (p.1 i).property
  | right i => simpa only [gammaPointSort,gammaPointCode,Fin.append_right,sortEval,iRV] using (p.2 i).property

theorem gammaSet_full_raw_iff (A : Set (Point (M := M) n m)) :
    GammaSetDefinable P A ↔ FullBaseAtomicity.OverBase (sM := sM) (gammaFullBase P) (pointValues '' A) := by
  let e : Fin n ⊕ Fin m ≃ Fin (n+m) := finSumFinEquiv
  constructor
  · intro hA
    have h := FullBaseAtomicity.OverBase.preimage_comp (gamma_to_full hA) e.symm
    apply FullBaseAtomicity.OverBase.congr h
    intro z
    exact (pointValues_image_iff A z).symm
  · intro hA
    have h := FullBaseAtomicity.OverBase.preimage_comp hA e
    have h' : FullBaseAtomicity.OverBase (sM := sM) (gammaFullBase P) (gammaPointCode '' A) := by
      apply FullBaseAtomicity.OverBase.congr h
      intro z
      constructor
      · rintro ⟨p,hp,he⟩
        refine ⟨p,hp,?_⟩
        rw [pointValues_eq_gammaPointCode] at he
        funext i
        have hi := congrFun he (e.symm i)
        simpa only [Function.comp_apply,Equiv.apply_symm_apply,e] using hi
      · rintro ⟨p,hp,rfl⟩
        exact ⟨p,hp,pointValues_eq_gammaPointCode p⟩
    exact full_to_gamma (gammaPointSort n m) h' (by
      rintro z ⟨p,hp,rfl⟩; exact gammaPointCode_sorted p)

end IntegrationInACVF.Section5
