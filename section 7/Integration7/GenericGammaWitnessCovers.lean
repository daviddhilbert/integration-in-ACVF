import IntegrationSection6.GammaWitnessUniformity
import Section4.GenericPoints
import Mathlib.Data.Finset.Sum

/-! A Gamma-definable witness available at every generic VF tuple has a
finite witness cover away from finitely many proper polynomial zero sets.
Compactness is applied over the original real and Gamma names together. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4
open IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

set_option maxHeartbeats 1600000 in
theorem gamma_finite_witnesses_off_polynomial_zero {κ : Cardinal} {n : ℕ}
    (B : Base (M := M)) (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (hreal : Cardinal.mk B.real < κ) (hgamma : Cardinal.mk B.gamma < κ)
    {I : Type} (valid : I → Set (Fin n → M))
    (hvalid : ∀ i, DefinableOverBase B (fun _ => .vf) (valid i))
    (hgeneric : ∀ x : Fin n → VFType (M := M),
      AlgebraicIndependent (vfParameterField B.real) x → ∃ i, vfValues x ∈ valid i) :
    ∃ P : Finset {p : MvPolynomial (Fin n) (vfParameterField B.real) // p ≠ 0},
      ∃ J : Finset I, ∀ x : Fin n → VFType (M := M),
        (∃ p ∈ P, p.val.eval₂ (vfParameterField B.real).subtype x = 0) ∨
        ∃ i ∈ J, vfValues x ∈ valid i := by
  let E := vfParameterField B.real
  let Poly := {p : MvPolynomial (Fin n) E // p ≠ 0}
  let pred : Poly ⊕ I → Set (Fin n → M) := Sum.elim
    (fun p => PolynomialZero.zeroSet E p.val) valid
  have hpred : ∀ w, DefinableOverBase B (fun _ => .vf) (pred w) := by
    intro w
    cases w with
    | inl p => exact real_definableOverBase B _ _ (PolynomialZero.zeroSet_parameterField_definable B.real p.val)
    | inr i => exact hvalid i
  have hcover : ∀ z ∈ sortedUniverse (fun _ : Fin n => SortTag.vf), ∃ w, z ∈ pred w := by
    intro z hz
    let x : Fin n → VFType (M := M) := fun j => ⟨z j,hz j⟩
    by_cases hx : AlgebraicIndependent E x
    · obtain ⟨i,hi⟩ := hgeneric x hx
      exact ⟨Sum.inr i,hi⟩
    · have hex : ∃ p : MvPolynomial (Fin n) E, p ≠ 0 ∧ p.eval₂ E.subtype x = 0 := by
        by_contra h
        apply hx
        refine algebraicIndependent_iff.mpr ?_
        intro p hp
        by_contra hp0
        exact h ⟨p,hp0,hp⟩
      obtain ⟨p,hp,hpx⟩ := hex
      exact ⟨Sum.inl ⟨p,hp⟩,hz,hpx⟩
  obtain ⟨K,hK⟩ := gamma_finite_witnesses hκ hs hreal hgamma
    (fun _ => .vf) (sortedUniverse (fun _ : Fin n => .vf))
    (real_definableOverBase B _ _ (sortedUniverse_definable B.real _)) pred hpred hcover
  refine ⟨K.toLeft,K.toRight,fun x => ?_⟩
  obtain ⟨w,hw,hx⟩ := hK (vfValues x) (fun j => (x j).property)
  cases w with
  | inl p =>
    left
    refine ⟨p,Finset.mem_toLeft.mpr hw,?_⟩
    obtain ⟨hz,hzero⟩ := hx
    have he : (fun j => (⟨(x j).val,hz j⟩ : VFType (M := M))) = x := by
      funext j
      exact Subtype.ext rfl
    change p.val.eval₂ E.subtype (fun j => ⟨(x j).val,hz j⟩) = 0 at hzero
    rwa [he] at hzero
  | inr i => exact Or.inr ⟨i,Finset.mem_toRight.mpr hw,hx⟩

theorem gamma_finite_witnesses_at_generic_points {κ : Cardinal} {n : ℕ}
    (B : Base (M := M)) (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (hreal : Cardinal.mk B.real < κ) (hgamma : Cardinal.mk B.gamma < κ)
    {I : Type} (valid : I → Set (Fin n → M))
    (hvalid : ∀ i, DefinableOverBase B (fun _ => .vf) (valid i))
    (hgeneric : ∀ x : Fin n → VFType (M := M),
      AlgebraicIndependent (vfParameterField B.real) x → ∃ i, vfValues x ∈ valid i) :
    ∃ J : Finset I, ∀ x : Fin n → VFType (M := M),
      AlgebraicIndependent (vfParameterField B.real) x → ∃ i ∈ J, vfValues x ∈ valid i := by
  obtain ⟨P,J,hJ⟩ := gamma_finite_witnesses_off_polynomial_zero B hκ hs hreal hgamma valid hvalid hgeneric
  refine ⟨J,fun x hx => ?_⟩
  rcases hJ x with ⟨p,_,hp⟩ | h
  · exact (p.property ((algebraicIndependent_iff.mp hx) p.val hp)).elim
  · exact h

end IntegrationInACVF.Section7
