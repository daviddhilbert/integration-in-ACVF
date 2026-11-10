import IntegrationSection3ACVF.AtomicPolynomialRoots
import IntegrationSection3ACVF.SeparationFunctions
import IntegrationSection3.BivariateCoordinates
import Section4.PolynomialZero

/-! A nonzero original-parameter-field polynomial cannot vanish between
the two atomic geometries separated by corrected3.11. -/

set_option backward.isDefEq.respectTransparency false

open Set Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer SpecialTransformations.Section3
open SpecialTransformations.Section4
open IntegrationInACVF.Section3

namespace IntegrationInACVF.Section3ACVF.PolynomialSeparation

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

theorem open_subset_vf {O : Set M} (hO : PaperBalls.IsOpenBall O) : O ⊆ {x | iVF x} := by
  rcases hO with he | ⟨a,γ,he⟩
  · rw [he]
  · rw [he]
    exact fun x hx => hx.1

theorem zeroSet_mem_iff (E : Subfield (VFType (M := M)))
    (q : MvPolynomial (Fin 2) E) (a b : VFType (M := M)) :
    ![a.val,b.val] ∈ PolynomialZero.zeroSet E q ↔ q.eval₂ E.subtype ![a,b] = 0 := by
  have he (h : ∀ i, iVF ((![a.val,b.val] : Fin 2 → M) i)) :
      (fun i => (⟨(![a.val,b.val] : Fin 2 → M) i,h i⟩ : VFType (M := M))) = ![a,b] := by
    funext i
    fin_cases i <;> rfl
  constructor
  · rintro ⟨h,hq⟩
    rwa [he h] at hq
  · intro hq
    have h : ∀ i, iVF ((![a.val,b.val] : Fin 2 → M) i) := by
      intro i
      fin_cases i
      · exact a.property
      · exact b.property
    refine ⟨h,?_⟩
    rwa [he h]

theorem nonzero_on_product (B : FullBaseAtomicity.Base (M := M))
    (h00 : M ⊨ Axioms.ACVF00) (δ : Values.Gamma (M := M))
    (hδ : FullGammaSyntax.Scalar B {δ}) (hδ1 : 1 < δ)
    {O A : Set M} (hOpen : PaperBalls.IsOpenBall O)
    (hO : AdjoinBall.AtomicOver B O) (hA : AdjoinBall.AtomicOver B A)
    (hTarget : (PaperBalls.IsClosedBall A ∧
      ∃ r : PaperBalls.Radius (M := M), PaperBalls.HasRadius A r ∧
        r < (↑(Values.infinity (M := M)) : PaperBalls.Radius (M := M))) ∨
      ∃ d : PuncturedGeometry.PuncturedBall M, PaperBalls.IsThinAnnulus d ∧ d.body = A)
    (q : MvPolynomial (Fin 2) (vfParameterField (M := M) B.real)) (hq : q ≠ 0)
    (a b : VFType (M := M)) (ha : a.val ∈ A) (hb : b.val ∈ O) :
    q.eval₂ (vfParameterField B.real).subtype ![a,b] ≠ 0 := by
  classical
  let E := vfParameterField (M := M) B.real
  let Z := PolynomialZero.zeroSet E q
  let R : Set (M × M) := {p | p.1 ∈ O ∧ p.2 ∈ A ∧ ![p.2,p.1] ∈ Z}
  have hZ := ((definableOver_iff_normalized_raw B.real (fun _ => .vf) Z).mp
    (PolynomialZero.zeroSet_parameterField_definable B.real q)).1
  have hZB := FullBaseAtomicity.OverBase.of_real (B := B) hZ
  have hO0 := FullBaseAtomicity.OverBase.preimage_comp hO.1 (fun _ : Fin 1 => (0 : Fin 2))
  have hA1 := FullBaseAtomicity.OverBase.preimage_comp hA.1 (fun _ : Fin 1 => (1 : Fin 2))
  have hswap := FullBaseAtomicity.OverBase.preimage_comp hZB (![1,0] : Fin 2 → Fin 2)
  have hBoth := FullBaseAtomicity.OverBase.inter hO0 (FullBaseAtomicity.OverBase.inter hA1 hswap)
  have hR : FullBaseAtomicity.OverBase B {z : Fin 2 → M | (z 0,z 1) ∈ R} := by
    apply FullBaseAtomicity.OverBase.congr hBoth
    intro z
    have he : z ∘ (![1,0] : Fin 2 → Fin 2) = ![z 1,z 0] := by
      funext i
      fin_cases i <;> rfl
    change (z 0 ∈ O ∧ z 1 ∈ A ∧ z ∘ (![1,0] : Fin 2 → Fin 2) ∈ Z) ↔ _
    rw [he]
    rfl
  have hsub : R ⊆ O ×ˢ A := fun p hp => ⟨hp.1,hp.2.1⟩
  have hOinf := SeparationFunctions.open_infinite h00 δ hδ1 hOpen
  have hOvf := open_subset_vf hOpen
  let F := BivariateCoordinates.equiv E q
  have hF : F ≠ 0 := (BivariateCoordinates.ne_zero_iff q).mpr hq
  have hfinite (c : M) (hc : c ∈ O) : {x | (c,x) ∈ R}.Finite := by
    let u : VFType (M := M) := ⟨c,hOvf hc⟩
    let P := PolynomialSpecialization.specialize (F.map (Polynomial.mapRingHom E.subtype)) u
    have hP : P ≠ 0 := AtomicPolynomialRoots.specialization_parameterField B hO.2 hOinf F hF u hc
    have hroots := (Polynomial.finite_setOfPred_isRoot hP).image Subtype.val
    apply hroots.subset
    intro x hx
    have hxVF : iVF x := (show ![x,c] ∈ Z from hx.2.2).choose 0
    let v : VFType (M := M) := ⟨x,hxVF⟩
    have hzero : q.eval₂ E.subtype ![v,u] = 0 := (zeroSet_mem_iff E q v u).mp hx.2.2
    refine ⟨v,?_,rfl⟩
    change P.eval v = 0
    change (PolynomialSpecialization.specialize
      ((BivariateCoordinates.equiv E q).map (Polynomial.mapRingHom E.subtype)) u).eval v = 0
    rw [BivariateCoordinates.eval₂_coordinates]
    exact hzero
  intro hzero
  have hne : R.Nonempty :=
    ⟨(b.val,a.val),hb,ha,(zeroSet_mem_iff E q a b).mpr hzero⟩
  exact Separation.lemma_3_11 B h00 δ hδ hδ1 hOpen hO hA hTarget hR hsub hne hfinite

end IntegrationInACVF.Section3ACVF.PolynomialSeparation
