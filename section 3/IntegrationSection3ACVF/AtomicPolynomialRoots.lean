import IntegrationSection3ACVF.FullBaseDefinability
import IntegrationSection3ACVF.FullBallCoset
import IntegrationSection3.PolynomialSpecialization

/-! Finite-root avoidance for infinite complete types over the full
interpreted base. Coefficients may lie in the real base's VF definable
closure; their temporary names are eliminated by the pinned sorted API. -/

set_option backward.isDefEq.respectTransparency false

open Set Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer SpecialTransformations.Section3
open IntegrationInACVF.Section3

namespace IntegrationInACVF.Section3ACVF.AtomicPolynomialRoots

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

theorem rootSet_definable (B : FullBaseAtomicity.Base (M := M))
    (E : Subfield (VFType (M := M))) (hE : E ≤ vfDefinableClosureField B.real)
    (q : Polynomial E) :
    FullBaseAtomicity.OverBase B
      {z : Fin 1 → M | z 0 ∈ PolynomialRoots.rootSet E q} := by
  let Z := PolynomialRoots.rootSet E q
  let D : Set M := {x | DefinableClosureAt B.real .vf x}
  have hnamed (x : E) : x.val.val ∈ D := hE x.property
  have hz : DefinableAt B.real .vf Z :=
    (PolynomialRoots.rootSet_definable D E hnamed q).eliminate_sorted_definable_params
      (fun x hx => ⟨.vf,hx⟩)
  exact FullBaseAtomicity.OverBase.of_real
    (((@definableAt_iff_normalized_raw M sM hM B.real .vf Z).mp hz).1)

theorem nonzero_on_complete_type (B : FullBaseAtomicity.Base (M := M))
    {A : Set M} (hA : FullBallCoset.CompleteType B A) (hinf : A.Infinite)
    (E : Subfield (VFType (M := M))) (hE : E ≤ vfDefinableClosureField B.real)
    (q : Polynomial E) (hq : q ≠ 0) (a : VFType (M := M)) (ha : a.val ∈ A) :
    q.eval₂ E.subtype a ≠ 0 := by
  let Z := PolynomialRoots.rootSet E q
  have hZ : FullBaseAtomicity.OverBase B {z : Fin 1 → M | z 0 ∈ Z} :=
    rootSet_definable B E hE q
  have hfin : Z.Finite := PolynomialRoots.rootSet_finite E q hq
  rcases hA Z hZ with hsub | hdis
  · exact (hinf (hfin.subset hsub)).elim
  · intro hzero
    exact Set.disjoint_left.mp hdis ha ⟨a.property,hzero⟩

theorem specialization_nonzero_on_complete_type (B : FullBaseAtomicity.Base (M := M))
    {A : Set M} (hA : FullBallCoset.CompleteType B A) (hinf : A.Infinite)
    (E : Subfield (VFType (M := M))) (hE : E ≤ vfDefinableClosureField B.real)
    (F : Polynomial (Polynomial E)) (hF : F ≠ 0)
    (a : VFType (M := M)) (ha : a.val ∈ A) :
    PolynomialSpecialization.specialize (F.map (Polynomial.mapRingHom E.subtype)) a ≠ 0 := by
  classical
  have hex : ∃ i : ℕ, F.coeff i ≠ 0 := by
    by_contra hn
    apply hF
    apply Polynomial.ext
    intro i
    change F.coeff i = 0
    by_contra hi
    exact hn ⟨i,hi⟩
  obtain ⟨i,hi⟩ := hex
  have hne := nonzero_on_complete_type B hA hinf E hE (F.coeff i) hi a ha
  intro hzero
  have hc := congrArg (fun p : Polynomial (VFType (M := M)) => p.coeff i) hzero
  have he : ((F.coeff i).map E.subtype).eval a = 0 := by
    simpa only [PolynomialSpecialization.specialize,Polynomial.coeff_map,
      Polynomial.coeff_zero,Polynomial.coe_evalRingHom,Polynomial.coe_mapRingHom] using hc
  rw [Polynomial.eval_map] at he
  exact hne he

theorem specialization_parameterField (B : FullBaseAtomicity.Base (M := M))
    {A : Set M} (hA : FullBallCoset.CompleteType B A) (hinf : A.Infinite)
    (F : Polynomial (Polynomial (vfParameterField (M := M) B.real))) (hF : F ≠ 0)
    (a : VFType (M := M)) (ha : a.val ∈ A) :
    PolynomialSpecialization.specialize
      (F.map (Polynomial.mapRingHom (vfParameterField (M := M) B.real).subtype)) a ≠ 0 :=
  specialization_nonzero_on_complete_type B hA hinf (vfParameterField B.real)
    (vfParameterField_le_definableClosureField B.real) F hF a ha

end IntegrationInACVF.Section3ACVF.AtomicPolynomialRoots
