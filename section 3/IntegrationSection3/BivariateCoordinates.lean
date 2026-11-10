module

public import IntegrationSection3.PolynomialSpecialization
public import Mathlib.Algebra.MvPolynomial.Equiv
public import Mathlib.Algebra.Polynomial.AlgebraMap

@[expose] public section

/-! Preserve the two VF coordinates when passing from the actual LRV
syntax's multivariate polynomials to iterated univariate polynomials. -/

namespace IntegrationInACVF.Section3.BivariateCoordinates

noncomputable def equiv (K : Type*) [Field K] :
    MvPolynomial (Fin 2) K ≃ₐ[K] Polynomial (Polynomial K) :=
  (MvPolynomial.finSuccEquiv K 1).trans
    (Polynomial.mapAlgEquiv (MvPolynomial.uniqueAlgEquiv K (Fin 1)))

variable {K : Type*} [Field K]

theorem ne_zero_iff (p : MvPolynomial (Fin 2) K) : equiv K p ≠ 0 ↔ p ≠ 0 := by
  constructor
  · intro h hp
    exact h (by rw [hp,map_zero])
  · intro h hp
    apply h
    apply (equiv K).injective
    simpa only [map_zero] using hp

theorem eval_coordinates (p : MvPolynomial (Fin 2) K) (x y : K) :
    (PolynomialSpecialization.specialize (equiv K p) y).eval x = MvPolynomial.eval ![x,y] p := by
  let φ : MvPolynomial (Fin 2) K →ₐ[K] K :=
    (Polynomial.aeval x).comp ((Polynomial.mapAlgHom (Polynomial.aeval y)).comp (equiv K).toAlgHom)
  have he : φ = MvPolynomial.aeval ![x,y] := by
    apply MvPolynomial.algHom_ext
    intro i
    fin_cases i
    · simp [φ,equiv,MvPolynomial.finSuccEquiv_X_zero,MvPolynomial.uniqueAlgEquiv]
    · have hX : (MvPolynomial.finSuccEquiv K 1) (MvPolynomial.X (1 : Fin 2)) =
          Polynomial.C (MvPolynomial.X (0 : Fin 1)) :=
        MvPolynomial.finSuccEquiv_X_succ (R := K) (n := 1) (j := 0)
      simp [φ,equiv,hX,MvPolynomial.uniqueAlgEquiv]
  have hp := congrArg (fun f : MvPolynomial (Fin 2) K →ₐ[K] K => f p) he
  simpa [φ,PolynomialSpecialization.specialize,Polynomial.coe_aeval_eq_eval,
    Polynomial.coe_mapAlgHom] using hp

theorem eval₂_coordinates {R : Type*} [Field R] (f : R →+* K)
    (p : MvPolynomial (Fin 2) R) (x y : K) :
    (PolynomialSpecialization.specialize
      ((equiv R p).map (Polynomial.mapRingHom f)) y).eval x =
        MvPolynomial.eval₂ f ![x,y] p := by
  let φ : MvPolynomial (Fin 2) R →+* K :=
    (Polynomial.evalRingHom x).comp
      ((Polynomial.mapRingHom (Polynomial.eval₂RingHom f y)).comp (equiv R).toRingHom)
  have he : φ = MvPolynomial.eval₂Hom f ![x,y] := by
    apply MvPolynomial.ringHom_ext
    · intro r
      rw [MvPolynomial.eval₂Hom_C]
      change Polynomial.eval x
        (Polynomial.map (Polynomial.eval₂RingHom f y) (equiv R (MvPolynomial.C r))) = f r
      rw [show equiv R (MvPolynomial.C r) = Polynomial.C (Polynomial.C r) from
        (equiv R).commutes r]
      simp
    · intro i
      fin_cases i
      · simp [φ,equiv,MvPolynomial.finSuccEquiv_X_zero]
      · have hX : (MvPolynomial.finSuccEquiv R 1) (MvPolynomial.X (1 : Fin 2)) =
            Polynomial.C (MvPolynomial.X (0 : Fin 1)) :=
          MvPolynomial.finSuccEquiv_X_succ (R := R) (n := 1) (j := 0)
        simp [φ,equiv,hX,MvPolynomial.uniqueAlgEquiv]
  have hcomp : Polynomial.eval₂RingHom f y =
      (Polynomial.evalRingHom y).comp (Polynomial.mapRingHom f) := by
    apply RingHom.ext
    intro q
    change q.eval₂ f y = (q.map f).eval y
    rw [Polynomial.eval_map]
  have hm : PolynomialSpecialization.specialize
      ((equiv R p).map (Polynomial.mapRingHom f)) y =
      (equiv R p).map (Polynomial.eval₂RingHom f y) := by
    rw [PolynomialSpecialization.specialize,Polynomial.map_map,← hcomp]
  rw [hm]
  have hp := congrArg (fun g : MvPolynomial (Fin 2) R →+* K => g p) he
  exact hp

end IntegrationInACVF.Section3.BivariateCoordinates
