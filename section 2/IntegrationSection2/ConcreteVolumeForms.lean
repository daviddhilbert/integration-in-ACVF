import Section9.MixedJacobian
import Section9.LiftLabelRepresentatives
import Section9.GammaJacobian
import Section9.RVJacobian

/-! Concrete RV-valued volume forms on the pinned finite-volume
objects and their actual lifts. These definitions use the actual RV
group, Gamma quotient and partial VF Jacobian; no volume laws or
Jacobian comparison theorem are fields of the model. -/

open Set Classical FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer SpecialTransformations.Section3
open SpecialTransformations.Section4 SpecialTransformations.Section7 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry

namespace IntegrationInACVF.Section2.ConcreteVolumeForms

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF] {S : Set M} {k : ℕ}

structure RVForm (U : RVFiniteObject (M := M) S k) where
  map : Map U.obj.domain (DefSet.univ (rawRVSpace (M := M) 1) S)
  nonzero : ∀ u, ((map u).val 0).val ≠ iRVZero

noncomputable def value {U : RVFiniteObject (M := M) S k} (ω : RVForm U) (u : U.obj.domain) :
    CanonicalRV.RVSort M := (ω.map u).val 0

theorem value_ne_zero {U : RVFiniteObject (M := M) S k} (ω : RVForm U) (u : U.obj.domain) : value ω u ≠ 0 := by
  intro h
  exact ω.nonzero u ((congrArg Subtype.val h).trans RVOperations.zero_val)

noncomputable def gammaValue {U : RVFiniteObject (M := M) S k} (ω : RVForm U) (u : U.obj.domain) :
    Values.Gamma (M := M) := Values.gammaOf (value ω u) (ω.nonzero u)

noncomputable def lift {U : RVFiniteObject (M := M) S k} (ω : RVForm U) :
    Map (rvLift U.obj) (DefSet.univ (rawRVSpace (M := M) 1) S) :=
  ω.map.comp (liftLabelMap U.obj)

noncomputable def liftedValue {U : RVFiniteObject (M := M) S k} (ω : RVForm U) (p : rvLift U.obj) :
    CanonicalRV.RVSort M := (lift ω p).val 0

theorem liftedValue_eq {U : RVFiniteObject (M := M) S k} (ω : RVForm U) (p : rvLift U.obj) :
    liftedValue ω p = value ω (liftLabelMap U.obj p) := rfl

/-- The concrete VF-volume equation outside one actual VF-small set. -/
def PreservesOff {U V : RVFiniteObject (M := M) S k} (ω : RVForm U) (π : RVForm V)
    (f : Map (rvLift U.obj) (rvLift V.obj)) : Prop :=
  ∃ Z : DefSet (rawMixedSpace (M := M) k U.obj.arity) S,
    vfDim (rawRVSpace (M := M) 1) Z < k ∧
      ∀ p : rvLift U.obj, p.val ∉ Z.carrier →
        ∃ J : VFType (M := M), HasMixedVFJacobianAt f p J ∧
          liftedValue ω p = liftedValue π (f p) * CanonicalRV.encodedRv J

theorem nonzero_jacobian_of_preserves {U V : RVFiniteObject (M := M) S k}
    (ω : RVForm U) (π : RVForm V) (f : Map (rvLift U.obj) (rvLift V.obj))
    (p : rvLift U.obj) (J : VFType (M := M))
    (hMeasure : liftedValue ω p = liftedValue π (f p) * CanonicalRV.encodedRv J) : J ≠ 0 := by
  intro hJ
  have hZero : liftedValue ω p = 0 := by
    rw [hMeasure,hJ,RVOperations.rv_zero,mul_zero]
  exact value_ne_zero ω (liftLabelMap U.obj p) hZero

end IntegrationInACVF.Section2.ConcreteVolumeForms
