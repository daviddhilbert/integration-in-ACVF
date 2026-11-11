import IntegrationSection4.RelativeObstaclePreparation
import Section5.GammaInvariantLogic

/-! Uniform preparation in one VF direction over the original Gamma base.
The ambient vertical bijection is definable over the original real base;
Gamma representatives do not enter its coefficients or its foci. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false

set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.DefinableGeometry.Space.prod
  SpecialTransformations.Section4.realSpace SpecialTransformations.Milestone0.sortEval
  SpecialTransformations.Section4.vfSpace SpecialTransformations.Section4.rvSpace

open Set Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters SpecialTransformations.Section5

namespace IntegrationInACVF.Section4.RelativeGammaPreparation

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

/-- The complete original-base relation is uniform in all free RV arguments
on the vertical inverse slices of one actual definable bijection. -/
theorem prepare {κ : Cardinal} (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (G : GammaParameters.Base (M := M)) (hsmall : Cardinal.mk G.real < κ)
    (hGenerated : VFGammaGeneratedBase G) {n m k : ℕ}
    (r : Point (M := M) (n+1) m → Point (M := M) 0 k → Prop)
    (hr : GammaGraphDefinable G r) :
    ∃ l : ℕ, ∃ B : DefSet (M := M) G.real (n+1) l,
      ∃ V : RelativeBijection (PresentedSet.univ (pointSpace (n+1) m) G.real) B,
        HeadSaturated (carrier B) ∧ (∃ j, Tagged (carrier B) 0 j) ∧
          ∀ b c : B, SameRV b.val c.val → TailEq b.val c.val → ∀ z,
            r (V.inverseMap b).val z ↔ r (V.inverseMap c).val z := by
  obtain ⟨d,p,hCoeff,hControl⟩ := gammaPolynomialSupportInput_of_generatedBase G hGenerated r hr
  let A := PresentedSet.univ (pointSpace (M := M) (n+1) m) G.real
  let C := canonicalImage A
  let W := RelativeBijection.canonical A
  let D := PresentedSet.univ (pointSpace (M := M) d 0) G.real
  let f := mvPolynomialTupleMap C p hCoeff
  let g := Map.comp (flattenKeyMap (PresentedSet.univ (keySpace d 0) G.real)) (Map.comp (keyMap D) f)
  have hC : IsRVPullback (carrier C) := (SpecialBijection.canonical A).preserves_pullback (by
    apply (isRVPullback_iff _).mpr
    intro b _ c _
    exact Set.mem_univ _)
  obtain ⟨l,B,T,hB,hTag,hUniform⟩ := RelativeObstaclePreparation.prepare hs hsmall h00 C hC
    (canonicalImage_allTagged A 0) g
  let V := W.comp T
  have hComm (b : B) : W.toMap (V.inverseMap b) = T.inverseMap b := by
    apply T.bijective.1
    rw [T.apply_inverse]
    exact V.apply_inverse b
  have hVF (b : B) : vfAt (V.inverseMap b).val = vfAt (T.inverseMap b).val := by
    have hh := congrArg (fun q : C => vfAt q.val) (hComm b)
    exact hh
  refine ⟨l,B,V,hB,hTag,?_⟩
  intro b c he ht z
  have hPolys : ∀ i, rv (MvPolynomial.eval (vfAt (V.inverseMap b).val) (p i)) =
      rv (MvPolynomial.eval (vfAt (V.inverseMap c).val) (p i)) := by
    intro i
    rw [hVF b,hVF c]
    have hh := congrFun (congrArg (fun q => q.val.2) (hUniform b c he ht)) (Fin.castAdd 0 i)
    change Fin.append (fun j => rv (MvPolynomial.eval (vfAt (T.inverseMap b).val) (p j))) Fin.elim0 (Fin.castAdd 0 i) =
      Fin.append (fun j => rv (MvPolynomial.eval (vfAt (T.inverseMap c).val) (p j))) Fin.elim0 (Fin.castAdd 0 i) at hh
    simpa only [Fin.append_left] using hh
  exact hControl _ _ (V.inverse_labels b c ((sameRV_iff _ _).mp he).2) hPolys z

end IntegrationInACVF.Section4.RelativeGammaPreparation
