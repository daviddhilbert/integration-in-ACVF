import IntegrationSection6.IntegrationContexts
import IntegrationSection6.VFParameterRowObjects
import IntegrationSection6.VFParameterFibreIsomorphisms
import IntegrationSection6.DefinableFamilyIntegration

/-! Integration of actual VF fibres in the varying coefficient semirings,
and its compatibility with the previously defined RV family values. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5 SpecialTransformations.Section7
namespace IntegrationInACVF.Section6.FiniteRV
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {κ : Cardinal} {hs : Saturated M κ} {p n m a b : ℕ}

def IntegrationContext.rowIntegral (P : IntegrationContext B κ hs)
    (U : Set (Point (M := M) (p+n) a)) (hU : GammaSetDefinable B U)
    (hfin : ∀ z : Fin (p+n) → VF (M := M), {r : Fin a → SpecialTransformations.Section5.RV (M := M) | (z,r) ∈ U}.Finite)
    (x : Fin p → VF (M := M)) : (P.atVF x).RV := by
  letI := (P.atVF x).vfSemiring
  exact (P.atVF x).equivalence (PositiveAdditiveGrothendieck.of
    (gammaVFAllAdditivePresentation (vfParameterCoefficientBase B x)) (vfParameterRowObject U hU hfin x))

theorem IntegrationContext.rowIntegral_iso (P : IntegrationContext B κ hs)
    (U : Set (Point (M := M) (p+n) a)) (V : Set (Point (M := M) (p+m) b))
    (hU : GammaSetDefinable B U) (hV : GammaSetDefinable B V)
    (hfinU : ∀ z : Fin (p+n) → VF (M := M), {r : Fin a → SpecialTransformations.Section5.RV (M := M) | (z,r) ∈ U}.Finite)
    (hfinV : ∀ z : Fin (p+m) → VF (M := M), {r : Fin b → SpecialTransformations.Section5.RV (M := M) | (z,r) ∈ V}.Finite)
    (e : GammaIso B U V) (hp : VFParametersPreserved e) (x : Fin p → VF (M := M)) :
    P.rowIntegral U hU hfinU x = P.rowIntegral V hV hfinV x := by
  letI := (P.atVF x).vfSemiring
  let C : Base (M := M) := ⟨B.real ∪ Set.range (fun j => (x j).val),B.gamma⟩
  let f := gammaVFParameterFibreIso e hp x
  let g : GammaIso (vfParameterCoefficientBase B x) (vfParameterFibre U x) (vfParameterFibre V x) :=
    ⟨f.equiv,f.graph.mono (subset_closureBase C).1 (subset_closureBase C).2⟩
  exact congrArg (P.atVF x).equivalence
    (PositiveAdditiveGrothendieck.of_iso (gammaVFAllAdditivePresentation (vfParameterCoefficientBase B x)) ⟨g⟩)

theorem IntegrationContext.rowIntegral_familyLift (P : IntegrationContext B κ hs) {a k : ℕ}
    (A : Set (Point (M := M) p 0)) (hA : GammaSetDefinable B A)
    (F : GammaFiniteRVSchema B p a k) (hF : ∀ x : A, F.finiteRow (fun j => (x.val.1 j).val)) (x : A) :
    P.rowIntegral (familyLiftDomain A F) (gamma_family_lift_definable A hA F)
        (gammaFamilyLift A hA F hF).finiteFibres x.val.1 =
      schemaRowCoefficient P.countable_le hs P.characteristic P.real_small P.gamma_small P.field_base P.generated
        P.value P.value_mem P.value_large P.section5_two_order F x.val.1 (hF x) := by
  let Q := P.atVF x.val.1
  letI := Q.vfSemiring
  let U := schemaRowObject F x.val.1 (hF x)
  have hsrc : U.toGamma.lift = vfParameterFibre (familyLiftDomain A F) x.val.1 :=
    (schemaRowObject_lift F x.val.1 (hF x)).trans (familyLiftDomain_fibre A F x).symm
  have hc : PositiveAdditiveGrothendieck.of (gammaVFAllAdditivePresentation (vfParameterCoefficientBase B x.val.1))
        (vfParameterRowObject (familyLiftDomain A F) (gamma_family_lift_definable A hA F)
          (gammaFamilyLift A hA F hF).finiteFibres x.val.1) = gammaAllAdditiveLiftClass U.toGamma := by
    exact PositiveAdditiveGrothendieck.of_iso _
      ⟨(gammaIso_reflexive U.toGamma.lift U.toGamma.toGammaRVObject.lift_definable).congr hsrc rfl⟩
  change Q.equivalence (PositiveAdditiveGrothendieck.of _ _) = _
  rw [hc]
  exact theorem_6_19_lift_finite Q.countable_le hs Q.characteristic Q.real_small Q.field_base Q.gamma_small
    Q.value Q.value_mem Q.value_large Q.section5_two_order Q.generated U.toGamma

end IntegrationInACVF.Section6.FiniteRV
