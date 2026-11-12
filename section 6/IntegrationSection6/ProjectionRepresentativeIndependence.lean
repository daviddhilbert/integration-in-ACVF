import IntegrationSection6.ProjectionFamilyRepresentations
import IntegrationSection6.DefinableFamilyParameterIsomorphisms

/-! Projection fibre integrals depend only on the represented function. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
namespace IntegrationInACVF.Section6
open FiniteRV
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {κ : Cardinal} {hs : Saturated M κ} {n p : ℕ}

theorem projectionFamily_parameter_iso (P : IntegrationContext B κ hs) (E : VFCoordinateProjection n p)
    (A : Set (Point (M := M) n 0)) (hA : GammaSetDefinable B A) (F G : DefinableRVFamily B A)
    (he : ∀ x : A, P.familyValue F x = P.familyValue G x) :
    ∃ e : GammaIso B (projectionFamilyDomain E A F.schema) (projectionFamilyDomain E A G.schema),
      VFParametersPreserved e := by
  obtain ⟨h,hp⟩ := gamma_family_lifts_parameter_iso P A hA F.schema G.schema F.finite G.finite he
  let f := projectionFamilyIso E A hA F.schema
  let g := projectionFamilyIso E A hA G.schema
  let e := ((f.symm (gammaLogicInput B)).trans (gammaLogicInput B) h).trans (gammaLogicInput B) g
  refine ⟨e,?_⟩
  intro u j
  change vfAt (g.equiv (h.equiv (f.equiv.symm u))).val (Fin.castAdd (E.discarded+G.degree) j) = _
  exact (projectionFamilyIso_retained E A hA G.schema _ j).trans
    ((hp (f.equiv.symm u) (E.retainedIndex j)).trans
      (projectionFamilyIso_symm_retained E A hA F.schema u j))

theorem projectionFibreIntegral_independent (P : IntegrationContext B κ hs) (E : VFCoordinateProjection n p)
    (A : Set (Point (M := M) n 0)) (hA : GammaSetDefinable B A) (F G : DefinableRVFamily B A)
    (he : ∀ x : A, P.familyValue F x = P.familyValue G x) (x : E.baseImage A) :
    projectionFibreIntegral P E A hA F x = projectionFibreIntegral P E A hA G x := by
  obtain ⟨e,hp⟩ := projectionFamily_parameter_iso P E A hA F G he
  exact P.rowIntegral_iso _ _ (projectionFamily_definable E A hA F.schema) (projectionFamily_definable E A hA G.schema)
    (projectionFamily_finite E A hA F.schema F.finite) (projectionFamily_finite E A hA G.schema G.finite) e hp x.val.1

theorem projectionRepresentative_independent (P : IntegrationContext B κ hs) (E : VFCoordinateProjection n p)
    (A : Set (Point (M := M) n 0)) (hA : GammaSetDefinable B A) (F G : DefinableRVFamily B A)
    (he : ∀ x : A, P.familyValue F x = P.familyValue G x) :
    (Quotient.mk _ (projectionRepresentative P E A hA F) : P.Function (E.baseImage A)) =
      Quotient.mk _ (projectionRepresentative P E A hA G) := by
  apply Quotient.sound
  intro x
  exact (projectionRepresentative_value P E A hA F x).trans
    ((projectionFibreIntegral_independent P E A hA F G he x).trans
      (projectionRepresentative_value P E A hA G x).symm)

end IntegrationInACVF.Section6
