import Integration7.CompletedSection6Kernel
import Integration7.ClosedSection6GammaMixedParameterUniformity
import Integration7.ClosedSection6IntegrationContexts
import Integration7.ClosedSection6DefinableFamilyIntegration
import IntegrationSection6.DefinableFamilyParameterIsomorphisms
import IntegrationSection6.GammaMixedParameterUniformity
import IntegrationSection6.IntegrationContexts
import IntegrationSection6.DefinableFamilyIntegration

/-! Closed generated-base Section6 integration. The former universal
Section5 input is replaced by the canonical-model certificate; its kernel
uses the proved generated-base contraction comparison. Original finite
objects, actual lifting, scissor addition and Cartesian products are retained.
This module keeps the dependent data and consumers in one coherent interface. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
open IntegrationInACVF.Section6 IntegrationInACVF.Section6.FiniteRV
namespace IntegrationInACVF.Section7.CompletedSection6
open FiniteRV
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {κ : Cardinal} {hs : Saturated M κ} {p a b k l : ℕ}

theorem gamma_family_lifts_parameter_iso (P : IntegrationContext B κ hs)
    (A : Set (Point (M := M) p 0)) (hA : GammaSetDefinable B A)
    (F : GammaFiniteRVSchema B p a k) (G : GammaFiniteRVSchema B p b l)
    (hF : ∀ x : A, F.finiteRow (fun j => (x.val.1 j).val))
    (hG : ∀ x : A, G.finiteRow (fun j => (x.val.1 j).val))
    (he : ∀ x : A,
      schemaRowCoefficient P.countable_le hs P.characteristic P.real_small P.gamma_small P.field_base P.generated
          P.value P.value_mem P.value_large P.canonical F x.val.1 (hF x) =
        schemaRowCoefficient P.countable_le hs P.characteristic P.real_small P.gamma_small P.field_base P.generated
          P.value P.value_mem P.value_large P.canonical G x.val.1 (hG x)) :
    ∃ e : GammaIso B (familyLiftDomain A F) (familyLiftDomain A G), VFParametersPreserved e := by
  apply gamma_mixed_fibre_uniformity P.countable_le hs P.real_small P.gamma_small A hA
    (familyLiftDomain A F) (familyLiftDomain A G)
    (gamma_family_lift_definable A hA F) (gamma_family_lift_definable A hA G)
    (fun q hq => hq.1) (fun q hq => hq.1)
  intro x
  obtain ⟨e⟩ := (schemaRowCoefficient_eq_iff P.countable_le hs P.characteristic P.real_small P.gamma_small
    P.field_base P.generated P.value P.value_mem P.value_large P.canonical F G x.val.1 (hF x) (hG x)).mp (he x)
  exact ⟨e.congr (familyLiftDomain_fibre A F x).symm (familyLiftDomain_fibre A G x).symm⟩

end IntegrationInACVF.Section7.CompletedSection6
