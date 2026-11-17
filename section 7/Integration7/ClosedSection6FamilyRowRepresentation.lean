module

public import Integration7.CompletedSection6Kernel
public import Integration7.ClosedSection6DefinableFamilyRowObjects
public import Integration7.ClosedSection6IntegrationContexts
public import Integration7.ClosedSection6DefinableFamilyCoefficients
public import IntegrationSection6.FamilyRowRepresentation
public import IntegrationSection6.DefinableFamilyRowObjects
public import IntegrationSection6.GammaSchemaNativeRows
public import IntegrationSection6.IntegrationContexts
public import IntegrationSection6.DefinableFamilyCoefficients

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

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
open SpecialTransformations.Section4 SpecialTransformations.Section5 SpecialTransformations.Section7
open IntegrationInACVF.Section6 IntegrationInACVF.Section6.FiniteRV
namespace IntegrationInACVF.Section7.CompletedSection6
open FiniteRV
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {p a k : ℕ}
local notation "N" => (@CanonicalStructure.normalize M sM)
local notation "hN" => (@CanonicalStructure.normalized_model M sM hM)

theorem schemaRowObject_represents (F : GammaFiniteRVSchema B p a k) (x : Fin p → VF (M := M))
    (hx : F.finiteRow (fun j => (x j).val)) :
    gammaSchemaRepresents (schemaRowObject F x hx).toGamma F (fun j => (x j).val) := by
  apply gammaSchemaRepresents_of_typed
  · intro r
    exact Iff.of_eq (congrArg (fun D => r ∈ D) (schemaRowPresentation F x hx).domain_eq.symm)
  · intro r v
    exact ⟨fun h => ((schemaRowPresentation F x hx).graph_iff r v).mpr ⟨hx.2.1 _ _ h,h⟩,
      fun h => (((schemaRowPresentation F x hx).graph_iff r v).mp h).2⟩

theorem gammaSchemaRepresents_lift {C : Base (M := M)} (U : GammaRVFiniteObject C k)
    (F : GammaFiniteRVSchema B p (rvObjectArity U.object) k) (x : Fin p → VF (M := M))
    (hr : gammaSchemaRepresents U F (fun j => (x j).val)) :
    U.lift = schemaRowLift F x := by
  ext q
  change (∃ u : rvObjectDomain U.object, u.val = q.2 ∧ (rvObjectVolume U.object u).val = @tupleRV M N hN k q.1) ↔ _
  rw [normalized_tupleRV]
  exact (gammaSchemaRepresents_volume U F (fun j => (x j).val) hr q.2 (tupleRV q.1)).symm

theorem schemaRowCoefficient_of_represents {κ : Cardinal} {hs : Saturated M κ}
    (P : IntegrationContext B κ hs) (x : Fin p → VF (M := M))
    (U : GammaObjectAt (vfParameterCoefficientBase B x) Set.univ k)
    (F : GammaFiniteRVSchema B p (rvObjectArity U.object.obj) k)
    (hx : F.finiteRow (fun j => (x j).val))
    (hr : gammaSchemaRepresents U.toGamma F (fun j => (x j).val)) :
    schemaRowCoefficient P.countable_le hs P.characteristic P.real_small P.gamma_small P.field_base P.generated
        P.value P.value_mem P.value_large P.canonical F x hx =
      parameterRVClass P.countable_le hs P.characteristic P.real_small P.gamma_small P.field_base P.generated
        P.value P.value_mem P.value_large P.canonical x U.toGamma := by
  apply (parameterRVClass_eq_iff_liftIso P.countable_le hs P.characteristic P.real_small P.gamma_small P.field_base
    P.generated P.value P.value_mem P.value_large P.canonical x (schemaRowObject F x hx) U).mpr
  exact ⟨(gammaIso_reflexive U.toGamma.lift U.toGamma.toGammaRVObject.lift_definable).congr
    ((gammaSchemaRepresents_lift U.toGamma F x hr).trans (schemaRowObject_lift F x hx).symm) rfl⟩

end IntegrationInACVF.Section7.CompletedSection6
