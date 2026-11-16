module

public import Integration7.CompletedSection6Kernel
public import Integration7.ClosedSection6DefinableFamilyLifts
public import IntegrationSection6.DefinableFamilyRowObjects
public import IntegrationSection6.DefinableFamilyLifts
public import IntegrationSection6.GammaSchemaFiniteRowPresentations
public import IntegrationSection6.VFParameterCoefficientBases
public import IntegrationSection6.GammaClosureIsomorphisms

@[expose] public section

/-! Closed generated-base Section6 integration. The former universal
Section5 input is replaced by the canonical-model certificate; its kernel
uses the proved generated-base contraction comparison. Original finite
objects, actual lifting, scissor addition and Cartesian products are retained.
This module keeps the dependent data and consumers in one coherent interface. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.DefinableGeometry.Space.prod
  SpecialTransformations.Section4.rawRVSpace SpecialTransformations.Section4.vfSpace
  SpecialTransformations.Section4.rvSpace SpecialTransformations.Section4.realSpace
  SpecialTransformations.Milestone0.sortEval SpecialTransformations.DefinableGeometry.Space.ofEmbedding
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5 SpecialTransformations.Section7
open IntegrationInACVF.Section6 IntegrationInACVF.Section6.FiniteRV
namespace IntegrationInACVF.Section7.CompletedSection6
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {p a k : ℕ}
local notation "N" => (@CanonicalStructure.normalize M sM)
local notation "hN" => (@CanonicalStructure.normalized_model M sM hM)

def schemaRowPresentation (F : GammaFiniteRVSchema B p a k) (x : Fin p → VF (M := M))
    (hx : F.finiteRow (fun j => (x j).val)) :
    GammaFiniteGraphPresentation ⟨B.real ∪ Set.range (fun j => (x j).val),B.gamma⟩ a k
      (F.rowDomain (fun j => (x j).val)) (F.rowVolume (fun j => (x j).val)) :=
  Classical.choice (F.realize_finiteRow (fun j => (x j).val) (fun j => (x j).property) hx)

def schemaRowObject (F : GammaFiniteRVSchema B p a k) (x : Fin p → VF (M := M))
    (hx : F.finiteRow (fun j => (x j).val)) : FiniteRV.GammaObjectAt (vfParameterCoefficientBase B x) Set.univ k where
  object := (FiniteRV.gammaUniversalObject (schemaRowPresentation F x hx).toGamma).object
  real_contains := Set.subset_univ _
  domain_graph := (schemaRowPresentation F x hx).toGamma.domain_graph.mono
    (subset_closureBase (⟨B.real ∪ Set.range (fun j => (x j).val),B.gamma⟩ : Base (M := M))).1
    (subset_closureBase (⟨B.real ∪ Set.range (fun j => (x j).val),B.gamma⟩ : Base (M := M))).2
  volume_graph := (schemaRowPresentation F x hx).toGamma.volume_graph.mono
    (subset_closureBase (⟨B.real ∪ Set.range (fun j => (x j).val),B.gamma⟩ : Base (M := M))).1
    (subset_closureBase (⟨B.real ∪ Set.range (fun j => (x j).val),B.gamma⟩ : Base (M := M))).2

theorem schemaRowObject_lift (F : GammaFiniteRVSchema B p a k) (x : Fin p → VF (M := M))
    (hx : F.finiteRow (fun j => (x j).val)) :
    (schemaRowObject F x hx).toGamma.lift =
      {q : Point (M := M) k a | F.rowVolume (fun j => (x j).val) q.2 (tupleRV q.1)} := by
  let P := schemaRowPresentation F x hx
  ext q
  change (∃ u : P.domain, u.val = q.2 ∧ (P.volume u).val = @tupleRV M N hN k q.1) ↔ _
  rw [normalized_tupleRV]
  constructor
  · intro h
    exact ((P.graph_iff q.2 (@tupleRV M sM hM k q.1)).mp h).2
  · intro h
    exact (P.graph_iff q.2 (@tupleRV M sM hM k q.1)).mpr ⟨hx.2.1 _ _ h,h⟩

end IntegrationInACVF.Section7.CompletedSection6
