import IntegrationSection6.DefinableFamilyLifts
import IntegrationSection6.GammaSchemaFiniteRowPresentations
import IntegrationSection6.VFParameterCoefficientBases
import IntegrationSection6.GammaClosureIsomorphisms

/-! Each finite family row is an actual RV[k] object over dcl(B,x).
Its lift is exactly the fibre used by the literal total family lift. -/
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
namespace IntegrationInACVF.Section6
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

end IntegrationInACVF.Section6
