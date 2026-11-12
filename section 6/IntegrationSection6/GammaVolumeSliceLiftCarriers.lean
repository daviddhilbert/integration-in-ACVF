import IntegrationSection6.GammaVolumeSliceSchemata
import IntegrationSection6.GammaFiniteGraphObjects

/-! The actual lift of a finite volume-slice presentation has the same
old RV labels and the unsliced VF volume, with the selected volume fixed. -/
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
variable {B : Base (M := M)} {e k : ℕ}
local notation "N" => (@CanonicalStructure.normalize M sM)
local notation "hN" => (@CanonicalStructure.normalized_model M sM hM)

theorem gammaVolumeSlicePresentation_lift (U : GammaRVFiniteObject B (e+k)) (t : Fin e → RV (M := M))
    (P : GammaFiniteGraphPresentation ⟨B.real ∪ Set.range (fun j => (t j).val),B.gamma⟩
      (rvObjectArity U.object) k ((gammaVolumeSliceSchema U).rowDomain (fun j => (t j).val))
      ((gammaVolumeSliceSchema U).rowVolume (fun j => (t j).val))) :
    P.toGamma.lift = {p : Point (M := M) k (rvObjectArity U.object) |
      ∃ u : rvObjectDomain U.object, u.val = p.2 ∧
        gammaVolumeValue U.toGammaRVObject u = Fin.append t (@tupleRV M N hN k p.1)} := by
  apply Set.ext
  intro p
  change (∃ v : P.domain, v.val = p.2 ∧ (P.volume v).val = @tupleRV M N hN k p.1) ↔ _
  constructor
  · intro hp
    have hRow := ((P.graph_iff p.2 (@tupleRV M N hN k p.1)).mp hp).2
    exact (gammaVolumeSliceSchema_volume U t p.2 _).mp hRow
  · intro hp
    have hRow := (gammaVolumeSliceSchema_volume U t p.2 _).mpr hp
    have hD := (GammaRelationFormula.graphSchema_row_domain (gammaVolumeSliceFormula U) _ p.2).mpr
      ⟨@tupleRV M N hN k p.1,hRow⟩
    exact (P.graph_iff p.2 _).mpr ⟨hD,hRow⟩

end IntegrationInACVF.Section6
