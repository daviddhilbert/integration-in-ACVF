import IntegrationSection6.GammaFamilyCoordinates
import IntegrationSection6.MixedCoordinatePointMaps
import IntegrationSection6.DefinableFamilyRowObjects
import IntegrationSection6.FamilyRowRepresentation

/-! A finite RV object defines a constant family over every VF parameter
space. The original Gamma graphs, rather than its internal codes, control
this construction. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
namespace IntegrationInACVF.Section6
open FiniteRV
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {k p : ℕ}
local notation "N" => (@CanonicalStructure.normalize M sM)

def constantRVFormula (U : GammaObjectAt B Set.univ k) (p : ℕ) :
    GammaRVFamilyFormula B p (rvObjectArity U.object.obj) k where
  domain := {q | q.2 ∈ @SpecialTransformations.DefinableGeometry.DefSet.carrier LRV M N _ _ (rvObjectDomain U.object.obj)}
  domain_definable := gamma_global_preimage
    (mixedCoordinatePointMap (Fin.elim0 : Fin 0 → Fin p) (Equiv.refl _) B.real) U.domain_graph
  volume := fun q v => ∃ u : rvObjectDomain U.object.obj, u.val = q.2 ∧ (rvObjectVolume U.object.obj u).val = v.2
  volume_definable := U.volume_graph.preimage_maps
    (mixedCoordinatePointMap (Fin.elim0 : Fin 0 → Fin p) (Equiv.refl _) B.real)
    (mixedCoordinatePointMap (Fin.elim0 : Fin 0 → Fin 0) (Equiv.refl _) B.real)

def constantRVSchema (U : GammaObjectAt B Set.univ k) (p : ℕ) := (constantRVFormula U p).schema 0

theorem constantRVSchema_domain (U : GammaObjectAt B Set.univ k) (x : Fin p → VF (M := M))
    (r : Fin (rvObjectArity U.object.obj) → RV (M := M)) :
    r ∈ (constantRVSchema U p).rowDomain (fun j => (x j).val) ↔
      r ∈ @SpecialTransformations.DefinableGeometry.DefSet.carrier LRV M N _ _ (rvObjectDomain U.object.obj) :=
  (constantRVFormula U p).schema_domain 0 (x,r)

theorem constantRVSchema_volume (U : GammaObjectAt B Set.univ k) (x : Fin p → VF (M := M))
    (r : Fin (rvObjectArity U.object.obj) → RV (M := M)) (v : Fin k → RV (M := M)) :
    (constantRVSchema U p).rowVolume (fun j => (x j).val) r v ↔
      ∃ u : rvObjectDomain U.object.obj, u.val = r ∧ (rvObjectVolume U.object.obj u).val = v :=
  (constantRVFormula U p).schema_volume 0 (x,r) (Fin.elim0,v)

theorem constantRVSchema_finite (U : GammaObjectAt B Set.univ k) (x : Fin p → VF (M := M)) :
    (constantRVSchema U p).finiteRow (fun j => (x j).val) := by
  refine ⟨?_,?_,?_⟩
  · intro r hr
    let u : rvObjectDomain U.object.obj := ⟨r,(constantRVSchema_domain U x r).mp hr⟩
    refine ⟨(rvObjectVolume U.object.obj u).val,(constantRVSchema_volume U x r _).mpr ⟨u,rfl,rfl⟩,?_⟩
    intro v hv
    obtain ⟨w,hw,hwv⟩ := (constantRVSchema_volume U x r v).mp hv
    have he : w = u := Subtype.ext hw
    exact (he ▸ hwv).symm
  · intro r v hv
    obtain ⟨u,hu,_⟩ := (constantRVSchema_volume U x r v).mp hv
    exact (constantRVSchema_domain U x r).mpr (hu ▸ u.property)
  · intro v
    apply ((U.object.property ⟨v,Set.mem_univ _⟩).image (fun u : rvObjectDomain U.object.obj => u.val)).subset
    intro r hr
    obtain ⟨u,hu,huv⟩ := (constantRVSchema_volume U x r v).mp hr
    exact ⟨u,Subtype.ext huv,hu⟩

end IntegrationInACVF.Section6
