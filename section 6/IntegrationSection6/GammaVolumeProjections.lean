import IntegrationSection6.GammaRVRealSets
import IntegrationSection6.ElementaryKeys
import IntegrationSection6.GammaRVGlobalRestriction

/-! Coordinate projections of actual volume maps retain full original
Gamma graphs. Finiteness of the projected volume is a separate obligation;
no larger category is introduced as a public numbered target. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
namespace IntegrationInACVF.Section6
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {S : Set M} {k l : ℕ}
local notation "N" => (@CanonicalStructure.normalize M sM)

def volumeProjectionMap (U : RVObject (M := M) S k) (π : Fin l → Fin k) :=
  (@selectRVTuple M sM S k l π
    (@SpecialTransformations.DefinableGeometry.DefSet.univ LRV M sM (@SpecialTransformations.Section4.rawRVSpace M sM k) S)).comp U.volume

def gammaProjectVolumeObject (U : GammaRVObject B k) (π : Fin l → Fin k) : GammaRVObject B l where
  codes := U.codes
  real_contains := U.real_contains
  object := @RVObject.mk M N U.codes l (rvObjectArity U.object) (rvObjectDomain U.object)
    (@volumeProjectionMap M N U.codes k l U.object π)
  domain_graph := U.domain_graph
  volume_graph := by
    let G := @selectRVTuple M N U.codes k l π
      (@SpecialTransformations.DefinableGeometry.DefSet.univ LRV M N (@SpecialTransformations.Section4.rawRVSpace M N k) U.codes)
    let H := @selectRVTuple M N B.real k l π
      (@SpecialTransformations.DefinableGeometry.DefSet.univ LRV M N (@SpecialTransformations.Section4.rawRVSpace M N k) B.real)
    have hG := gamma_rv_graph_of_global_formula G H
      (gamma_rv_set_of_real
        (@SpecialTransformations.DefinableGeometry.DefSet.univ LRV M N (@SpecialTransformations.Section4.rawRVSpace M N k) B.real))
      (fun _ => rfl)
    apply GammaGraphDefinable.congr ((gammaLogicInput B).comp_graph U.volume_graph hG)
    intro p q
    constructor
    · rintro ⟨z,⟨u,hu,hz⟩,⟨v,hv,hq⟩⟩
      have he : v = rvObjectVolume U.object u := Subtype.ext (hv.trans hz.symm)
      refine ⟨u,hu,?_⟩
      change (G (rvObjectVolume U.object u)).val = q.2
      rw [← he]
      exact hq
    · rintro ⟨u,hu,hq⟩
      exact ⟨(Fin.elim0,(rvObjectVolume U.object u).val),⟨u,hu,rfl⟩,rvObjectVolume U.object u,rfl,hq⟩

@[simp] theorem gammaProjectVolumeObject_value (U : GammaRVObject B k) (π : Fin l → Fin k)
    (u : rvObjectDomain U.object) :
    (rvObjectVolume (gammaProjectVolumeObject U π).object u).val =
      fun j => (rvObjectVolume U.object u).val (π j) := rfl

end IntegrationInACVF.Section6
