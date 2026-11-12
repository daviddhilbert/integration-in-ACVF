import IntegrationSection6.FiniteGammaFormulaIsos
import Section4.RVReindexing

/-! Finite volume-coordinate reindexing with original-Gamma graphs.
The internal real code presentation remains arbitrary. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
namespace IntegrationInACVF.Section6.FiniteRV
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {S : Set M} {k l : ℕ}
local notation "N" => (@CanonicalStructure.normalize M sM)

def GammaObjectAt.reindexVolume (U : GammaObjectAt B S k) (e : Fin l ≃ Fin k) : GammaObjectAt B S l where
  object := ⟨@RVObject.reindexVolume M N S l k U.object.obj e,by
    intro t
    apply (U.object.property ⟨t.val ∘ e.symm,Set.mem_univ _⟩).subset
    intro u hu
    apply Subtype.ext
    funext j
    have h := congrFun (congrArg Subtype.val hu) (e.symm j)
    change (@RVObject.value M N S k U.object.obj u) (e (e.symm j)) = t.val (e.symm j) at h
    change (@RVObject.value M N S k U.object.obj u) j = t.val (e.symm j)
    rw [e.apply_symm_apply] at h
    exact h⟩
  real_contains := U.real_contains
  domain_graph := U.domain_graph
  volume_graph := by
    have h := U.volume_graph.preimage_maps
      (Map.id (PresentedSet.univ (pointSpace (M := M) 0 (rvObjectArity U.object.obj)) B.real))
      (rvCoordinatePointMap e.symm B.real)
    apply GammaGraphDefinable.congr h
    intro p q
    constructor
    · rintro ⟨u,hu,hv⟩
      refine ⟨u,hu,?_⟩
      funext j
      change (rvObjectVolume U.object.obj u).val (e j) = q.2 j
      exact (congrFun hv (e j)).trans (congrArg q.2 (e.symm_apply_apply j))
    · rintro ⟨u,hu,hv⟩
      refine ⟨u,hu,?_⟩
      funext j
      have hh := congrFun hv (e.symm j)
      change (rvObjectVolume U.object.obj u).val (e (e.symm j)) = q.2 (e.symm j) at hh
      change (rvObjectVolume U.object.obj u).val j = q.2 (e.symm j)
      rw [e.apply_symm_apply] at hh
      exact hh


def gammaReindexVolumeIsoAt (U : GammaObjectAt B S k) (e : Equiv.Perm (Fin k)) :
    GammaIsoAt U (U.reindexVolume e) :=
  GammaIsoAt.ofAmbientFormula (@rvReindexVolumeIso M N S k U.object.obj e)
    (@SpecialTransformations.DefinableGeometry.Map.id LRV M N _ B.real
      (@SpecialTransformations.DefinableGeometry.DefSet.univ LRV M N
        (@SpecialTransformations.Section4.rawRVSpace M N (rvObjectArity U.object.obj)) B.real)) (fun _ => rfl)

end IntegrationInACVF.Section6.FiniteRV
