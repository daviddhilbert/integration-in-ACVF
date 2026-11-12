import IntegrationSection6.FiniteGammaScissorPartitions
import IntegrationSection6.FiniteGammaLocusBlowups

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5 SpecialTransformations.Section7
namespace IntegrationInACVF.Section6.FiniteRV
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {S : Set M} {k : ℕ}
local notation "N" => (@CanonicalStructure.normalize M sM)
local notation "hN" => (@CanonicalStructure.normalized_model M sM hM)

theorem gammaFiniteScissorClass_coprod (U V : GammaObjectAt B S k) :
    gammaFiniteScissorClass (gammaCoprodAt U V).toGamma =
      gammaFiniteScissorClass U.toGamma + gammaFiniteScissorClass V.toGamma := by
  have h := gammaFiniteScissorClass_partition (gammaCoprodAt U V) (gammaLeftLocus U V)
    (fun _ h => Or.inl h)
    (gamma_rv_map_image (@rvLeftTagMap M N hN S (rvObjectArity U.object.obj)
      (rvObjectDomain U.object.obj) (rvObjectArity V.object.obj))
      (gamma_leftTag_graph U (rvObjectArity V.object.obj)))
  rw [← gammaFiniteScissorClass_iso (gammaLeftRestrictionIsoAt U V).toGamma,
    ← gammaFiniteScissorClass_iso (gammaCoprodComplementIsoAt U V).toGamma] at h
  exact h.symm

end IntegrationInACVF.Section6.FiniteRV
