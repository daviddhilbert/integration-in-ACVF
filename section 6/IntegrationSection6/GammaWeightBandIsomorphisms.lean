import IntegrationSection6.GammaWeightSeparation
import IntegrationSection6.GammaFiniteRestrictionIsomorphisms
import IntegrationSection6.FiniteGammaLocusBlowups
import IntegrationSection6.GammaWeightStrata
import Mathlib.Algebra.DirectSum.Ring

/-! The graded semiring of actual original-Gamma RV[k] isomorphism
classes. This follows the pinned RVHomogeneousProducts/RVGradedSemiring
construction, using the finite Gamma structural maps proved here. -/
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

theorem gammaIsoAt_weight_bands {n : ℕ} (U V C D : GammaObjectAt B S (n+1))
    (hU : @rvLowWeightProperty M N S n U.object.obj) (hV : GammaFullWeightAt V)
    (hC : @rvLowWeightProperty M N S n C.object.obj) (hD : GammaFullWeightAt D)
    (e : GammaIsoAt (gammaCoprodAt U V) (gammaCoprodAt C D)) :
    Nonempty (GammaIsoAt U C) ∧ Nonempty (GammaIsoAt V D) := by
  let A := gammaCoprodAt U V
  let Z := gammaCoprodAt C D
  let L := gammaLeftLocus U V
  let R := gammaLeftLocus C D
  have hL := (gammaLeftRestrictionIsoAt U V).graph
  have hR := (gammaLeftRestrictionIsoAt C D).graph
  have hLΓ := gamma_rv_map_image (@rvLeftTagMap M N (@CanonicalStructure.normalized_model M sM hM) S
    (rvObjectArity U.object.obj) (rvObjectDomain U.object.obj) (rvObjectArity V.object.obj)) (gamma_leftTag_graph U (rvObjectArity V.object.obj))
  have hRΓ := gamma_rv_map_image (@rvLeftTagMap M N (@CanonicalStructure.normalized_model M sM hM) S
    (rvObjectArity C.object.obj) (rvObjectDomain C.object.obj) (rvObjectArity D.object.obj)) (gamma_leftTag_graph C (rvObjectArity D.object.obj))
  have hc (u : rvObjectDomain A.object.obj) : u.val ∈ carrier L ↔ (isoAtMap e.iso u).val ∈ carrier R := by
    rw [gammaLeftLocus_mem_iff_low U V hU hV,gammaLeftLocus_mem_iff_low C D hC hD]
    rw [gammaIsoAt_normalized_weight e u]
  let el := gammaRestrictIsoAt e L R (fun _ h => Or.inl h) (fun _ h => Or.inl h) hLΓ hRΓ hc
  have hcomp (u : rvObjectDomain A.object.obj) :
      u.val ∈ carrier (@complement M N S (n+1) A.object.obj L) ↔
        (isoAtMap e.iso u).val ∈ carrier (@complement M N S (n+1) Z.object.obj R) := by
    change (_ ∧ ¬ _) ↔ (_ ∧ ¬ _)
    exact and_congr (iff_of_true u.property (isoAtMap e.iso u).property) (not_congr (hc u))
  let er := gammaRestrictIsoAt e (@complement M N S (n+1) A.object.obj L) (@complement M N S (n+1) Z.object.obj R)
    (@complement_subset M N (@CanonicalStructure.normalized_model M sM hM) S (n+1) A.object.obj L)
    (@complement_subset M N (@CanonicalStructure.normalized_model M sM hM) S (n+1) Z.object.obj R)
    ((gammaLogicInput B).sdiff A.domain_graph hLΓ) ((gammaLogicInput B).sdiff Z.domain_graph hRΓ) hcomp
  exact ⟨⟨((gammaLeftRestrictionIsoAt U V).trans el).trans (gammaLeftRestrictionIsoAt C D).symm⟩,
    ⟨((gammaCoprodComplementIsoAt U V).trans er).trans (gammaCoprodComplementIsoAt C D).symm⟩⟩

end IntegrationInACVF.Section6.FiniteRV
