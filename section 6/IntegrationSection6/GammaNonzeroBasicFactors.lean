import IntegrationSection6.GammaWeightDecomposition
import IntegrationSection6.FiniteGammaBasicRelation
import IntegrationSection6.FiniteGammaFormulaIsos
import IntegrationSection6.GammaCompressionIsomorphisms
import IntegrationSection6.FiniteGammaPartitionCharts
import IntegrationSection6.FiniteGammaAmbientIsos
import Section4.RVPaddingSplit
import IntegrationSection6.GammaWeightStrata
import Section4.RVFinitePadding
import IntegrationSection6.FiniteGammaIsoLaws

/-! Original-Gamma RV[k] data at a fixed internal real presentation.
The parameter set S describes codes only; every domain and volume graph
is still certified over the original Base B. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
namespace IntegrationInACVF.Section6.FiniteRV
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

variable {B : Base (M := M)} {S : Set M} {n : ℕ}
local notation "N" => (@CanonicalStructure.normalize M sM)
local notation "hN" => (@CanonicalStructure.normalized_model M sM hM)

def gammaPositiveZeroIsoUnitAt (hBS : B.real ⊆ S) :
    GammaIsoAt (gammaWeightProjectionAt (gammaPositiveAt hBS)) (gammaUnitAt hBS) := by
  let A := gammaWeightProjectionAt (gammaPositiveAt hBS)
  let Q := gammaUnitAt hBS
  let F := @selectRVTuple M N S 1 0 Fin.elim0 (rvObjectDomain A.object.obj)
  have hz (u : rvObjectDomain A.object.obj) : u.val = (fun _ : Fin 1 => (0 : CanonicalRV.RVSort M)) := by
    have hu : ∃ v : @positiveRV M N S, v.val = u.val ∧ ∃ i : Fin 1, (v.val i).val = @iRVZero M N := u.property
    obtain ⟨v,hv,i,hi⟩ := hu
    funext j
    apply Subtype.ext
    have he : (show Fin 1 from j) = i := Subsingleton.elim _ _
    exact ((congrArg (fun t => (t j).val) hv).symm.trans (he.symm ▸ hi)).trans ((@CanonicalStructure.sortZero_normalize M sM .rv).trans (@RVOperations.zero_val M sM hM).symm)
  have hF : Function.Bijective F := by
    constructor
    · intro u v _
      exact Subtype.ext ((hz u).trans (hz v).symm)
    · intro q
      let z : @positiveRV M N S := by
        letI : LRV.Structure M := N
        letI : M ⊨ Axioms.ACVF := hN
        exact ⟨fun _ => 0,zero_mem_positiveRV⟩
      let u : rvObjectDomain A.object.obj := ⟨z.val,⟨z,rfl,⟨0,@RVOperations.zero_val M N hN⟩⟩⟩
      exact ⟨u,Subtype.ext (funext (fun i : Fin 0 => i.elim0))⟩
  have hΓ := gamma_rv_graph_of_global_formula F
    (@selectRVTuple M N B.real 1 0 Fin.elim0
      (@SpecialTransformations.DefinableGeometry.DefSet.univ LRV M N (@rawRVSpace M N 1) B.real)) A.domain_graph (fun _ => rfl)
  exact {
    iso := @isoOfDefinableBijection M N S 0 A.object Q.object F hF (fun _ => rfl)
    graph := hΓ }

theorem gammaOneAt_fullWeight (hBS : B.real ⊆ S) : GammaFullWeightAt (gammaOneAt hBS) := by
  apply (gammaFullWeightAt_iff_nonzero _).mpr
  intro u i
  letI : LRV.Structure M := N
  letI : M ⊨ Axioms.ACVF := hN
  change (1 : CanonicalRV.RVSort M).val ≠ iRVZero
  rw [RVOperations.one_val]
  exact RVCalc.rv_one_ne_zero hN

end IntegrationInACVF.Section6.FiniteRV
