import IntegrationSection6.PullbackPartitions
import IntegrationSection6.FiniteGammaObjects

/-! Actual RV data of a mixed subset inherit finite volume fibres from
the RV data of its ambient set. Both RV arities are unchanged. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section4 SpecialTransformations.Section5
namespace IntegrationInACVF.Section6
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {S : Set M} {n a : ℕ}

theorem pullback_finite_of_subset {U D : DefSet (M := M) S n a}
    (hDU : carrier D ⊆ carrier U) (hUF : Map.FiniteFibres (rvObjectVolume (pullbackObject U))) :
    Map.FiniteFibres (rvObjectVolume (pullbackObject D)) := by
  have hDom := pullbackObject_domain_mono hDU
  let f : rvObjectDomain (pullbackObject D) → rvObjectDomain (pullbackObject U) := fun u => ⟨u.val,hDom u.property⟩
  intro t
  apply (hUF t).of_injOn (f := f)
  · intro u hu
    exact hu
  · intro u hu v hv he
    exact Subtype.ext (congrArg (fun z : rvObjectDomain (pullbackObject U) => z.val) he)

end IntegrationInACVF.Section6
