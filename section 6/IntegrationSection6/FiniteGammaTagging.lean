import IntegrationSection6.FiniteGammaObjects
import IntegrationSection6.GammaRVGlobalRestriction

/-! The actual two RV tags have full original-Gamma graphs. They add only
the existing named RV zero and one, with finite tuple padding. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
namespace IntegrationInACVF.Section6.FiniteRV
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

variable {B : Base (M := M)} {S : Set M} {n : ℕ}
local notation "N" => (@CanonicalStructure.normalize M sM)
local notation "hN" => (@CanonicalStructure.normalized_model M sM hM)

theorem gamma_leftTag_graph (U : GammaObjectAt B S n) (r : ℕ) :
    GammaGraphDefinable B
      (fun (p : Point (M := M) 0 (rvObjectArity U.object.obj))
        (q : Point (M := M) 0 (1+(rvObjectArity U.object.obj+r))) =>
        ∃ u : rvObjectDomain U.object.obj, u.val = p.2 ∧
          @rvLeftTag M N hN (rvObjectArity U.object.obj) r u.val = q.2) := by
  apply gamma_rv_graph_of_global_formula
    (@rvLeftTagMap M N hN S (rvObjectArity U.object.obj) (rvObjectDomain U.object.obj) r)
    (@rvLeftTagMap M N hN B.real (rvObjectArity U.object.obj)
      (@SpecialTransformations.DefinableGeometry.DefSet.univ LRV M N
        (@SpecialTransformations.Section4.rawRVSpace M N (rvObjectArity U.object.obj)) B.real) r)
    U.domain_graph
  intro u
  rfl

theorem gamma_rightTag_graph (U : GammaObjectAt B S n) (r : ℕ) :
    GammaGraphDefinable B
      (fun (p : Point (M := M) 0 (rvObjectArity U.object.obj))
        (q : Point (M := M) 0 (1+(r+rvObjectArity U.object.obj))) =>
        ∃ u : rvObjectDomain U.object.obj, u.val = p.2 ∧
          @rvRightTag M N hN (rvObjectArity U.object.obj) r u.val = q.2) := by
  apply gamma_rv_graph_of_global_formula
    (@rvRightTagMap M N hN S (rvObjectArity U.object.obj) (rvObjectDomain U.object.obj) r)
    (@rvRightTagMap M N hN B.real (rvObjectArity U.object.obj)
      (@SpecialTransformations.DefinableGeometry.DefSet.univ LRV M N
        (@SpecialTransformations.Section4.rawRVSpace M N (rvObjectArity U.object.obj)) B.real) r)
    U.domain_graph
  intro u
  rfl

end IntegrationInACVF.Section6.FiniteRV
