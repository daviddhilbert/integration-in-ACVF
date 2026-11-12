import IntegrationSection6.FiniteGammaAmbientIsos
import IntegrationSection6.GammaRVGlobalRestriction

/-! Full original-Gamma graphs for ambient isomorphisms following an
explicit globally real-definable RV coordinate program. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
namespace IntegrationInACVF.Section6.FiniteRV
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

variable {B : Base (M := M)} {S : Set M} {n : ℕ}
local notation "N" => (@CanonicalStructure.normalize M sM)
local notation "hN" => (@CanonicalStructure.normalized_model M sM hM)

def GammaIsoAt.ofAmbientFormula {U V : GammaObjectAt B S n}
    (e : @CategoryTheory.Iso (@RVObject M N S n)
      (@SpecialTransformations.Section4.instCategoryRVObject M N S n) U.object.obj V.object.obj)
    (G : @SpecialTransformations.DefinableGeometry.Map LRV M N _ _ B.real
      (@SpecialTransformations.DefinableGeometry.DefSet.univ LRV M N (@rawRVSpace M N (rvObjectArity U.object.obj)) B.real)
      (@SpecialTransformations.DefinableGeometry.DefSet.univ LRV M N (@rawRVSpace M N (rvObjectArity V.object.obj)) B.real))
    (hF : ∀ a : rvObjectDomain U.object.obj,
      (@RVHom.map M N S n U.object.obj V.object.obj e.hom a).val = (G ⟨a.val,Set.mem_univ _⟩).val) : GammaIsoAt U V :=
  GammaIsoAt.ofAmbient e (gamma_rv_graph_of_global_formula
    (@RVHom.map M N S n U.object.obj V.object.obj e.hom) G U.domain_graph hF)

end IntegrationInACVF.Section6.FiniteRV
