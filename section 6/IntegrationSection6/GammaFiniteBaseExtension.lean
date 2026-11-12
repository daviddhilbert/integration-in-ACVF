import IntegrationSection6.FiniteGammaObjects

/-! Enlarge the mathematical definition base and the internal real code
presentation separately. Existing full Gamma graphs extend monotonically;
no cardinal bound is imposed on the internal code set. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
namespace IntegrationInACVF.Section6
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B C : Base (M := M)} {n : ℕ}

def gammaFiniteBaseExtension (U : GammaRVFiniteObject B n)
    (hR : B.real ⊆ C.real) (hG : B.gamma ⊆ C.gamma) : GammaRVFiniteObject C n := by
  let V := FiniteRV.gammaObjectAtExtend U (Set.subset_union_left : U.codes ⊆ U.codes ∪ C.real)
  exact {
    codes := U.codes ∪ C.real
    real_contains := Set.subset_union_right
    object := V.object.obj
    domain_graph := U.domain_graph.mono hR hG
    volume_graph := U.volume_graph.mono hR hG
    finite_volume := V.object.property }

end IntegrationInACVF.Section6
