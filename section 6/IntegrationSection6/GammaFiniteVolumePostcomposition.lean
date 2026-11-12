import IntegrationSection6.GammaRVRealMapGraphs
import Section4.MapCorestrict
import Section4.FiniteMaps
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

def gammaFiniteVolumePostcompose (U : GammaRVFiniteObject B k)
    {A : @SpecialTransformations.DefinableGeometry.DefSet LRV M N (@rawRVSpace M N k) B.real}
    (F : @SpecialTransformations.DefinableGeometry.Map LRV M N _ _ B.real A (@SpecialTransformations.DefinableGeometry.DefSet.univ LRV M N (@rawRVSpace M N l) B.real))
    (hF : @SpecialTransformations.DefinableGeometry.Map.FiniteFibres LRV M N _ _ B.real A (@SpecialTransformations.DefinableGeometry.DefSet.univ LRV M N (@rawRVSpace M N l) B.real) F)
    (hA : ∀ u : rvObjectDomain U.object, (rvObjectVolume U.object u).val ∈
      @SpecialTransformations.DefinableGeometry.DefSet.carrier LRV M N _ B.real A) : GammaRVFiniteObject B l := by
  let T := @SpecialTransformations.DefinableGeometry.Map.extend LRV M N _ _ B.real U.codes A (@SpecialTransformations.DefinableGeometry.DefSet.univ LRV M N (@rawRVSpace M N l) B.real) F U.real_contains
  let G := @SpecialTransformations.DefinableGeometry.Map.corestrict LRV M N _ _ U.codes _ _
    (@SpecialTransformations.DefinableGeometry.DefSet.extend LRV M N _ B.real U.codes A U.real_contains)
    (rvObjectVolume U.object) hA
  let V := @RVObject.mk M N U.codes l (rvObjectArity U.object) (rvObjectDomain U.object)
    (@SpecialTransformations.DefinableGeometry.Map.comp LRV M N _ _ _ U.codes _ _ _ T G)
  have hG : @SpecialTransformations.DefinableGeometry.Map.FiniteFibres LRV M N _ _ U.codes _ _ G := by
    intro t
    apply (U.finite_volume ⟨t.val,Set.mem_univ _⟩).subset
    intro u hu
    have he := congrArg (fun v : A => v.val) hu
    exact Subtype.ext he
  refine {
    codes := U.codes
    real_contains := U.real_contains
    object := V
    domain_graph := U.domain_graph
    volume_graph := ?_
    finite_volume := @SpecialTransformations.DefinableGeometry.Map.FiniteFibres.comp LRV M N _ _ _ U.codes _ _ _ T G
      (@SpecialTransformations.DefinableGeometry.Map.FiniteFibres.extend LRV M N _ _ B.real U.codes A (@SpecialTransformations.DefinableGeometry.DefSet.univ LRV M N (@rawRVSpace M N l) B.real) F hF U.real_contains) hG }
  apply GammaGraphDefinable.congr ((gammaLogicInput B).comp_graph U.volume_graph (gamma_rv_graph_of_real_map F))
  intro p q
  constructor
  · rintro ⟨z,⟨u,hu,hz⟩,⟨v,hv,hq⟩⟩
    have he : v = ⟨(rvObjectVolume U.object u).val,hA u⟩ := Subtype.ext (hv.trans hz.symm)
    exact ⟨u,hu,(congrArg (fun v => (F v).val) he).symm.trans hq⟩
  · rintro ⟨u,hu,hq⟩
    exact ⟨(Fin.elim0,(rvObjectVolume U.object u).val),⟨u,hu,rfl⟩,⟨(rvObjectVolume U.object u).val,hA u⟩,rfl,hq⟩

end IntegrationInACVF.Section6
