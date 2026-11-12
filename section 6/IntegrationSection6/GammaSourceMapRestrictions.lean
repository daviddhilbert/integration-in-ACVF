import IntegrationSection5.RelativeSpecialRestriction
import IntegrationSection5.GammaGraphOperations

/-! Complete original-Gamma graphs for actual source restrictions, with
codomain the literal point image. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section5
open IntegrationInACVF.Section5
namespace IntegrationInACVF.Section6
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {S : Set M} {B : Base (M := M)} {n a b : ℕ}
variable {U : DefSet (M := M) S n a} {V : DefSet (M := M) S n b}

theorem gamma_restrictPointMap (f : Map U V) (A : DefSet (M := M) S n a) (hAU : carrier A ⊆ carrier U)
    (hA : GammaSetDefinable B (carrier A)) (hF : GammaGraphDefinable B (pointMapGraph f)) :
    GammaGraphDefinable B (pointMapGraph (restrictPointMap f A hAU)) := by
  apply GammaGraphDefinable.congr ((gammaLogicInput B).restrict_graph hA hF)
  intro p q
  constructor
  · rintro ⟨hp,u,hu,hq⟩
    let a : A := ⟨p,hp⟩
    refine ⟨a,rfl,?_⟩
    have he : (⟨a.val,hAU a.property⟩ : U) = u := Subtype.ext hu.symm
    exact (congrArg (fun v : U => (f v).val) he).trans hq
  · rintro ⟨a,ha,hq⟩
    exact ⟨ha ▸ a.property,⟨a.val,hAU a.property⟩,ha,hq⟩

theorem restrictPointMap_bijective (f : Map U V) (hf : Function.Injective f)
    (A : DefSet (M := M) S n a) (hAU : carrier A ⊆ carrier U) :
    Function.Bijective (restrictPointMap f A hAU) := by
  constructor
  · intro a b he
    have hv := congrArg (fun q : restrictPointImage f A hAU => q.val) he
    exact Subtype.ext (congrArg (fun u : U => u.val) (hf (Subtype.ext hv)))
  · rintro ⟨q,a,ha⟩
    exact ⟨a,Subtype.ext ha⟩

end IntegrationInACVF.Section6
