import IntegrationSection6.GammaFiniteGraphObjects
import IntegrationSection6.GammaNativeRawObjects

/-! Every actual finite Gamma RV object admits a presentation adding only
finitely many proper representatives. Its existing internal code set need
not be small or a finite extension of the original real base. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.DefinableGeometry.Space.prod
  SpecialTransformations.Section4.rawRVSpace SpecialTransformations.Section4.vfSpace
  SpecialTransformations.Section4.rvSpace SpecialTransformations.Section4.realSpace
  SpecialTransformations.Milestone0.sortEval SpecialTransformations.DefinableGeometry.Space.ofEmbedding
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5 SpecialTransformations.Section7
namespace IntegrationInACVF.Section6
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {k : ℕ}

def gammaFiniteObjectRelation (U : GammaRVFiniteObject B k)
    (x : Fin (rvObjectArity U.object) → RV (M := M)) (y : Fin k → RV (M := M)) : Prop :=
  ∃ u : rvObjectDomain U.object, u.val = x ∧ gammaVolumeValue U.toGammaRVObject u = y

theorem gammaFiniteObjectPresentation_exists (U : GammaRVFiniteObject B k) :
    Nonempty (GammaFiniteGraphPresentation B (rvObjectArity U.object) k
      (@SpecialTransformations.DefinableGeometry.DefSet.carrier LRV M
        (@CanonicalStructure.normalize M sM) _ U.codes (rvObjectDomain U.object)) (gammaFiniteObjectRelation U)) := by
  apply exists_gammaFiniteGraphPresentation U.domain_graph U.volume_graph
  · intro x
    let u : rvObjectDomain U.object := ⟨x.val,x.property⟩
    refine ⟨gammaVolumeValue U.toGammaRVObject u,⟨u,rfl,rfl⟩,?_⟩
    intro y hy
    obtain ⟨v,hv,hy⟩ := hy
    have he : v = u := Subtype.ext hv
    exact hy.symm.trans (congrArg (gammaVolumeValue U.toGammaRVObject) he)
  · intro y
    have h := U.finite_volume ⟨y,Set.mem_univ _⟩
    apply h.subset
    intro x hx
    obtain ⟨v,hv,hy⟩ := hx
    have he : v = x := Subtype.ext hv
    apply Subtype.ext
    exact (congrArg (gammaVolumeValue U.toGammaRVObject) he).symm.trans hy

end IntegrationInACVF.Section6
