import IntegrationSection6.FiniteGammaRestrictions
import IntegrationSection6.FiniteGammaCoproducts
import IntegrationSection6.FiniteGammaAmbientIsos
import IntegrationSection6.PartitionCoordinates

/-! A Gamma-definable RV locus and its complement give an actual RV[k]
partition isomorphism whose entire graph remains over the original base. -/
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

def gammaPartitionIsoAt (U : GammaObjectAt B S n)
    (A : @SpecialTransformations.DefinableGeometry.DefSet LRV M N
      (@rawRVSpace M N (rvObjectArity U.object.obj)) S)
    (hA : (@SpecialTransformations.DefinableGeometry.DefSet.carrier LRV M N _ S A) ⊆
      (@SpecialTransformations.DefinableGeometry.DefSet.carrier LRV M N _ S (rvObjectDomain U.object.obj)))
    (hΓ : GammaSetDefinable B {p : Point (M := M) 0 (rvObjectArity U.object.obj) |
      p.2 ∈ (@SpecialTransformations.DefinableGeometry.DefSet.carrier LRV M N _ S A)}) :
    GammaIsoAt (gammaCoprodAt (gammaRestrictAt U A hA hΓ) (gammaComplementAt U A hΓ)) U := by
  let C := gammaRestrictAt U A hA hΓ
  let R := gammaComplementAt U A hΓ
  let e := @partitionIso M N hN S n U.object.obj A hA
  let F := @RVHom.map M N S n (gammaCoprodAt C R).object.obj U.object.obj e.hom
  apply GammaIsoAt.ofAmbient e
  let L := gammaLogicInput B
  apply GammaGraphDefinable.congr (L.union_graph
    (L.swap_graph (gamma_leftTag_graph C (rvObjectArity R.object.obj)))
    (L.swap_graph (gamma_rightTag_graph R (rvObjectArity C.object.obj))))
  intro p q
  constructor
  · rintro (⟨u,hu,hp⟩ | ⟨v,hv,hp⟩)
    · refine ⟨@rvCoprodLeftMap M N hN S n C.object.obj R.object.obj u,hp,?_⟩
      exact (@partitionIso_left M N hN S n U.object.obj A hA u).trans hu
    · refine ⟨@rvCoprodRightMap M N hN S n C.object.obj R.object.obj v,hp,?_⟩
      exact (@partitionIso_right M N hN S n U.object.obj A hA v).trans hv
  · rintro ⟨a,ha,hq⟩
    rcases a.property with ⟨u,hu⟩ | ⟨v,hv⟩
    · have he : a = @rvCoprodLeftMap M N hN S n C.object.obj R.object.obj u := Subtype.ext hu.symm
      have hc : u.val = q.2 := (@partitionIso_left M N hN S n U.object.obj A hA u).symm.trans
        ((congrArg (fun a => (F a).val) he).symm.trans hq)
      exact Or.inl ⟨u,hc,hu.trans ha⟩
    · have he : a = @rvCoprodRightMap M N hN S n C.object.obj R.object.obj v := Subtype.ext hv.symm
      have hc : v.val = q.2 := (@partitionIso_right M N hN S n U.object.obj A hA v).symm.trans
        ((congrArg (fun a => (F a).val) he).symm.trans hq)
      exact Or.inr ⟨v,hc,hv.trans ha⟩

end IntegrationInACVF.Section6.FiniteRV
