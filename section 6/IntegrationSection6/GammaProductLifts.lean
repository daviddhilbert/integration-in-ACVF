import IntegrationSection6.GammaMixedProductIsomorphisms
import IntegrationSection6.FiniteGammaProducts
import IntegrationSection6.FiniteGammaLiftGluing
import IntegrationSection6.GammaTaggedLifts
import IntegrationSection6.GammaDisjointIsomorphisms

/-! The lift of the actual finite RV coproduct is the disjoint union of
the corresponding tagged lifts. This is the gluing geometry for6.13. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.DefinableGeometry.Space.prod
  SpecialTransformations.Section4.realSpace SpecialTransformations.Milestone0.sortEval
  SpecialTransformations.Section4.vfSpace SpecialTransformations.Section4.rvSpace
  SpecialTransformations.Section4.rawVFSpace SpecialTransformations.Section4.rawRVSpace
  SpecialTransformations.Section4.rawMixedSpace SpecialTransformations.DefinableGeometry.Space.ofEmbedding
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
namespace IntegrationInACVF.Section6.FiniteRV
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

variable {B : Base (M := M)} {S : Set M} {n l : ℕ}
local notation "N" => (@CanonicalStructure.normalize M sM)
local notation "hN" => (@CanonicalStructure.normalized_model M sM hM)

theorem gammaProductAt_lift (U : GammaObjectAt B S n) (V : GammaObjectAt B S l) :
    (gammaProductAt U V).toGamma.lift = mixedProductSet U.toGamma.lift V.toGamma.lift := by
  ext p
  constructor
  · rintro ⟨z,hz,hvol⟩
    obtain ⟨u,v,rfl⟩ := @exists_rvPackPair M N S _ _ (rvObjectDomain U.object.obj) (rvObjectDomain V.object.obj) z
    have hvol' := (@rvProductObject_value_pair M N S n l U.object.obj V.object.obj u v).symm.trans hvol
    have hu : u.val = p.2 ∘ Fin.castAdd (rvObjectArity V.object.obj) := by
      funext j
      exact (Fin.append_left _ _ j).symm.trans (congrFun hz (Fin.castAdd (rvObjectArity V.object.obj) j))
    have hv : v.val = p.2 ∘ Fin.natAdd (rvObjectArity U.object.obj) := by
      funext j
      exact (Fin.append_right _ _ j).symm.trans (congrFun hz (Fin.natAdd (rvObjectArity U.object.obj) j))
    have hU : @RVObject.value M N S n U.object.obj u = @tupleRV M N hN n (p.1 ∘ Fin.castAdd l) := by
      funext j
      exact (Fin.append_left _ _ j).symm.trans (congrFun hvol' (Fin.castAdd l j))
    have hV : @RVObject.value M N S l V.object.obj v = @tupleRV M N hN l (p.1 ∘ Fin.natAdd n) := by
      funext j
      exact (Fin.append_right _ _ j).symm.trans (congrFun hvol' (Fin.natAdd n j))
    exact ⟨⟨u,hu,hU⟩,⟨v,hv,hV⟩⟩
  · rintro ⟨⟨u,hu,hU⟩,⟨v,hv,hV⟩⟩
    let z := @rvPackPair M N S _ _ (rvObjectDomain U.object.obj) (rvObjectDomain V.object.obj) u v
    refine ⟨z,?_,?_⟩
    · change Fin.append u.val v.val = p.2
      rw [hu,hv]
      exact Fin.append_castAdd_natAdd
    · refine (@rvProductObject_value_pair M N S n l U.object.obj V.object.obj u v).trans ?_
      change Fin.append (@RVObject.value M N S n U.object.obj u) (@RVObject.value M N S l V.object.obj v) = _
      refine (congrArg₂ (fun s t => Fin.append s t) hU hV).trans ?_
      funext j
      cases j using Fin.addCases <;> simp only [Fin.append_left,Fin.append_right,tupleRV,mixedProductLeft,mixedProductRight,Function.comp_apply]

def gammaProductLiftIsoAt (U : GammaObjectAt B S n) (V : GammaObjectAt B S l) :
    GammaIso B (gammaProductAt U V).toGamma.lift (mixedProductSet U.toGamma.lift V.toGamma.lift) :=
  (gammaIso_reflexive (gammaProductAt U V).toGamma.lift (gammaProductAt U V).toGamma.toGammaRVObject.lift_definable).congr
    rfl (gammaProductAt_lift U V)

end IntegrationInACVF.Section6.FiniteRV
