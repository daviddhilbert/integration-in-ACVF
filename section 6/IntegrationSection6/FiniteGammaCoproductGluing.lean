import IntegrationSection6.FiniteGammaCategoricalCoproducts
import Mathlib.Data.Sum.Basic

/-! Gluing two finite Gamma morphisms into an isomorphism when their
actual disjoint images cover the target and preserve weight. -/
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

def coprodSumMap (U V : GammaObjectAt B S n) :
    Sum (rvObjectDomain U.object.obj) (rvObjectDomain V.object.obj) → rvObjectDomain (gammaCoprodAt U V).object.obj :=
  Sum.elim (@rvCoprodLeftMap M N hN S n U.object.obj V.object.obj)
    (@rvCoprodRightMap M N hN S n U.object.obj V.object.obj)

theorem coprodSumMap_bijective (U V : GammaObjectAt B S n) : Function.Bijective (coprodSumMap U V) := by
  constructor
  · apply Sum.elim_injective.mpr
    refine ⟨?_,?_,?_⟩
    · intro u v he
      exact Subtype.ext (@rvLeftTag_injective M N hN (rvObjectArity U.object.obj) (rvObjectArity V.object.obj)
        _ _ (congrArg (fun a : rvObjectDomain (gammaCoprodAt U V).object.obj => a.val) he))
    · intro u v he
      exact Subtype.ext (@rvRightTag_injective M N hN (rvObjectArity V.object.obj) (rvObjectArity U.object.obj)
        _ _ (congrArg (fun a : rvObjectDomain (gammaCoprodAt U V).object.obj => a.val) he))
    · intro u v he
      exact @rvTag_disjoint M N hN (rvObjectArity U.object.obj) (rvObjectArity V.object.obj) u.val v.val
        (congrArg (fun a : rvObjectDomain (gammaCoprodAt U V).object.obj => a.val) he)
  · intro a
    rcases a.property with ⟨u,hu⟩ | ⟨v,hv⟩
    · exact ⟨Sum.inl u,Subtype.ext hu⟩
    · exact ⟨Sum.inr v,Subtype.ext hv⟩

theorem gammaCoprodDescMap_bijective {U V W : GammaObjectAt B S n}
    (f : U ⟶ W) (g : V ⟶ W)
    (h : Function.Bijective (Sum.elim (homAtMap f.hom) (homAtMap g.hom))) :
    Function.Bijective (gammaCoprodDescMap f g) := by
  apply (Function.Bijective.of_comp_iff _ (coprodSumMap_bijective U V)).mp
  have he : gammaCoprodDescMap f g ∘ coprodSumMap U V = Sum.elim (homAtMap f.hom) (homAtMap g.hom) := by
    funext a
    cases a with
    | inl u => exact gammaCoprodDescMap_left f g u
    | inr v => exact gammaCoprodDescMap_right f g v
  rw [he]
  exact h

def gammaCoprodIsoOfSum {U V W : GammaObjectAt B S n}
    (f : U ⟶ W) (g : V ⟶ W)
    (h : Function.Bijective (Sum.elim (homAtMap f.hom) (homAtMap g.hom)))
    (hf : ∀ u : rvObjectDomain U.object.obj,
      @rvWeight M N n (@RVObject.value M N S n U.object.obj u) =
        @rvWeight M N n (@RVObject.value M N S n W.object.obj (homAtMap f.hom u)))
    (hg : ∀ v : rvObjectDomain V.object.obj,
      @rvWeight M N n (@RVObject.value M N S n V.object.obj v) =
        @rvWeight M N n (@RVObject.value M N S n W.object.obj (homAtMap g.hom v))) :
    GammaIsoAt (gammaCoprodAt U V) W := by
  have hw (a : rvObjectDomain (gammaCoprodAt U V).object.obj) :
      @rvWeight M N n (@RVObject.value M N S n (gammaCoprodAt U V).object.obj a) =
        @rvWeight M N n (@RVObject.value M N S n W.object.obj (gammaCoprodDescMap f g a)) := by
    rcases a.property with ⟨u,hu⟩ | ⟨v,hv⟩
    · have he : a = @rvCoprodLeftMap M N hN S n U.object.obj V.object.obj u := Subtype.ext hu.symm
      rw [he,gammaCoprodDescMap_left]
      exact (congrArg (@rvWeight M N n) (@rvCoprod_value_left M N hN S n U.object.obj V.object.obj u)).trans (hf u)
    · have he : a = @rvCoprodRightMap M N hN S n U.object.obj V.object.obj v := Subtype.ext hv.symm
      rw [he,gammaCoprodDescMap_right]
      exact (congrArg (@rvWeight M N n) (@rvCoprod_value_right M N hN S n U.object.obj V.object.obj v)).trans (hg v)
  exact {
    iso := @isoOfDefinableBijection M N S n (gammaCoprodAt U V).object W.object
      (gammaCoprodDescMap f g) (gammaCoprodDescMap_bijective f g h) hw
    graph := gamma_coprodDesc_graph f g }

end IntegrationInACVF.Section6.FiniteRV
