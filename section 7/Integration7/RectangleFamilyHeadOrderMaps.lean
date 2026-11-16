module

public import Integration7.IndependentRectangleFamilyPreparations

@[expose] public section

/-! The two actual contraction targets of a shared-label rectangle
family are definably bijective. The map exchanges the factor keys and
uses the proved equality of their original RV labels. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.DefinableGeometry.Space.prod
  SpecialTransformations.Section4.realSpace SpecialTransformations.Milestone0.sortEval
  SpecialTransformations.Section4.vfSpace SpecialTransformations.Section4.rvSpace
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section5
open IntegrationInACVF.Section5 IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7.IndependentRectangleFamilyPreparations
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {G : Base (M := M)} {S : Set M} {m : ℕ}
variable {H : DefSet (M := M) S 2 m} {hRect : RectangularRVFibres (carrier H)}

def forwardPairMap (F : IndependentRectangleFamilyPreparations G H hRect) :
    Map (headImage F.headLift.target) (PresentedSet.prod (headImage F.tailTarget) (headImage F.headTarget)) :=
  Map.pair F.headLift.headPreparedMap F.headLift.headParameterMap

def backwardPairMap (F : IndependentRectangleFamilyPreparations G H hRect) :
    Map (headImage F.tailLift.target) (PresentedSet.prod (headImage F.headTarget) (headImage F.tailTarget)) :=
  Map.pair F.tailLift.headPreparedMap F.tailLift.headParameterMap

theorem forward_pair_preimage (F : IndependentRectangleFamilyPreparations G H hRect)
    (p : headImage F.headLift.target) : ∃ q, F.tailLift.headProductMap q = F.forwardPairMap p := by
  apply F.tailLift.head_product_map_preimage
  have h := (F.headLift.head_product_map_compatible p).symm
  exact h

theorem backward_pair_preimage (F : IndependentRectangleFamilyPreparations G H hRect)
    (q : headImage F.tailLift.target) : ∃ p, F.headLift.headProductMap p = F.backwardPairMap q := by
  apply F.headLift.head_product_map_preimage
  exact (F.tailLift.head_product_map_compatible q).symm

private theorem image_pair_bijective (F : IndependentRectangleFamilyPreparations G H hRect) :
    Function.Bijective (Map.toImage F.tailLift.headProductMap) := by
  constructor
  · intro p q he
    apply F.tailLift.head_product_map_injective
    have hv := congrArg Subtype.val he
    exact Subtype.ext hv
  · rintro ⟨q,p,hp⟩
    exact ⟨p,Subtype.ext hp⟩

def headOrderMap (F : IndependentRectangleFamilyPreparations G H hRect) :
    Map (headImage F.headLift.target) (headImage F.tailLift.target) :=
  let g := Map.toImage F.tailLift.headProductMap
  let k := mapIntoSubset F.forwardPairMap (Map.image F.tailLift.headProductMap) (fun p => by
    obtain ⟨q,hq⟩ := F.forward_pair_preimage p
    exact ⟨q,congrArg Subtype.val hq⟩)
  Map.comp (Map.inverse g (image_pair_bijective F)) k

theorem head_order_square (F : IndependentRectangleFamilyPreparations G H hRect)
    (p : headImage F.headLift.target) :
    F.tailLift.headProductMap (F.headOrderMap p) = F.forwardPairMap p := by
  have he := Map.apply_inverse (Map.toImage F.tailLift.headProductMap) (image_pair_bijective F)
    (mapIntoSubset F.forwardPairMap (Map.image F.tailLift.headProductMap) (fun p => by
      obtain ⟨q,hq⟩ := F.forward_pair_preimage p
      exact ⟨q,congrArg Subtype.val hq⟩) p)
  have hv := congrArg Subtype.val he
  exact Subtype.ext hv

theorem head_order_bijective (F : IndependentRectangleFamilyPreparations G H hRect) :
    Function.Bijective F.headOrderMap := by
  constructor
  · intro p q he
    have h := (F.head_order_square p).symm.trans
      ((congrArg (fun z => F.tailLift.headProductMap z) he).trans (F.head_order_square q))
    have hv := congrArg Subtype.val h
    have hSwap := congrArg Prod.swap hv
    apply F.headLift.head_product_map_injective
    exact Subtype.ext hSwap
  · intro q
    obtain ⟨p,hp⟩ := F.backward_pair_preimage q
    refine ⟨p,?_⟩
    apply F.tailLift.head_product_map_injective
    have hv := congrArg Subtype.val hp
    have hSwap := congrArg Prod.swap hv
    exact (F.head_order_square p).trans (Subtype.ext hSwap)

end IntegrationInACVF.Section7.IndependentRectangleFamilyPreparations
