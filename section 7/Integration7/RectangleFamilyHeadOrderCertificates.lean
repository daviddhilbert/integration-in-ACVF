import Integration7.RectangleFamilyHeadOrderMaps
import Integration7.GammaCoordinateSquareGraphs

/-! The rectangle target bijection has a full original-Gamma graph.
Its coordinate square retains both entire prepared factor keys. -/
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

def headKeySelector (F : IndependentRectangleFamilyPreparations G H hRect) :
    Fin ((1+F.tailArity)+(1+F.headArity)) → Fin (1+F.headLift.arity) :=
  Fin.append F.headLift.headProjection F.headLift.headParameters

def tailKeySelector (F : IndependentRectangleFamilyPreparations G H hRect) :
    Fin ((1+F.tailArity)+(1+F.headArity)) → Fin (1+F.tailLift.arity) :=
  Fin.append F.tailLift.headParameters F.tailLift.headProjection

theorem head_order_coordinate_square (F : IndependentRectangleFamilyPreparations G H hRect)
    (p : headImage F.headLift.target) :
    p.val.2 ∘ F.headKeySelector = (F.headOrderMap p).val.2 ∘ F.tailKeySelector := by
  have hv := congrArg Subtype.val (F.head_order_square p)
  have hE := congrArg (fun z : Point (M := M) 0 (1+F.tailArity) × Point (M := M) 0 (1+F.headArity) => z.1.2) hv
  have hD := congrArg (fun z : Point (M := M) 0 (1+F.tailArity) × Point (M := M) 0 (1+F.headArity) => z.2.2) hv
  change (F.headOrderMap p).val.2 ∘ F.tailLift.headParameters = p.val.2 ∘ F.headLift.headProjection at hE
  change (F.headOrderMap p).val.2 ∘ F.tailLift.headProjection = p.val.2 ∘ F.headLift.headParameters at hD
  funext i
  cases i using Fin.addCases with
  | left i =>
    change p.val.2 (Fin.append F.headLift.headProjection F.headLift.headParameters
      (Fin.castAdd (1+F.headArity) i)) = (F.headOrderMap p).val.2
        (Fin.append F.tailLift.headParameters F.tailLift.headProjection (Fin.castAdd (1+F.headArity) i))
    erw [Fin.append_left,Fin.append_left]
    exact congrFun hE.symm i
  | right i =>
    change p.val.2 (Fin.append F.headLift.headProjection F.headLift.headParameters
      (Fin.natAdd (1+F.tailArity) i)) = (F.headOrderMap p).val.2
        (Fin.append F.tailLift.headParameters F.tailLift.headProjection (Fin.natAdd (1+F.tailArity) i))
    erw [Fin.append_right,Fin.append_right]
    exact congrFun hD.symm i

theorem tail_key_selector_injective (F : IndependentRectangleFamilyPreparations G H hRect)
    (p q : headImage F.tailLift.target)
    (he : p.val.2 ∘ F.tailKeySelector = q.val.2 ∘ F.tailKeySelector) : p=q := by
  apply F.tailLift.head_product_map_injective
  apply Subtype.ext
  refine Prod.ext (Prod.ext (Subsingleton.elim _ _) ?_) (Prod.ext (Subsingleton.elim _ _) ?_)
  · funext i
    have h := congrFun he (Fin.castAdd (1+F.headArity) i)
    change p.val.2 (Fin.append F.tailLift.headParameters F.tailLift.headProjection
      (Fin.castAdd (1+F.headArity) i)) = q.val.2
        (Fin.append F.tailLift.headParameters F.tailLift.headProjection (Fin.castAdd (1+F.headArity) i)) at h
    erw [Fin.append_left] at h
    exact h
  · funext i
    have h := congrFun he (Fin.natAdd (1+F.tailArity) i)
    change p.val.2 (Fin.append F.tailLift.headParameters F.tailLift.headProjection
      (Fin.natAdd (1+F.tailArity) i)) = q.val.2
        (Fin.append F.tailLift.headParameters F.tailLift.headProjection (Fin.natAdd (1+F.tailArity) i)) at h
    erw [Fin.append_right] at h
    exact h

theorem head_order_graph_gamma (F : IndependentRectangleFamilyPreparations G H hRect) :
    GammaGraphDefinable G (pointMapGraph F.headOrderMap) :=
  gamma_coordinate_square_graph
    (gamma_headImage _ (F.headLift.gamma.target G F.headLift.special.chain))
    (gamma_headImage _ (F.tailLift.gamma.target G F.tailLift.special.chain))
    F.headOrderMap F.headKeySelector F.tailKeySelector F.head_order_coordinate_square F.tail_key_selector_injective

end IntegrationInACVF.Section7.IndependentRectangleFamilyPreparations
