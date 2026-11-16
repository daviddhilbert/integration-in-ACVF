module

public import Integration7.RectangleFamilyRawOrderIsomorphisms
public import Integration7.IndependentRectangleRetainedLabels

@[expose] public section

/-! The two-order rectangle isomorphism retains every original RV
label, hence every nonconstant density carried by one of those labels. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section5
open IntegrationInACVF.Section5 IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7.IndependentRectangleFamilyPreparations
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {G : Base (M := M)} {S : Set M} {m : ℕ}
variable {H : DefSet (M := M) S 2 m} {hRect : RectangularRVFibres (carrier H)}

theorem head_order_retained_labels (F : IndependentRectangleFamilyPreparations G H hRect)
    (p : headImage F.headLift.target) (i : Fin m) :
    (F.headOrderMap p).val.2 (suffixIndex F.tailContraction.program.rvArity_le i) =
      p.val.2 (suffixIndex F.headContraction.program.rvArity_le i) := by
  let q := F.headOrderMap p
  have hv := congrArg Subtype.val (F.head_order_square p)
  have hE := congrArg (fun z : Point (M := M) 0 (1+F.tailArity) × Point (M := M) 0 (1+F.headArity) => z.1.2) hv
  change q.val.2 ∘ F.tailLift.headParameters = p.val.2 ∘ F.headLift.headProjection at hE
  have hCompatible := congrFun (F.headLift.head_product_map_compatible p) i
  change p.val.2 (F.headLift.headProjection (Fin.natAdd 1
    (suffixIndex (special_chain_rvArity_le F.tailSpecial.chain) i))) =
      p.val.2 (F.headLift.headParameters (rectangleHeadOldLabelIndex F.headSpecial i)) at hCompatible
  exact (F.tail_retained_label q i).trans
    ((congrFun hE (rectangleHeadOldLabelIndex (swappedRectangleHeadSpecial F.tailSpecial) i)).trans
      (hCompatible.trans (F.head_retained_label p i).symm))

theorem raw_order_retained_labels (F : IndependentRectangleFamilyPreparations G H hRect)
    (hc : CanonicalStructure.IsCanonical (M := M))
    (u : (canonicalRVObject hc F.headContraction.contractionObject).domain) (i : Fin m) :
    (F.rawOrderMap hc u).val (suffixIndex F.tailContraction.program.rvArity_le i) =
      u.val (suffixIndex F.headContraction.program.rvArity_le i) := by
  let p := rawLabelImageInverse (headImage F.headLift.target) ⟨u.val,u.property⟩
  have hp : p.val.2 = u.val := raw_label_image_inverse_labels _ _
  exact (F.head_order_retained_labels p i).trans (congrFun hp _)

end IntegrationInACVF.Section7.IndependentRectangleFamilyPreparations
