import Integration7.NativeRectangleFamilyHeadGeometry
import Integration7.NativeUnaryProductPreparations
import IntegrationSection5.RestrictedHeadPreparation
import IntegrationSection5.RelativeLabelPreservation
import IntegrationSection6.RelativeSpecialSourceRestriction

/-! A unary special preparation of the labelled head projection lifts
to an actual relatively special head preparation of a rectangle family.
Shared RV labels are retained through the inverse membership argument. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section5
open IntegrationInACVF.Section5 IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {S : Set M} {m r : ℕ}

theorem rectangle_family_ambient_source_subset (H : DefSet (M := M) S 2 m) :
    carrier H ⊆ carrier (nativeUnaryProductDomain (Map.image (coordinateProjectMap 0 H))
      (PresentedSet.univ (pointSpace 1 0) S)) := by
  intro p hp
  apply (native_unary_product_carrier _ _ p).mpr
  exact ⟨⟨⟨p,hp⟩,rfl⟩,Set.mem_univ _⟩

set_option maxHeartbeats 1600000 in
theorem rectangle_family_inverse_membership_uniform
    (H : DefSet (M := M) S 2 m) (hRect : RectangularRVFibres (carrier H))
    {D : DefSet (M := M) S 1 r} (T : SpecialBijection (Map.image (coordinateProjectMap 0 H)) D)
    (b c : nativeUnaryProductDomain D (PresentedSet.univ (pointSpace 1 0) S))
    (he : SameRV b.val c.val) (ht : TailEq b.val c.val) :
    let U := PresentedSet.univ (pointSpace (M := M) 1 0) S
    let g := nativeUnaryProductMap T.toMap U
    let hg := native_unary_product_map_bijective T.toMap T.bijective U
    (Map.inverse g hg b).val ∈ carrier H ↔ (Map.inverse g hg c).val ∈ carrier H := by
  intro U g hg
  let p := Map.inverse g hg b
  let q := Map.inverse g hg c
  have hgp : g p = b := Map.apply_inverse g hg b
  have hgq : g q = c := Map.apply_inverse g hg c
  have hSpec := native_unary_product_special_relative T U
  have hRV : p.val.2=q.val.2 := by
    funext i
    let j := suffixIndex (specialRelative_rvArity_le hSpec) i
    have hpOld := specialRelative_oldLabels hSpec p i
    have hqOld := specialRelative_oldLabels hSpec q i
    have hpVal := congrArg (fun z : nativeUnaryProductDomain D U => z.val.2 j) hgp
    have hqVal := congrArg (fun z : nativeUnaryProductDomain D U => z.val.2 j) hgq
    have hLabels := congrFun ((sameRV_iff _ _).mp he).2 j
    exact hpOld.symm.trans (hpVal.trans (hLabels.trans (hqVal.symm.trans hqOld)))
  have hpTail : vfAt p.val 1 = vfAt b.val 1 :=
    ((native_unary_product_map_relative T.toMap U) p 1 (by decide)).symm.trans
      (congrArg (fun z : nativeUnaryProductDomain D U => vfAt z.val 1) hgp)
  have hqTail : vfAt q.val 1 = vfAt c.val 1 :=
    ((native_unary_product_map_relative T.toMap U) q 1 (by decide)).symm.trans
      (congrArg (fun z : nativeUnaryProductDomain D U => vfAt z.val 1) hgq)
  exact rectangle_family_head_membership_uniform H hRect p.val q.val
    ((native_unary_product_carrier _ _ p.val).mp p.property).1
    ((native_unary_product_carrier _ _ q.val).mp q.property).1 hRV (hpTail.trans ((ht 0).trans hqTail.symm))

def rectangleFamilyHeadPreparation
    (H : DefSet (M := M) S 2 m) (hRect : RectangularRVFibres (carrier H))
    {D : DefSet (M := M) S 1 r} (T : SpecialBijection (Map.image (coordinateProjectMap 0 H)) D)
    (hD : IsRVPullback (carrier D)) : HeadPreparation H :=
  let U := PresentedSet.univ (pointSpace (M := M) 1 0) S
  let g := nativeUnaryProductMap T.toMap U
  let hSub := rectangle_family_ambient_source_subset H
  { arity := r
    target := restrictPointImage g H hSub
    map := restrictPointMap g H hSub
    special := specialRelative_restrict g H hSub (native_unary_product_special_relative T U)
    saturated := restrictPointImage_headSaturated g (native_unary_product_map_bijective T.toMap T.bijective U)
      (native_unary_product_head_saturated D U hD) H hSub
      (rectangle_family_inverse_membership_uniform H hRect T) }

end IntegrationInACVF.Section7
