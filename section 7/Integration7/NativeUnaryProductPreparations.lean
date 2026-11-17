module

public import Integration7.NativeUnaryProductFibres
public import IntegrationSection6.SpecialEqualityTransport

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! A unary special preparation acts as an actual relatively special
preparation on a rectangle. Restriction also handles empty fibres. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.DefinableGeometry.Space.prod
  SpecialTransformations.Section4.realSpace SpecialTransformations.Milestone0.sortEval
  SpecialTransformations.Section4.vfSpace SpecialTransformations.Section4.rvSpace
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section5
open IntegrationInACVF.Section5 IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {S : Set M} {m r : ℕ}
variable {A : DefSet (M := M) S 1 m} {D : DefSet (M := M) S 1 r}

theorem native_unary_product_special_relative (T : SpecialBijection A D)
    (B : DefSet (M := M) S 1 0) : SpecialRelative (nativeUnaryProductMap T.toMap B) 0 := by
  refine ⟨native_unary_product_map_relative T.toMap B,fun u => ?_⟩
  let H := coordinateFibre (nativeUnaryProductDomain A B) 0 u
  let K := coordinateFibre (nativeUnaryProductDomain D B) 0 u
  let hSR : S ⊆ coordinateFibreBase S 0 u := Set.subset_union_left
  let V := T.extendBase hSR
  have hHA : carrier H ⊆ carrier (extendBase A hSR) :=
    fun p hp => ((native_unary_product_coordinate_fibre A B u p).mp hp).1
  obtain ⟨R,W,hAlt,hEnd,hRD,hW⟩ := special_restrict_boundary V H hHA none V.alternating
  have hRK : carrier R = carrier K := by
    ext q
    constructor
    · intro hq
      obtain ⟨p,hp⟩ := W.bijective.2 ⟨q,hq⟩
      have hv := (hW p).symm.trans (congrArg Subtype.val hp)
      have hv' := (T.chain.extendBase_apply hSR ⟨p.val,hHA p.property⟩).symm.trans hv
      have hFrozen := ((native_unary_product_coordinate_fibre A B u p.val).mp p.property).2
      apply (native_unary_product_coordinate_fibre D B u q).mpr
      exact ⟨(congrArg (fun z : Point (M := M) 1 r => z ∈ carrier D) hv').mp
        (T.toMap ⟨p.val,hHA p.property⟩).property,hFrozen⟩
    · intro hq
      have hq' := (native_unary_product_coordinate_fibre D B u q).mp hq
      let d : D := ⟨q,hq'.1⟩
      let a := T.inverseMap d
      let p : H := ⟨a.val,(native_unary_product_coordinate_fibre A B u a.val).mpr ⟨a.property,hq'.2⟩⟩
      have hv : (W.toMap p).val = q := by
        calc
          (W.toMap p).val = (V.toMap ⟨p.val,hHA p.property⟩).val := hW p
          _ = (T.toMap a).val := T.chain.extendBase_apply hSR _
          _ = q := congrArg Subtype.val (T.apply_inverse d)
      exact hv ▸ (W.toMap p).property
  have hEq : R = K := defSet_eq_of_carrier_eq hRK
  refine ⟨specialCastBoth W rfl hEq,fun p => Subtype.ext ?_⟩
  calc
    ((specialCastBoth W rfl hEq).toMap p).val = (W.toMap p).val := specialCastBoth_value W rfl hEq p p rfl
    _ = (V.toMap ⟨p.val,hHA p.property⟩).val := hW p
    _ = (T.toMap ⟨p.val,hHA p.property⟩).val := T.chain.extendBase_apply hSR _
    _ = (coordinateFibreMap (nativeUnaryProductMap T.toMap B) 0
      (native_unary_product_map_relative T.toMap B) u p).val :=
        (native_unary_product_fibre_map_value T.toMap B u p).symm

def nativeUnaryProductHeadPreparation (T : SpecialBijection A D)
    (B : DefSet (M := M) S 1 0) (hD : IsRVPullback (carrier D)) :
    HeadPreparation (nativeUnaryProductDomain A B) where
  arity := r
  target := nativeUnaryProductDomain D B
  map := nativeUnaryProductMap T.toMap B
  special := native_unary_product_special_relative T B
  saturated := native_unary_product_head_saturated D B hD

end IntegrationInACVF.Section7
