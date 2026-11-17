module

public import Integration7.NativeUnaryProducts
public import IntegrationSection5.HeadPreparation

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! Actual unary maps act on the first factor of a native VF rectangle.
The other VF coordinate stays fixed, and pullback first factors give
actual head-saturated product targets. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.DefinableGeometry.Space.prod
  SpecialTransformations.Section4.realSpace SpecialTransformations.Milestone0.sortEval
  SpecialTransformations.Section4.vfSpace SpecialTransformations.Section4.rvSpace
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section5
open IntegrationInACVF.Section5

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {S : Set M} {m r : ℕ}
variable {A : DefSet (M := M) S 1 m} {D : DefSet (M := M) S 1 r}

def nativeUnaryProductMap (f : Map A D) (B : DefSet (M := M) S 1 0) :
    Map (nativeUnaryProductDomain A B) (nativeUnaryProductDomain D B) :=
  Map.comp (Map.toImage (nativeUnaryProductJoinMap D B))
    (Map.pair (Map.comp f (nativeUnaryProductLeftMap A B)) (nativeUnaryProductRightMap A B))

theorem native_unary_product_map_value (f : Map A D) (B : DefSet (M := M) S 1 0)
    (p : nativeUnaryProductDomain A B) :
    (nativeUnaryProductMap f B p).val =
      (![(f (nativeUnaryProductLeftMap A B p)).val.1 0,vfAt p.val 1],
        (f (nativeUnaryProductLeftMap A B p)).val.2) := rfl

theorem native_unary_product_map_left (f : Map A D) (B : DefSet (M := M) S 1 0)
    (p : nativeUnaryProductDomain A B) :
    nativeUnaryProductLeftMap D B (nativeUnaryProductMap f B p) = f (nativeUnaryProductLeftMap A B p) := by
  apply Subtype.ext
  exact Prod.ext (by funext i;fin_cases i;rfl) rfl

theorem native_unary_product_map_relative (f : Map A D) (B : DefSet (M := M) S 1 0) :
    UnaryRelative (nativeUnaryProductMap f B) 0 := by
  intro p j hj
  fin_cases j
  · exact (hj rfl).elim
  · rfl

theorem native_unary_product_map_bijective (f : Map A D) (hf : Function.Bijective f)
    (B : DefSet (M := M) S 1 0) : Function.Bijective (nativeUnaryProductMap f B) := by
  constructor
  · intro p q he
    have hh := congrArg (nativeUnaryProductLeftMap D B) he
    rw [native_unary_product_map_left,native_unary_product_map_left] at hh
    have hOld := hf.1 hh
    have hOldValue := congrArg Subtype.val hOld
    have h0 := congrFun (congrArg Prod.fst hOldValue) 0
    have h1 : vfAt p.val 1 = vfAt q.val 1 :=
      congrArg (fun z : nativeUnaryProductDomain D B => vfAt z.val 1) he
    have hr := congrArg Prod.snd hOldValue
    apply Subtype.ext
    refine Prod.ext ?_ hr
    funext i
    fin_cases i
    · exact h0
    · exact h1
  · intro q
    obtain ⟨a,ha⟩ := hf.2 (nativeUnaryProductLeftMap D B q)
    let t : PresentedSet.prod A B := ⟨(a.val,(nativeUnaryProductRightMap D B q).val),a.property,
      (nativeUnaryProductRightMap D B q).property⟩
    let p := Map.toImage (nativeUnaryProductJoinMap A B) t
    have hp : nativeUnaryProductLeftMap A B p = a := by
      apply Subtype.ext
      exact Prod.ext (by funext i;fin_cases i;rfl) rfl
    refine ⟨p,Subtype.ext ?_⟩
    rw [native_unary_product_map_value,hp,ha]
    refine Prod.ext ?_ rfl
    funext i
    fin_cases i <;> rfl

theorem native_unary_product_head_saturated (A : DefSet (M := M) S 1 m)
    (B : DefSet (M := M) S 1 0) (hA : IsRVPullback (carrier A)) :
    HeadSaturated (carrier (nativeUnaryProductDomain A B)) := by
  intro p hp x hx
  have h := (native_unary_product_carrier A B p).mp hp
  apply (native_unary_product_carrier A B (replace 0 p x)).mpr
  constructor
  · apply (isRVPullback_iff _).mp hA (coordinateProject 0 p) h.1 (coordinateProject 0 (replace 0 p x))
    apply (sameRV_iff _ _).mpr
    refine ⟨?_,rfl⟩
    intro i
    change rv (vfAt p 0) = rv x
    exact hx.symm
  · simpa only [replace,vfAt,Function.update_of_ne (by decide : (1 : Fin 2) ≠ 0)] using h.2

end IntegrationInACVF.Section7
