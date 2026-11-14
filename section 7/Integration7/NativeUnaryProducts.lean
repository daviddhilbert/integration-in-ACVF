import IntegrationSection5.CoordinateFibreMaps
import IntegrationSection6.MixedCoordinatePointMaps

/-! Products of an actual unary mixed domain with a pure unary VF domain,
in the native two-coordinate point language. Labels belong to the first
factor, and the two VF coordinates retain their original order. -/
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
variable {S : Set M} {m : ℕ}

def nativeUnaryProductJoinMap (A : DefSet (M := M) S 1 m) (B : DefSet (M := M) S 1 0) :
    Map (PresentedSet.prod A B) (PresentedSet.univ (pointSpace 2 m) S) :=
  Map.ofCodes _ (fun p => (![p.1.1 0,p.2.1 0],p.1.2))
    (fun z => Sum.elim (fun i : Fin 2 => if i = 0 then z (.inl (.inl 0)) else z (.inr (.inl 0)))
      (fun j => z (.inl (.inr j))))
    (by
      intro i
      cases i with
      | inl i =>
        by_cases hi : i = 0
        · simpa only [Sum.elim_inl,hi,ite_true] using rawProj S
            (Sum.inl (Sum.inl 0) : (Fin 1 ⊕ Fin m) ⊕ (Fin 1 ⊕ Fin 0))
        · simpa only [Sum.elim_inl,hi,ite_false] using rawProj S
            (Sum.inr (Sum.inl 0) : (Fin 1 ⊕ Fin m) ⊕ (Fin 1 ⊕ Fin 0))
      | inr j => exact rawProj S (Sum.inl (Sum.inr j) : (Fin 1 ⊕ Fin m) ⊕ (Fin 1 ⊕ Fin 0)))
    (by
      intro c
      refine ⟨?_,c.property.1.2⟩
      intro i
      fin_cases i
      · exact c.property.1.1 0
      · exact c.property.2.1 0)
    (by
      intro c
      refine Prod.ext ?_ rfl
      funext i
      fin_cases i <;> rfl)

theorem native_unary_product_join_value (A : DefSet (M := M) S 1 m) (B : DefSet (M := M) S 1 0)
    (p : PresentedSet.prod A B) :
    (nativeUnaryProductJoinMap A B p).val = (![p.val.1.1 0,p.val.2.1 0],p.val.1.2) := rfl

def nativeUnaryProductDomain (A : DefSet (M := M) S 1 m) (B : DefSet (M := M) S 1 0) :
    DefSet (M := M) S 2 m := Map.image (nativeUnaryProductJoinMap A B)

theorem native_unary_product_carrier (A : DefSet (M := M) S 1 m) (B : DefSet (M := M) S 1 0)
    (p : Point (M := M) 2 m) :
    p ∈ carrier (nativeUnaryProductDomain A B) ↔ coordinateProject 0 p ∈ carrier A ∧
      ((fun _ : Fin 1 => vfAt p 1),Fin.elim0) ∈ carrier B := by
  constructor
  · rintro ⟨q,rfl⟩
    have hA : coordinateProject 0 (nativeUnaryProductJoinMap A B q).val = q.val.1 :=
      Prod.ext (by funext i;fin_cases i;rfl) rfl
    have hB : (show Point (M := M) 1 0 from
        ((fun _ : Fin 1 => vfAt (nativeUnaryProductJoinMap A B q).val 1),Fin.elim0)) = q.val.2 :=
      Prod.ext (by funext i;fin_cases i;rfl) (Subsingleton.elim _ _)
    exact ⟨(congrArg (fun z : Point (M := M) 1 m => z ∈ carrier A) hA).mpr q.property.1,
      (congrArg (fun z : Point (M := M) 1 0 => z ∈ carrier B) hB).mpr q.property.2⟩
  · rintro ⟨hpA,hpB⟩
    refine ⟨⟨(coordinateProject 0 p,((fun _ : Fin 1 => vfAt p 1),Fin.elim0)),hpA,hpB⟩,?_⟩
    refine Prod.ext ?_ rfl
    funext i
    fin_cases i <;> rfl

def nativeUnaryProductLeftMap (A : DefSet (M := M) S 1 m) (B : DefSet (M := M) S 1 0) :
    Map (nativeUnaryProductDomain A B) A :=
  mapIntoSubset (coordinateProjectMap 0 (nativeUnaryProductDomain A B)) A
    (fun p => ((native_unary_product_carrier A B p.val).mp p.property).1)

def nativeUnaryProductRightMap (A : DefSet (M := M) S 1 m) (B : DefSet (M := M) S 1 0) :
    Map (nativeUnaryProductDomain A B) B := by
  let g := Map.comp (mixedCoordinatePointMap (fun _ : Fin 1 => (1 : Fin 2))
    (Fin.elim0 : Fin 0 → Fin m) S)
    (Map.inclusion (Set.subset_univ _) : Map (nativeUnaryProductDomain A B) (PresentedSet.univ (pointSpace 2 m) S))
  refine mapIntoSubset g B ?_
  intro p
  have he : (g p).val = (show Point (M := M) 1 0 from
      ((fun _ : Fin 1 => vfAt p.val 1),Fin.elim0)) := Prod.ext rfl (Subsingleton.elim _ _)
  exact (congrArg (fun z : Point (M := M) 1 0 => z ∈ carrier B) he).mpr
    ((native_unary_product_carrier A B p.val).mp p.property).2

theorem native_unary_product_left_value (A : DefSet (M := M) S 1 m) (B : DefSet (M := M) S 1 0)
    (p : nativeUnaryProductDomain A B) :
    (nativeUnaryProductLeftMap A B p).val = coordinateProject 0 p.val := rfl

theorem native_unary_product_right_value (A : DefSet (M := M) S 1 m) (B : DefSet (M := M) S 1 0)
    (p : nativeUnaryProductDomain A B) :
    (nativeUnaryProductRightMap A B p).val = ((fun _ : Fin 1 => vfAt p.val 1),Fin.elim0) :=
  Prod.ext rfl (Subsingleton.elim _ _)

end IntegrationInACVF.Section7
