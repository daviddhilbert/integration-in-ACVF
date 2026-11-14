import Integration7.RVParameterHeadProducts

/-! A carried-parameter unary contraction is definably bijective to
the product of the parameter domain and the original unary contraction.
Surjectivity uses the actual special chain, not an amalgamation axiom
for possibly overlapping coordinate selectors. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.DefinableGeometry.Space.prod
  SpecialTransformations.Section4.realSpace SpecialTransformations.Milestone0.sortEval
  SpecialTransformations.Section4.vfSpace SpecialTransformations.Section4.rvSpace
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3.GammaParameters SpecialTransformations.Section5

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {P : Base (M := M)} {S : Set M} {b l : ℕ}
variable {A : DefSet (M := M) S 1 0} {B : DefSet (M := M) S 1 b}
variable {T : SpecialBijection A B} {H : DefSet (M := M) S 1 l} {Q : DefSet (M := M) S 0 l}

namespace RVParameterSpecialPreparation

theorem head_product_map_injective (L : RVParameterSpecialPreparation T H Q P) :
    Function.Injective L.headProductMap := by
  intro p q he
  have hv := congrArg Subtype.val he
  rw [head_product_map_value,head_product_map_value] at hv
  have hQ := congrArg (fun z : Point (M := M) 0 l × Point (M := M) 0 (1+b) => z.1.2) hv
  have hB := congrArg (fun z : Point (M := M) 0 l × Point (M := M) 0 (1+b) => z.2.2) hv
  have hR : (fun j => p.val.2 (Fin.natAdd 1 j)) = (fun j => q.val.2 (Fin.natAdd 1 j)) := by
    apply L.jointly_determine
    · funext j
      have h := congrFun hB (Fin.natAdd 1 j)
      change p.val.2 (L.headProjection (Fin.natAdd 1 j)) = q.val.2 (L.headProjection (Fin.natAdd 1 j)) at h
      rw [headProjection,Fin.append_right] at h
      exact h
    · exact hQ
  apply Subtype.ext
  refine Prod.ext (Subsingleton.elim _ _) ?_
  funext j
  cases j using Fin.addCases with
  | left j =>
    have hj : j = 0 := Subsingleton.elim _ _
    subst j
    have h := congrFun hB (Fin.castAdd b 0)
    change p.val.2 (L.headProjection (Fin.castAdd b 0)) = q.val.2 (L.headProjection (Fin.castAdd b 0)) at h
    rw [headProjection,Fin.append_left] at h
    exact h
  | right j => exact congrFun hR j

theorem head_product_map_surjective (L : RVParameterSpecialPreparation T H Q P) :
    Function.Surjective L.headProductMap := by
  intro q
  obtain ⟨v,hv⟩ := q.property.2
  let a := T.inverseMap v
  let p0 : Point (M := M) 1 l := (a.val.1,q.val.1.2)
  have hP0 : retainVFLabels (Fin.elim0 : Fin 0 → Fin l) p0 = a.val :=
    Prod.ext rfl (Subsingleton.elim _ _)
  have hQ : (Fin.elim0,p0.2) ∈ carrier Q := by
    have he : (show Point (M := M) 0 l from (Fin.elim0,p0.2)) = q.val.1 :=
      Prod.ext (Subsingleton.elim _ _) rfl
    exact (congrArg (fun z : Point (M := M) 0 l => z ∈ carrier Q) he).mpr q.property.1
  let p : H := ⟨p0,(L.source_shape p0).mpr
    ⟨(congrArg (fun z : Point (M := M) 1 0 => z ∈ carrier A) hP0).mpr a.property,hQ⟩⟩
  let k := L.special.toMap p
  let u : headImage L.target := Map.toImage (headKeyMap L.target) k
  refine ⟨u,Subtype.ext ?_⟩
  rw [head_product_map_value]
  have hComm : retainVFLabels L.projection k.val = v.val := by
    have hpa : (⟨retainVFLabels (Fin.elim0 : Fin 0 → Fin l) p.val,
      ((L.source_shape p.val).mp p.property).1⟩ : A) = a := Subtype.ext hP0
    exact (L.commutes p).trans ((congrArg (fun x : A => (T.toMap x).val) hpa).trans
      (congrArg Subtype.val (T.apply_inverse v)))
  have hKey : headKey k.val = u.val := (headKeyMap_apply L.target k).symm
  refine Prod.ext (Prod.ext (Subsingleton.elim _ _) ?_) (Prod.ext (Subsingleton.elim _ _) ?_)
  · funext j
    have h := congrFun (L.parameters p) j
    change u.val.2 (Fin.natAdd 1 (L.carried j)) = q.val.1.2 j
    rw [← hKey]
    simpa only [headKey,Fin.append_right,Function.comp_apply,p,p0] using h
  · have hV : headKey v.val = q.val.2 := (headKeyMap_apply B v).symm.trans hv
    have hOld := congrArg headKey hComm
    have hLabels := congrArg Prod.snd (hOld.trans hV)
    funext j
    cases j using Fin.addCases with
    | left j =>
      have hj : j = 0 := Subsingleton.elim _ _
      subst j
      have h := congrFun hLabels (Fin.castAdd b 0)
      change u.val.2 (L.headProjection (Fin.castAdd b 0)) = q.val.2.2 (Fin.castAdd b 0)
      rw [← hKey]
      simpa only [headKey,headProjection,Fin.append_left,retainVFLabels,vfAt] using h
    | right j =>
      have h := congrFun hLabels (Fin.natAdd 1 j)
      change u.val.2 (L.headProjection (Fin.natAdd 1 j)) = q.val.2.2 (Fin.natAdd 1 j)
      rw [← hKey]
      simpa only [headKey,headProjection,Fin.append_right,retainVFLabels,Function.comp_apply] using h

theorem head_product_map_bijective (L : RVParameterSpecialPreparation T H Q P) :
    Function.Bijective L.headProductMap := ⟨L.head_product_map_injective,L.head_product_map_surjective⟩

end RVParameterSpecialPreparation
end IntegrationInACVF.Section7
