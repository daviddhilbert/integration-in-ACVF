import Integration7.RVParameterSpecialPreparations
import IntegrationSection6.MixedCoordinatePointMaps

/-! The head of a carried-parameter preparation projects to its original
unary contraction and to its complete retained parameter tuple. -/
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

def headProjection (L : RVParameterSpecialPreparation T H Q P) : Fin (1+b) → Fin (1+L.arity) :=
  Fin.append (m := 1) (n := b) (fun j : Fin 1 => Fin.castAdd L.arity j)
    (fun j : Fin b => Fin.natAdd 1 (L.projection j))

def headParameters (L : RVParameterSpecialPreparation T H Q P) : Fin l → Fin (1+L.arity) :=
  fun j => Fin.natAdd 1 (L.carried j)

theorem head_projection_mem (L : RVParameterSpecialPreparation T H Q P)
    (q : headImage L.target) : (Fin.elim0,q.val.2 ∘ L.headProjection) ∈ carrier (headImage B) := by
  obtain ⟨p,hp⟩ := q.property
  have hTarget := ((L.target_carrier p.val).mp p.property).1
  refine ⟨⟨retainVFLabels L.projection p.val,hTarget⟩,?_⟩
  refine (headKeyMap_apply B ⟨retainVFLabels L.projection p.val,hTarget⟩).trans ?_
  have hq := (headKeyMap_apply L.target p).symm.trans hp
  refine Prod.ext (Subsingleton.elim _ _) ?_
  funext j
  cases j using Fin.addCases with
  | left j =>
    have hj : j = 0 := Subsingleton.elim _ _
    subst j
    have h := congrFun (congrArg Prod.snd hq) (Fin.castAdd L.arity 0)
    change rv (vfAt p.val 0) = q.val.2 (L.headProjection (Fin.castAdd b 0))
    rw [headProjection,Fin.append_left]
    exact h
  | right j =>
    have h := congrFun (congrArg Prod.snd hq) (Fin.natAdd 1 (L.projection j))
    simp only [headKey,Fin.append_right,retainVFLabels,Function.comp_apply]
    rw [headProjection,Fin.append_right]
    simpa only [headKey,Fin.append_right] using h

theorem head_parameters_mem (L : RVParameterSpecialPreparation T H Q P)
    (q : headImage L.target) : (Fin.elim0,q.val.2 ∘ L.headParameters) ∈ carrier Q := by
  obtain ⟨p,hp⟩ := q.property
  have hTarget := ((L.target_carrier p.val).mp p.property).2
  have hq := (headKeyMap_apply L.target p).symm.trans hp
  have he : q.val.2 ∘ L.headParameters = p.val.2 ∘ L.carried := by
    funext j
    have h := congrFun (congrArg Prod.snd hq) (Fin.natAdd 1 (L.carried j))
    simpa only [headKey,Fin.append_right,Function.comp_apply,headParameters] using h.symm
  rw [he]
  exact hTarget

end RVParameterSpecialPreparation
end IntegrationInACVF.Section7
