module

public import Integration7.RVLabelConstraintHeadProjections

@[expose] public section

/-! Actual definable factor maps for a preparation with shared RV labels.
Their joint image will retain the equality of the overlapping labels. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.DefinableGeometry.Space.prod
  SpecialTransformations.Section4.realSpace SpecialTransformations.Milestone0.sortEval
  SpecialTransformations.Section4.vfSpace SpecialTransformations.Section4.rvSpace
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3.GammaParameters SpecialTransformations.Section5
open IntegrationInACVF.Section5

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {P : Base (M := M)} {S : Set M} {a b l : ℕ}
variable {A : DefSet (M := M) S 1 a} {B : DefSet (M := M) S 1 b}
variable {ρ : Fin a → Fin l}
variable {T : SpecialBijection A B} {H : DefSet (M := M) S 1 l} {Q : DefSet (M := M) S 0 l}

namespace RVLabelConstraintSpecialPreparation

def headPreparedMap (L : RVLabelConstraintSpecialPreparation T H Q ρ P) : Map (headImage L.target) (headImage B) :=
  let J : Map (headImage L.target) (PresentedSet.univ (pointSpace (M := M) 0 (1+L.arity)) S) :=
    Map.inclusion (fun _ _ => Set.mem_univ _)
  mapIntoSubset (Map.comp (rvCoordinatePointMap L.headProjection S) J) (headImage B) L.head_projection_mem

def headParameterMap (L : RVLabelConstraintSpecialPreparation T H Q ρ P) : Map (headImage L.target) Q :=
  let J : Map (headImage L.target) (PresentedSet.univ (pointSpace (M := M) 0 (1+L.arity)) S) :=
    Map.inclusion (fun _ _ => Set.mem_univ _)
  mapIntoSubset (Map.comp (rvCoordinatePointMap L.headParameters S) J) Q L.head_parameters_mem

def headProductMap (L : RVLabelConstraintSpecialPreparation T H Q ρ P) :
    Map (headImage L.target) (PresentedSet.prod Q (headImage B)) :=
  Map.pair L.headParameterMap L.headPreparedMap

theorem head_product_map_value (L : RVLabelConstraintSpecialPreparation T H Q ρ P) (p : headImage L.target) :
    (L.headProductMap p).val = ((Fin.elim0,p.val.2 ∘ L.headParameters),(Fin.elim0,p.val.2 ∘ L.headProjection)) := rfl

end RVLabelConstraintSpecialPreparation
end IntegrationInACVF.Section7
