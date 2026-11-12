import IntegrationSection5.GammaMapPresentation

/-! Full original-Gamma sets and graphs have real presentations over the
whole model. This changes only an internal presentation; the mathematical
base stays unchanged and no smallness bound on internal codes is used. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section5
namespace IntegrationInACVF.Section6
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {n m u v : ℕ}

theorem gammaSet_univ_definable {A : Set (Point (M := M) n m)} (hA : GammaSetDefinable B A) :
    SetDefinable (pointSpace n m) Set.univ A := by
  obtain ⟨d,t,_,C,hC⟩ := gammaPresentationInput B A hA
  exact hC ▸ SetDefinable.mono (pointSpace n m) (setDefinable C) (Set.subset_univ _)

def gammaDefSetUniv (A : Set (Point (M := M) n m)) (hA : GammaSetDefinable B A) :
    DefSet (M := M) Set.univ n m := PresentedSet.mk A (gammaSet_univ_definable hA)

theorem gammaGraph_univ_definable {r : Point (M := M) n m → Point (M := M) u v → Prop}
    (hr : GammaGraphDefinable B r) : RelationDefinable (pointSpace n m) (pointSpace u v) Set.univ r := by
  obtain ⟨d,t,hr⟩ := hr.real_specialize
  exact RelationDefinable.mono _ _ hr (Set.subset_univ _)

end IntegrationInACVF.Section6
