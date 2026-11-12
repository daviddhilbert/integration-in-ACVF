import IntegrationSection6.GammaFiniteGraphObjects
import IntegrationSection6.GammaPresentationTotalVolume

/-! The entire RV[d] tuple space with identity volume is an actual finite
index object, even though its underlying set is infinite. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.DefinableGeometry.Space.prod
  SpecialTransformations.Section4.realSpace SpecialTransformations.Milestone0.sortEval
  SpecialTransformations.Section4.vfSpace SpecialTransformations.Section4.rvSpace
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
namespace IntegrationInACVF.Section6
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {d : ℕ}

abbrev IdentityIndexPresentation (B : Base (M := M)) (d : ℕ) :=
  GammaFiniteGraphPresentation B d d Set.univ (fun x y => x = y)

theorem gamma_identity_index_presentation_exists (B : Base (M := M)) (d : ℕ) :
    Nonempty (IdentityIndexPresentation B d) := by
  have hD : GammaSetDefinable B (Set.univ : Set (Point (M := M) 0 d)) :=
    (gammaLogicInput B).real_set _ (setDefinable (PresentedSet.univ (pointSpace (M := M) 0 d) B.real))
  have hR : GammaGraphDefinable B (fun (p q : Point (M := M) 0 d) => p.2 = q.2) := by
    apply GammaGraphDefinable.congr ((gammaLogicInput B).real_map_graph
      (Map.id (PresentedSet.univ (pointSpace (M := M) 0 d) B.real)))
    intro p q
    constructor
    · rintro ⟨x,hx,hq⟩
      exact congrArg Prod.snd (hx.symm.trans hq)
    · intro h
      exact ⟨⟨p,Set.mem_univ _⟩,rfl,Prod.ext (Subsingleton.elim _ _) h⟩
  apply exists_gammaFiniteGraphPresentation hD hR
  · intro x
    exact ⟨x.val,rfl,fun y hy => hy.symm⟩
  · intro y
    apply (Set.finite_singleton (⟨y,Set.mem_univ _⟩ : (Set.univ : Set (Fin d → RV (M := M))))).subset
    intro x hx
    exact Subtype.ext hx

theorem IdentityIndexPresentation.totalVolume_eq (BP : IdentityIndexPresentation B d)
    (x : Fin d → RV (M := M)) : BP.totalVolume x = x :=
  ((BP.totalVolume_graph x x).mp ((BP.graph_iff x x).mpr ⟨Set.mem_univ _,rfl⟩)).2

end IntegrationInACVF.Section6
