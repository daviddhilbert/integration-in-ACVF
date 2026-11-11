import IntegrationSection5.GammaScalarUpdate
import IntegrationSection5.ScalarCoordinateRefinement

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.DefinableGeometry.Space.prod
  SpecialTransformations.Section4.realSpace SpecialTransformations.Milestone0.sortEval
  SpecialTransformations.Section4.vfSpace SpecialTransformations.Section4.rvSpace
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section5 SpecialTransformations.Section3
namespace IntegrationInACVF.Section5
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {G : GammaParameters.Base (M := M)} {n m u w : ℕ}
variable {A : Set (Point (M := M) n m)} {B : Set (Point (M := M) u w)}

theorem gamma_set_coordinate_scalar_graph (B : Set (Point (M := M) u w))
    (hB : GammaSetDefinable G B) (i : Fin u) :
    GammaScalarGraphDefinable G (fun p y => ∃ b : B, b.val = p ∧ vfAt b.val i = y) := by
  apply GammaGraphDefinable.congr ((gammaLogicInput G).restrict_graph hB
    ((gammaLogicInput G).real_map_graph (vfScalarPointMap G.real u w i)))
  intro p q
  constructor
  · rintro ⟨hp,b,hb,hq⟩
    have hh := congrArg (fun z : Point (M := M) 1 0 => vfAt z 0) hq
    change vfAt b.val i = vfAt q 0 at hh
    exact ⟨⟨p,hp⟩,rfl,hb ▸ hh⟩
  · rintro ⟨b,hb,hq⟩
    refine ⟨hb ▸ b.property,⟨b.val,Set.mem_univ _⟩,hb,?_⟩
    refine Prod.ext ?_ (Subsingleton.elim _ _)
    funext j
    fin_cases j
    exact hq

theorem gamma_iso_coordinate_scalar_graph (e : GammaIso G A B) (i : Fin u) :
    GammaScalarGraphDefinable G (fun p y => ∃ a : A, a.val = p ∧ vfAt (e.equiv a).val i = y) :=
  gamma_iso_precomp_scalar e (fun b => vfAt b.val i)
    (gamma_set_coordinate_scalar_graph B (e.target_definable (gammaLogicInput G)) i)

end IntegrationInACVF.Section5
