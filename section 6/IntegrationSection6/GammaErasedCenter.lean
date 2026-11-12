import IntegrationSection6.GammaScalarClosure
import IntegrationSection6.FocusCenterAlgebraicity
import IntegrationSection6.GammaGlobalRestriction

/-! Descend a genuine Gamma focus centre after erasing the active VF
coordinate. The full invariant graph, and hence original-real-base scalar
algebraicity, descends without introducing any representative parameters. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.DefinableGeometry.Space.prod
  SpecialTransformations.Section4.realSpace SpecialTransformations.Milestone0.sortEval
  SpecialTransformations.Section4.vfSpace SpecialTransformations.Section4.rvSpace
  SpecialTransformations.DefinableGeometry.Space.ofEmbedding
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters SpecialTransformations.Section5
namespace IntegrationInACVF.Section6
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {S : Set M} {n m : ℕ}
variable {A : DefSet (M := M) S n m} {i : Fin n} {k : Fin m}

def centerPointMap (D : Focus A i k) := Map.comp (scalarPointMap S) D.centerMap

theorem centerPointMap_constant (D : Focus A i k) (a b : D.active)
    (he : (erasePointMap D.active i a).val = (erasePointMap D.active i b).val) :
    centerPointMap D a = centerPointMap D b := by
  have hc := D.independent a.val a.property b.val b.property he
  apply Subtype.ext
  apply Prod.ext
  · change ![D.center a.val] = ![D.center b.val]
    rw [hc]
  · exact Subsingleton.elim _ _

def erasedCenterPointMap (D : Focus A i k) :=
  Map.descend (erasePointMap D.active i) (centerPointMap D) (centerPointMap_constant D)

def erasedCenterValue (D : Focus A i k) (b : Map.image (erasePointMap D.active i)) : VF (M := M) :=
  (erasedCenterPointMap D b).val.1 0

@[simp] theorem erasedCenterValue_apply (D : Focus A i k) (a : D.active) :
    erasedCenterValue D (Map.toImage (erasePointMap D.active i) a) = D.center a.val := by
  unfold erasedCenterValue erasedCenterPointMap
  rw [Map.descend_apply]
  rfl

theorem erasedCenterValue_gamma (D : Focus A i k)
    (hA : GammaSetDefinable B (carrier A)) (hD : GammaFocusDefinable B D) :
    GammaScalarGraphDefinable B (fun p y =>
      ∃ b : Map.image (erasePointMap D.active i), b.val = p ∧ erasedCenterValue D b = y) := by
  let L := gammaLogicInput B
  have hActive : GammaSetDefinable B (carrier D.active) := L.inter hA hD.1
  have hErase := gamma_map_graph_of_global_formula (erasePointMap D.active i)
    (erasePointMap (PresentedSet.univ (pointSpace n m) B.real) i) hActive (fun _ => rfl)
  have h := L.comp_graph (L.swap_graph hErase) hD.2
  apply GammaGraphDefinable.congr h
  intro p q
  constructor
  · rintro ⟨z,⟨a,ha,hp⟩,_,hq⟩
    refine ⟨Map.toImage (erasePointMap D.active i) a,hp,?_⟩
    rw [erasedCenterValue_apply]
    exact (congrArg D.center ha).trans hq.symm
  · rintro ⟨b,hb,hq⟩
    obtain ⟨a,ha⟩ := b.property
    have he : b = Map.toImage (erasePointMap D.active i) a := Subtype.ext ha.symm
    rw [he,erasedCenterValue_apply] at hq
    exact ⟨a.val,⟨a,rfl,ha.trans hb⟩,a.property,hq.symm⟩

theorem gamma_center_algebraic_erased (D : Focus A i k)
    (hA : GammaSetDefinable B (carrier A)) (hD : GammaFocusDefinable B D) (a : D.active) :
    AlgebraicAt (B.real ∪ Set.range (fun j => ((erase i a.val).1 j).val)) .vf (D.center a.val).val := by
  have h := gamma_scalar_value_algebraic (erasedCenterValue D) (erasedCenterValue_gamma D hA hD)
    (Map.toImage (erasePointMap D.active i) a)
  rw [erasedCenterValue_apply] at h
  exact h

end IntegrationInACVF.Section6
