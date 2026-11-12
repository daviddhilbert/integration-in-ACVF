import IntegrationSection6.GammaRawCoproductSchemata
import IntegrationSection6.GammaIndexedFiniteObjects

/-! Full original-Gamma graphs for the native tags inside an RV-indexed
family. The index labels are preserved exactly. -/
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
variable {B : Base (M := M)} {p a b : ℕ}
local notation "N" => (@CanonicalStructure.normalize M sM)
local notation "hN" => (@CanonicalStructure.normalized_model M sM hM)

theorem gamma_indexed_rv_relation {r : Point (M := M) 0 a → Point (M := M) 0 b → Prop}
    (hr : GammaGraphDefinable B r) :
    GammaGraphDefinable B (fun (w : Point (M := M) 0 (p+a)) (y : Point (M := M) 0 (p+b)) =>
      indexedLeft w.2 = indexedLeft y.2 ∧ r (Fin.elim0,indexedRight w.2) (Fin.elim0,indexedRight y.2)) := by
  let par := rvCoordinatePointMap (Fin.castAdd a : Fin p → Fin (p+a)) B.real
  let par' := rvCoordinatePointMap (Fin.castAdd b : Fin p → Fin (p+b)) B.real
  let left := rvCoordinatePointMap (Fin.natAdd p : Fin a → Fin (p+a)) B.real
  let right := rvCoordinatePointMap (Fin.natAdd p : Fin b → Fin (p+b)) B.real
  let ident := @Map.id M sM _ B.real (PresentedSet.univ (pointSpace (M := M) 0 (p+a)) B.real)
  have h := ((gamma_global_map_graph par).preimage_maps ident par').inter (hr.preimage_maps left right)
  apply GammaGraphDefinable.congr h
  intro w y
  change (((Fin.elim0,indexedLeft w.2) = (Fin.elim0,indexedLeft y.2)) ∧ _) ↔ _
  exact and_congr ⟨fun he => congrArg Prod.snd he,fun he => Prod.ext (Subsingleton.elim _ _) he⟩ Iff.rfl

theorem append_blocks_eq_iff {Y : Type*} {p c : ℕ}
    (t : Fin p → Y) (u : Fin c → Y) (w : Fin (p+c) → Y) :
    Fin.append t u = w ↔ t = indexedLeft w ∧ u = indexedRight w := by
  constructor
  · intro h
    constructor
    · funext j
      simpa only [Fin.append_left,indexedLeft,Function.comp_apply] using congrFun h (Fin.castAdd c j)
    · funext j
      simpa only [Fin.append_right,indexedRight,Function.comp_apply] using congrFun h (Fin.natAdd p j)
  · rintro ⟨ht,hu⟩
    rw [ht,hu]
    exact Fin.append_castAdd_natAdd

theorem gamma_indexed_leftTag_graph :
    GammaGraphDefinable B (fun (w : Point (M := M) 0 (p+a))
      (y : Point (M := M) 0 (p+(1+(a+b)))) =>
      Fin.append (indexedLeft w.2) (@rvLeftTag M N hN a b (indexedRight w.2)) = y.2) := by
  have hRaw := gamma_rv_graph_from_tuple_formula (rawLeftTagGraph_definable B a b)
  have hr : GammaGraphDefinable B (fun (x : Point (M := M) 0 a) (y : Point (M := M) 0 (1+(a+b))) =>
      @rvLeftTag M N hN a b x.2 = y.2) := by
    apply GammaGraphDefinable.congr hRaw
    intro x y
    exact rawLeftTagGraph_tuple_iff B x.2 y.2
  have h := gamma_indexed_rv_relation (p := p) hr
  apply GammaGraphDefinable.congr h
  intro w y
  exact (append_blocks_eq_iff _ _ y.2).symm

theorem gamma_indexed_rightTag_graph :
    GammaGraphDefinable B (fun (w : Point (M := M) 0 (p+b))
      (y : Point (M := M) 0 (p+(1+(a+b)))) =>
      Fin.append (indexedLeft w.2) (@rvRightTag M N hN b a (indexedRight w.2)) = y.2) := by
  have hRaw := gamma_rv_graph_from_tuple_formula (rawRightTagGraph_definable B a b)
  have hr : GammaGraphDefinable B (fun (x : Point (M := M) 0 b) (y : Point (M := M) 0 (1+(a+b))) =>
      @rvRightTag M N hN b a x.2 = y.2) := by
    apply GammaGraphDefinable.congr hRaw
    intro x y
    exact rawRightTagGraph_tuple_iff B x.2 y.2
  have h := gamma_indexed_rv_relation (p := p) hr
  apply GammaGraphDefinable.congr h
  intro w y
  exact (append_blocks_eq_iff _ _ y.2).symm

end IntegrationInACVF.Section6
