import IntegrationSection5.GammaPreparation
import Section3.GammaSupport

/-! Intersection and source predicates for complete invariant Gamma graphs.
All operations retain the full preimage of the original named values. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.DefinableGeometry.Space.prod
  SpecialTransformations.Section4.realSpace SpecialTransformations.Milestone0.sortEval
  SpecialTransformations.Section4.vfSpace SpecialTransformations.Section4.rvSpace

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section5

namespace IntegrationInACVF.Section5

variable {M : Type} [sM : LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {P : SpecialTransformations.Section3.GammaParameters.Base (M := M)}
variable {S : Set M} {n m u w : ℕ}

theorem gammaPointCode_injective :
    Function.Injective (gammaPointCode (M := M) (n := n) (m := m)) := by
  intro p q h
  apply Prod.ext
  · funext i
    apply Subtype.ext
    simpa only [gammaPointCode, vfAt, Fin.append_left] using congrFun h (Fin.castAdd m i)
  · funext i
    apply Subtype.ext
    simpa only [gammaPointCode, Fin.append_right] using congrFun h (Fin.natAdd n i)

theorem gammaGraph_inter
    {r t : Point (M := M) n m → Point (M := M) u w → Prop}
    (hr : GammaGraphDefinable P r) (ht : GammaGraphDefinable P t) :
    GammaGraphDefinable P (fun p q => r p q ∧ t p q) := by
  have h := hr.inter ht
  unfold GammaGraphDefinable
  convert h using 1
  ext z
  constructor
  · rintro ⟨p,q,⟨hp,hq⟩,rfl⟩
    exact ⟨⟨p,q,hp,rfl⟩,⟨p,q,hq,rfl⟩⟩
  · rintro ⟨⟨p,q,hp,rfl⟩,⟨a,b,hq,he⟩⟩
    have ha : a = p := gammaPointCode_injective (by
      funext i
      simpa only [Fin.append_left] using congrFun he (Fin.castAdd (u+w) i))
    have hb : b = q := gammaPointCode_injective (by
      funext i
      simpa only [Fin.append_right] using congrFun he (Fin.natAdd (n+m) i))
    subst a; subst b
    exact ⟨p,q,⟨hp,hq⟩,rfl⟩

theorem gamma_inverse_map_graph {A : DefSet (M := M) S n m}
    {B : DefSet (M := M) S u w} (f : Map A B) (hf : Function.Bijective f)
    (h : GammaGraphDefinable P (pointMapGraph f)) :
    GammaGraphDefinable P (pointMapGraph (Map.inverse f hf)) := by
  apply GammaGraphDefinable.congr ((gammaLogicInput P).swap_graph h)
  intro q p
  constructor
  · rintro ⟨a,rfl,he⟩
    exact ⟨f a,he,congrArg Subtype.val (Map.inverse_apply f hf a)⟩
  · rintro ⟨b,rfl,he⟩
    exact ⟨Map.inverse f hf b,he,congrArg Subtype.val (Map.apply_inverse f hf b)⟩

theorem gamma_map_preimage {A : DefSet (M := M) S n m}
    {B : DefSet (M := M) S u w} (f : Map A B)
    (hf : GammaGraphDefinable P (pointMapGraph f))
    {C : Set (Point (M := M) u w)} (hC : GammaSetDefinable P C) :
    GammaSetDefinable P {p | ∃ a : A, a.val = p ∧ (f a).val ∈ C} := by
  have h := (gammaLogicInput P).image_graph
    ((gammaLogicInput P).restrict_graph hC ((gammaLogicInput P).swap_graph hf))
  convert h using 1
  ext p
  constructor
  · rintro ⟨a,rfl,ha⟩
    exact ⟨(f a).val,ha,a,rfl,rfl⟩
  · rintro ⟨q,hq,a,rfl,he⟩
    exact ⟨a,rfl,he.symm ▸ hq⟩

theorem gamma_sameRV_graph :
    GammaGraphDefinable P (fun p q : Point (M := M) n m => SameRV p q) := by
  let L := gammaLogicInput P
  let A := PresentedSet.univ (pointSpace (M := M) n m) P.real
  let f := Map.comp (flattenKeyMap (PresentedSet.univ (keySpace n m) P.real)) (keyMap A)
  have hf := L.real_map_graph f
  apply GammaGraphDefinable.congr (L.comp_graph hf (L.swap_graph hf))
  intro p q
  constructor
  · rintro ⟨z,⟨a,ha,haz⟩,⟨b,hb,hbz⟩⟩
    have he : (f a).val = (f b).val := haz.trans hbz.symm
    have ht := congrArg Prod.snd he
    change Fin.append (key a.val).1 (key a.val).2 =
      Fin.append (key b.val).1 (key b.val).2 at ht
    rw [ha,hb] at ht
    apply Prod.ext
    · funext i
      simpa only [Fin.append_left] using congrFun ht (Fin.castAdd m i)
    · funext i
      simpa only [Fin.append_right] using congrFun ht (Fin.natAdd n i)
  · intro he
    let a : A := ⟨p,Set.mem_univ _⟩
    let b : A := ⟨q,Set.mem_univ _⟩
    refine ⟨(f a).val,⟨a,rfl,rfl⟩,b,rfl,?_⟩
    refine Prod.ext (Subsingleton.elim _ _) ?_
    change Fin.append (key q).1 (key q).2 = Fin.append (key p).1 (key p).2
    rw [he]

end IntegrationInACVF.Section5
