import IntegrationSection5.RelativeSpecialRestriction
import IntegrationSection5.HeadPreparation

/-! Inverse membership constancy restricts an ambient preparation to an
actual source set with head-saturated image. -/
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
variable {S : Set M} {n m l : ℕ}

theorem restrictPointImage_headSaturated {X : DefSet (M := M) S (n+1) m}
    {Y : DefSet (M := M) S (n+1) l} (f : Map X Y) (hf : Function.Bijective f)
    (hY : HeadSaturated (carrier Y)) (A : DefSet (M := M) S (n+1) m) (hAX : carrier A ⊆ carrier X)
    (hUniform : ∀ b c : Y, SameRV b.val c.val → TailEq b.val c.val →
      ((Map.inverse f hf b).val ∈ carrier A ↔ (Map.inverse f hf c).val ∈ carrier A)) :
    HeadSaturated (carrier (restrictPointImage f A hAX)) := by
  rintro p ⟨a,rfl⟩ x hx
  let b := f ⟨a.val,hAX a.property⟩
  let c : Y := ⟨replace 0 b.val x,hY b.val b.property x hx⟩
  have he : SameRV b.val c.val := sameRV_replace 0 b.val x hx
  have ht : TailEq b.val c.val := by intro j; simp [c,replace,vfAt,Fin.succ_ne_zero]
  have hb : (Map.inverse f hf b).val ∈ carrier A := by
    change (Map.inverse f hf (f ⟨a.val,hAX a.property⟩)).val ∈ carrier A
    rw [Map.inverse_apply]
    exact a.property
  have hc := (hUniform b c he ht).mp hb
  let a' : A := ⟨(Map.inverse f hf c).val,hc⟩
  have hax : (⟨a'.val,hAX a'.property⟩ : X) = Map.inverse f hf c := Subtype.ext rfl
  refine ⟨a',?_⟩
  change (f ⟨a'.val,hAX a'.property⟩).val = replace 0 b.val x
  rw [hax,Map.apply_inverse]

end IntegrationInACVF.Section5
