import IntegrationSection5.UnaryFocusImages
import IntegrationSection5.PulledFocusGeometry

/-! Unary special bijections preserve a zero VF coordinate. In particular,
a point hit by a focus remains zero in every later special transformation. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section5

namespace IntegrationInACVF.Section5

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {S : Set M} {m l : ℕ}
variable {A : DefSet (M := M) S 1 m} {B : DefSet (M := M) S 1 l}

theorem unary_focus_preserves_zero {j : Fin 1} {k : Fin m} (D : Focus A j k) (a : A)
    (ha0 : vfAt a.val 0 = 0) : vfAt (D.toFocusGeometry.eta a.val) 0 = 0 := by
  have hj : j = 0 := Subsingleton.elim _ _
  subst j
  by_cases ha : a.val ∈ D.locus
  · have hc : D.center a.val = 0 := by
      apply (CanonicalRV.encodedRv_zero_iff _).mp
      have h := congrArg Subtype.val (D.center_sameRV a.val ⟨a.property, ha⟩)
      change iRv (D.center a.val).val = iRv (vfAt a.val 0).val at h
      rw [ha0] at h
      exact h.trans (RVCalc.rv_zero_eq hM)
    rw [FocusGeometry.eta, ite_eq_left ha]
    change vfAt a.val 0 - D.center a.val = 0
    rw [ha0, hc, sub_self]
  · rw [FocusGeometry.eta, ite_eq_right ha]
    exact ha0

theorem unary_primitive_preserves_zero (p : Primitive S 1 A B) (a : A)
    (ha0 : vfAt a.val 0 = 0) : vfAt (p.toMap a).val 0 = 0 := by
  cases p with
  | canonical A => exact ha0
  | centripetal D => exact unary_focus_preserves_zero D a ha0

theorem unary_chain_preserves_zero (T : Chain S 1 A B) (a : A)
    (ha0 : vfAt a.val 0 = 0) : vfAt (T.toMap a).val 0 = 0 := by
  induction T with
  | nil A => exact ha0
  | cons p tail ih => exact ih (p.toMap a) (unary_primitive_preserves_zero p a ha0)

theorem unary_special_preserves_zero (T : SpecialBijection A B) (a : A)
    (ha0 : vfAt a.val 0 = 0) : vfAt (T.toMap a).val 0 = 0 :=
  unary_chain_preserves_zero T.chain a ha0

theorem unary_focus_section_zero {k : Fin m} (D : Focus A 0 k)
    (hA : IsRVPullback (carrier A)) (a : A) (ha : a.val ∈ D.locus) :
    vfAt ((SpecialBijection.centripetal D).toMap (focusSectionMap D hA a)).val 0 = 0 := by
  let b := focusSectionMap D hA a
  have hb : b.val ∈ D.locus := (focusSection_locus D hA a).mpr ha
  have hc : D.center b.val = D.center a.val :=
    unary_focus_center_eq D b a hb (focusSectionMap_sameRV D hA a)
  change vfAt (D.toFocusGeometry.eta b.val) 0 = 0
  rw [FocusGeometry.eta, ite_eq_left hb]
  change vfAt b.val 0 - D.center b.val = 0
  rw [hc]
  have hcoord : vfAt b.val 0 = D.center a.val := by
    have h := focusSectionMap_active D hA a ha
    have hh := congrArg (fun p : Point (M := M) 1 m => vfAt p 0) h
    exact hh
  rw [hcoord, sub_self]

theorem unary_tail_focus_section_zero {k : Fin m} (D : Focus A 0 k)
    (hA : IsRVPullback (carrier A)) (T : Chain S 1 D.etaImage B)
    (a : A) (ha : a.val ∈ D.locus) :
    vfAt (T.toMap ((SpecialBijection.centripetal D).toMap (focusSectionMap D hA a))).val 0 = 0 :=
  unary_chain_preserves_zero T _ (unary_focus_section_zero D hA a ha)

end IntegrationInACVF.Section5
