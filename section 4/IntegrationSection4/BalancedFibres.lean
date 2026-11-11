import IntegrationSection4.TranslationOffsets
import Section5.RootConstruction

/-! The two actual fibre identities in Definition 4.5 and their elementary
consequences. Open-ball and Gamma-linearity conditions are added by the
cell-level predicate; this module does not assert balanced-map existence. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false

set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.Milestone0.sortEval

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section5

namespace IntegrationInACVF.Section4.BalancedFibres

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

def translatedRV (t : RV (M := M)) (c : VF (M := M)) : Set (VF (M := M)) :=
  {x | rv (x-c) = t}

theorem translatedRV_eq_image (t : RV (M := M)) (c : VF (M := M)) :
    translatedRV t c = (fun x => x+c) '' {x : VF (M := M) | rv x = t} := by
  ext x
  constructor
  · intro hx
    exact ⟨x-c,hx,sub_add_cancel x c⟩
  · rintro ⟨y,hy,rfl⟩
    change rv (y+c-c) = t
    change rv y = t at hy
    rwa [add_sub_cancel_right]

theorem translatedRV_nonempty (t : RV (M := M)) (c : VF (M := M)) :
    (translatedRV t c).Nonempty := by
  obtain ⟨x,hx⟩ := CanonicalRV.encodedRv_surjective t
  refine ⟨x+c,?_⟩
  change rv (x+c-c) = t
  rw [add_sub_cancel_right]
  apply Subtype.ext
  exact congrArg Subtype.val hx

theorem centre_mem_iff (t : RV (M := M)) (c : VF (M := M)) :
    c ∈ translatedRV t c ↔ t = rv (0 : VF (M := M)) := by
  change rv (c-c) = t ↔ t = rv (0 : VF (M := M))
  rw [sub_self]
  exact eq_comm

theorem translatedRV_zero (c : VF (M := M)) :
    translatedRV (rv (0 : VF (M := M))) c = {c} := by
  ext x
  change rv (x-c) = rv (0 : VF (M := M)) ↔ x = c
  rw [rv_eq_zero_iff,sub_eq_zero]

theorem translatedRV_parameter_unique (c : VF (M := M)) (t u : RV (M := M))
    (h : translatedRV t c = translatedRV u c) : t = u := by
  obtain ⟨x,hx⟩ := translatedRV_nonempty t c
  have hu : x ∈ translatedRV u c := h ▸ hx
  exact hx.symm.trans hu

def fibre (R : Set (VF (M := M) × VF (M := M))) (a : VF (M := M)) : Set (VF (M := M)) :=
  {b | (a,b) ∈ R}

structure HasBalancedFibres (D E : Set (VF (M := M)))
    (R : Set (VF (M := M) × VF (M := M))) (f : VF (M := M) → VF (M := M))
    (t₁ t₂ : RV (M := M)) : Prop where
  bijective : Set.BijOn f D E
  subset : R ⊆ D ×ˢ E
  vertical : ∀ a ∈ D, fibre R a = translatedRV t₂ (f a)
  horizontal : ∀ a ∈ D, D ∩ f ⁻¹' fibre R a = {x | rv (a-x) = t₁}

variable {D E : Set (VF (M := M))} {R : Set (VF (M := M) × VF (M := M))}
variable {f : VF (M := M) → VF (M := M)} {t₁ t₂ : RV (M := M)}

theorem paradigms_degenerate_together (h : HasBalancedFibres D E R f t₁ t₂)
    (a : VF (M := M)) (ha : a ∈ D) :
    t₁ = rv (0 : VF (M := M)) ↔ t₂ = rv (0 : VF (M := M)) := by
  have hH := Set.ext_iff.mp (h.horizontal a ha) a
  have hV := Set.ext_iff.mp (h.vertical a ha) (f a)
  have hH' : f a ∈ fibre R a ↔ rv (0 : VF (M := M)) = t₁ := by
    simpa only [Set.mem_inter_iff,Set.mem_preimage,Set.mem_setOf_eq,ha,true_and,sub_self] using hH
  have hV' : f a ∈ fibre R a ↔ rv (0 : VF (M := M)) = t₂ := by
    simpa only [translatedRV,Set.mem_setOf_eq,sub_self] using hV
  exact (eq_comm.trans hH'.symm).trans (hV'.trans eq_comm)

theorem graph_of_degenerate (h : HasBalancedFibres D E R f t₁ t₂)
    (ht : t₂ = rv (0 : VF (M := M))) : R = {p | p.1 ∈ D ∧ p.2 = f p.1} := by
  ext p
  constructor
  · intro hp
    have ha := (h.subset hp).1
    have hf : p.2 ∈ fibre R p.1 := hp
    rw [h.vertical p.1 ha,ht,translatedRV_zero] at hf
    exact ⟨ha,hf⟩
  · rintro ⟨ha,hb⟩
    have hrow := h.vertical p.1 ha
    rw [ht,translatedRV_zero] at hrow
    change p.2 ∈ fibre R p.1
    rw [hrow]
    exact hb

theorem positioning_not_in_fibre (h : HasBalancedFibres D E R f t₁ t₂)
    (ht : t₂ ≠ rv (0 : VF (M := M))) (a : VF (M := M)) (ha : a ∈ D) :
    f a ∉ fibre R a := by
  rw [h.vertical a ha,centre_mem_iff]
  exact ht

theorem second_paradigm_unique (h : HasBalancedFibres D E R f t₁ t₂)
    {u₁ u₂ : RV (M := M)} (k : HasBalancedFibres D E R f u₁ u₂)
    (a : VF (M := M)) (ha : a ∈ D) : t₂ = u₂ :=
  translatedRV_parameter_unique (f a) t₂ u₂ ((h.vertical a ha).symm.trans (k.vertical a ha))

end IntegrationInACVF.Section4.BalancedFibres
