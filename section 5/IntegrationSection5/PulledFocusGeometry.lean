import IntegrationSection5.FocusSection
import Section5.TransformGeometry

/-! Pull a target focus back through a contractible unary bijection.
The selected source locus is a union of actual RV cells. The section and
locus below are constructed from the supplied maps, not choice hypotheses. -/

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

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {S : Set M} {m l : ℕ}
variable {A : DefSet (M := M) S 1 m} {B : DefSet (M := M) S 1 l}
variable {k : Fin l}

theorem focusSection_locus (D : Focus B 0 k) (hB : IsRVPullback (carrier B)) (b : B) :
    (focusSectionMap D hB b).val ∈ D.locus ↔ b.val ∈ D.locus :=
  mem_iff_sameRV D.locus_pullback (focusSectionMap_sameRV D hB b)

theorem unary_focusSection_idempotent
    (D : Focus B 0 k) (hB : IsRVPullback (carrier B)) (b : B) :
    focusSectionMap D hB (focusSectionMap D hB b) = focusSectionMap D hB b := by
  by_cases hb : b.val ∈ D.locus
  · exact unary_focusSectionMap_eq D hB (focusSectionMap D hB b) b
      ((focusSection_locus D hB b).mpr hb) (focusSectionMap_sameRV D hB b)
  · rw [focusSectionMap_inactive D hB b hb]
    exact focusSectionMap_inactive D hB b hb

def pulledFocusSection (f : Map A B) (hf : Function.Bijective f)
    (D : Focus B 0 k) (hB : IsRVPullback (carrier B)) : Map A A :=
  Map.comp (Map.inverse f hf) (Map.comp (focusSectionMap D hB) f)

theorem map_pulledFocusSection (f : Map A B) (hf : Function.Bijective f)
    (D : Focus B 0 k) (hB : IsRVPullback (carrier B)) (a : A) :
    f (pulledFocusSection f hf D hB a) = focusSectionMap D hB (f a) :=
  Map.apply_inverse f hf _

theorem pulledFocusSection_constant (f : Map A B) (hf : Function.Bijective f)
    (hc : Contractible f) (D : Focus B 0 k) (hB : IsRVPullback (carrier B))
    (a b : A) (ha : (f a).val ∈ D.locus) (hab : SameRV a.val b.val) :
    pulledFocusSection f hf D hB a = pulledFocusSection f hf D hB b := by
  exact congrArg (Map.inverse f hf) (unary_focusSectionMap_eq D hB (f a) (f b) ha (hc a b hab))

theorem pulledFocusSection_idempotent (f : Map A B) (hf : Function.Bijective f)
    (D : Focus B 0 k) (hB : IsRVPullback (carrier B)) (a : A) :
    pulledFocusSection f hf D hB (pulledFocusSection f hf D hB a) =
      pulledFocusSection f hf D hB a := by
  apply hf.1
  rw [map_pulledFocusSection, map_pulledFocusSection, unary_focusSection_idempotent]

def PullSelected (f : Map A B) (hf : Function.Bijective f)
    (D : Focus B 0 k) (hB : IsRVPullback (carrier B)) (a : A) : Prop :=
  (f a).val ∈ D.locus ∧ SameRV (pulledFocusSection f hf D hB a).val a.val

theorem pullSelected_sameRV (f : Map A B) (hf : Function.Bijective f)
    (hc : Contractible f) (D : Focus B 0 k) (hB : IsRVPullback (carrier B))
    (a b : A) (ha : PullSelected f hf D hB a) (hab : SameRV a.val b.val) :
    PullSelected f hf D hB b := by
  refine ⟨(mem_iff_sameRV D.locus_pullback (hc a b hab)).mp ha.1, ?_⟩
  rw [← pulledFocusSection_constant f hf hc D hB a b ha.1 hab]
  exact ha.2.trans hab

theorem pullSelected_section (f : Map A B) (hf : Function.Bijective f)
    (D : Focus B 0 k) (hB : IsRVPullback (carrier B)) (a : A)
    (ha : (f a).val ∈ D.locus) : PullSelected f hf D hB (pulledFocusSection f hf D hB a) := by
  constructor
  · rw [map_pulledFocusSection]
    exact (focusSection_locus D hB (f a)).mpr ha
  · rw [pulledFocusSection_idempotent]
    rfl

def pulledFocusLocus (f : Map A B) (hf : Function.Bijective f)
    (D : Focus B 0 k) (hB : IsRVPullback (carrier B)) : Set (Point (M := M) 1 m) :=
  {p | ∃ a : A, a.val = p ∧ PullSelected f hf D hB a}

theorem pulledFocusLocus_pullback (f : Map A B) (hf : Function.Bijective f)
    (hc : Contractible f) (D : Focus B 0 k)
    (hA : IsRVPullback (carrier A)) (hB : IsRVPullback (carrier B)) :
    IsRVPullback (pulledFocusLocus f hf D hB) := by
  apply (isRVPullback_iff _).mpr
  rintro p ⟨a, rfl, ha⟩ q hpq
  let b : A := ⟨q, (isRVPullback_iff _).mp hA a.val a.property q hpq⟩
  exact ⟨b, rfl, pullSelected_sameRV f hf hc D hB a b ha hpq⟩

theorem pulledFocusLocus_subset (f : Map A B) (hf : Function.Bijective f)
    (D : Focus B 0 k) (hB : IsRVPullback (carrier B)) :
    pulledFocusLocus f hf D hB ⊆ hull (carrier A) := by
  rintro p ⟨a, rfl, ha⟩
  exact subset_hull _ a.property

def pulledFocusCentre (f : Map A B) (hf : Function.Bijective f)
    (D : Focus B 0 k) (hB : IsRVPullback (carrier B)) (p : Point (M := M) 1 m) : VF (M := M) :=
  if hp : p ∈ carrier A then vfAt (pulledFocusSection f hf D hB ⟨p, hp⟩).val 0 else 0

theorem pulledFocusCentre_apply (f : Map A B) (hf : Function.Bijective f)
    (D : Focus B 0 k) (hB : IsRVPullback (carrier B)) (a : A) :
    pulledFocusCentre f hf D hB a.val = vfAt (pulledFocusSection f hf D hB a).val 0 := by
  simp only [pulledFocusCentre, dite_eq_left a.property]

theorem unary_sameRV_of_tagged_labels {j : Fin m} (hTag : Tagged (carrier A) 0 j)
    (a b : A) (he : a.val.2 = b.val.2) : SameRV a.val b.val := by
  apply (sameRV_iff _ _).mpr
  refine ⟨?_, he⟩
  intro i
  have hi : i = 0 := Subsingleton.elim _ _
  subst i
  exact (hTag a.val a.property).symm.trans ((congrFun he j).trans (hTag b.val b.property))

theorem pulledFocusCentre_independent (f : Map A B) (hf : Function.Bijective f)
    (hc : Contractible f) (D : Focus B 0 k) (hB : IsRVPullback (carrier B))
    {j : Fin m} (hTag : Tagged (carrier A) 0 j)
    (p : Point (M := M) 1 m) (hp : p ∈ carrier A ∩ pulledFocusLocus f hf D hB)
    (q : Point (M := M) 1 m) (hq : q ∈ carrier A ∩ pulledFocusLocus f hf D hB)
    (he : erase 0 p = erase 0 q) :
    pulledFocusCentre f hf D hB p = pulledFocusCentre f hf D hB q := by
  let a : A := ⟨p, hp.1⟩
  let b : A := ⟨q, hq.1⟩
  have hlabels0 := congrArg (fun z : Point (M := M) 1 m => z.2) he
  have hlabels : a.val.2 = b.val.2 := hlabels0
  have hab := unary_sameRV_of_tagged_labels hTag a b hlabels
  have hsel : PullSelected f hf D hB a := by
    obtain ⟨a', ha', hsel⟩ := hp.2
    have haa : a' = a := Subtype.ext ha'
    exact haa ▸ hsel
  have hcenter := congrArg (fun a : A => vfAt a.val 0)
    (pulledFocusSection_constant f hf hc D hB a b hsel.1 hab)
  exact (pulledFocusCentre_apply f hf D hB a).trans
    (hcenter.trans (pulledFocusCentre_apply f hf D hB b).symm)

theorem pulledFocusCentre_mem (f : Map A B) (hf : Function.Bijective f)
    (D : Focus B 0 k) (hB : IsRVPullback (carrier B))
    (p : Point (M := M) 1 m) (hp : p ∈ carrier A ∩ pulledFocusLocus f hf D hB) :
    replace 0 p (pulledFocusCentre f hf D hB p) ∈ pulledFocusLocus f hf D hB := by
  let a : A := ⟨p, hp.1⟩
  have hsel : PullSelected f hf D hB a := by
    obtain ⟨a', ha', hsel⟩ := hp.2
    have haa : a' = a := Subtype.ext ha'
    exact haa ▸ hsel
  refine ⟨pulledFocusSection f hf D hB a, ?_, pullSelected_section f hf D hB a hsel.1⟩
  have hlabel := ((sameRV_iff _ _).mp hsel.2).2
  refine Prod.ext ?_ hlabel
  funext i
  have hi : i = 0 := Subsingleton.elim _ _
  subst i
  change vfAt (pulledFocusSection f hf D hB a).val 0 = pulledFocusCentre f hf D hB a.val
  exact (pulledFocusCentre_apply f hf D hB a).symm

def pulledFocusGeometry (f : Map A B) (hf : Function.Bijective f)
    (hc : Contractible f) (D : Focus B 0 k)
    (hA : IsRVPullback (carrier A)) (hB : IsRVPullback (carrier B))
    {j : Fin m} (hTag : Tagged (carrier A) 0 j) : FocusGeometry (carrier A) 0 j where
  tagged := hTag
  locus := pulledFocusLocus f hf D hB
  locus_pullback := pulledFocusLocus_pullback f hf hc D hA hB
  locus_subset := pulledFocusLocus_subset f hf D hB
  center := pulledFocusCentre f hf D hB
  independent := pulledFocusCentre_independent f hf hc D hB hTag
  center_mem := pulledFocusCentre_mem f hf D hB

end IntegrationInACVF.Section5
