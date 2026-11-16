module

public import IntegrationSection5.CoordinateFibreMaps
public import Section5.CoordinateLift

@[expose] public section

/-! Carrying additional RV labels through genuine focus transformations.
The VF coordinates are retained exactly; the projected original labels
determine the old focus and its centre. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.DefinableGeometry.Space.prod
  SpecialTransformations.Section4.realSpace SpecialTransformations.Milestone0.sortEval
  SpecialTransformations.Section4.vfSpace SpecialTransformations.Section4.rvSpace
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section5 IntegrationInACVF.Section5

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {S : Set M} {n m l : ℕ}

def retainVFLabels (ρ : Fin m → Fin l) (p : Point (M := M) n l) : Point (M := M) n m :=
  (p.1,p.2 ∘ ρ)

theorem same_rv_retain_vf_labels (ρ : Fin m → Fin l) {p q : Point (M := M) n l}
    (h : SameRV p q) : SameRV (retainVFLabels ρ p) (retainVFLabels ρ q) := by
  obtain ⟨hv,ht⟩ := (sameRV_iff _ _).mp h
  exact (sameRV_iff _ _).mpr ⟨hv,congrArg (fun r => r ∘ ρ) ht⟩

theorem retain_vf_labels_replace (ρ : Fin m → Fin l) (j : Fin n)
    (p : Point (M := M) n l) (x : VF (M := M)) :
    retainVFLabels ρ (replace j p x) = replace j (retainVFLabels ρ p) x := rfl

def retainVFLabelsMap (ρ : Fin m → Fin l) (A : DefSet (M := M) S n l) :
    Map A (PresentedSet.univ (pointSpace n m) S) :=
  Map.ofCodes A (retainVFLabels ρ)
    (fun z => Sum.elim (fun i => z (.inl i)) (fun i => z (.inr (ρ i))))
    (by intro i;cases i <;> exact rawProj S _)
    (by intro c;exact ⟨c.property.1,fun i => c.property.2 (ρ i)⟩)
    (by intro c;rfl)

theorem retain_vf_labels_preimage_definable (ρ : Fin m → Fin l)
    (D : Set (Point (M := M) n m)) (hD : SetDefinable (pointSpace n m) S D) :
    SetDefinable (pointSpace n l) S {p | retainVFLabels ρ p ∈ D} := by
  have h := Map.definable_preimage (retainVFLabelsMap ρ (PresentedSet.univ (pointSpace n l) S)) hD
  convert h using 1
  ext p
  exact ⟨fun hp => ⟨⟨p,Set.mem_univ _⟩,rfl,hp⟩,fun ⟨q,hq,hp⟩ => hq ▸ hp⟩

def rvLabelFocusGeometry {A : DefSet (M := M) S n m} {H : DefSet (M := M) S n l}
    {j : Fin n} {k : Fin m} (D : Focus A j k) (ρ : Fin m → Fin l)
    (hHA : ∀ p ∈ carrier H, retainVFLabels ρ p ∈ carrier A) :
    FocusGeometry (carrier H) j (ρ k) where
  tagged p hp := D.tagged (retainVFLabels ρ p) (hHA p hp)
  locus := {p | retainVFLabels ρ p ∈ D.locus} ∩ hull (carrier H)
  locus_pullback := isRVPullback_inter ((isRVPullback_iff _).mpr (by
    intro p hp q he
    exact (isRVPullback_iff _).mp D.locus_pullback _ hp _ (same_rv_retain_vf_labels ρ he))) (hull_idem _)
  locus_subset := Set.inter_subset_right
  center p := D.center (retainVFLabels ρ p)
  independent p hp q hq he := by
    apply D.independent (retainVFLabels ρ p) ⟨hHA p hp.1,hp.2.1⟩
      (retainVFLabels ρ q) ⟨hHA q hq.1,hq.2.1⟩
    exact congrArg (retainVFLabels ρ) he
  center_mem := by
    intro p hp
    have hlow := D.center_mem (retainVFLabels ρ p) ⟨hHA p hp.1,hp.2.1⟩
    have hr := D.toFocusGeometry.center_sameRV (retainVFLabels ρ p) ⟨hHA p hp.1,hp.2.1⟩
    refine ⟨hlow,p,hp.1,sameRV_replace j p _ hr⟩

def rvLabelFocusActive {A : DefSet (M := M) S n m} {H : DefSet (M := M) S n l}
    {j : Fin n} {k : Fin m} (D : Focus A j k) (ρ : Fin m → Fin l)
    (hHA : ∀ p ∈ carrier H, retainVFLabels ρ p ∈ carrier A) : DefSet (M := M) S n l :=
  PresentedSet.mk (carrier H ∩ (rvLabelFocusGeometry D ρ hHA).locus)
    (SetDefinable.inter _ (setDefinable H) (SetDefinable.inter _
      (retain_vf_labels_preimage_definable ρ D.locus D.locus_definable) (hull_definable H)))

def rvLabelFocusActiveMap {A : DefSet (M := M) S n m} {H : DefSet (M := M) S n l}
    {j : Fin n} {k : Fin m} (D : Focus A j k) (ρ : Fin m → Fin l)
    (hHA : ∀ p ∈ carrier H, retainVFLabels ρ p ∈ carrier A) : Map (rvLabelFocusActive D ρ hHA) D.active :=
  Map.mk (fun p => ⟨retainVFLabels ρ p.val,hHA _ p.property.1,p.property.2.1⟩)
    (Map.graph_definable (retainVFLabelsMap ρ (rvLabelFocusActive D ρ hHA)))

def rvLabelFocusLift {A : DefSet (M := M) S n m} {H : DefSet (M := M) S n l}
    {j : Fin n} {k : Fin m} (D : Focus A j k) (ρ : Fin m → Fin l)
    (hHA : ∀ p ∈ carrier H, retainVFLabels ρ p ∈ carrier A) : Focus H j (ρ k) where
  toFocusGeometry := rvLabelFocusGeometry D ρ hHA
  locus_definable := SetDefinable.inter _
    (retain_vf_labels_preimage_definable ρ D.locus D.locus_definable) (hull_definable H)
  center_graph := by
    have h := Map.graph_definable (Map.comp D.centerMap (rvLabelFocusActiveMap D ρ hHA))
    apply RelationDefinable.congr _ _ h
    intro p z
    constructor
    · rintro ⟨a,rfl,hz⟩
      exact ⟨a.property,(congrFun hz 0).symm⟩
    · rintro ⟨hp,hz⟩
      refine ⟨⟨p,hp⟩,rfl,?_⟩
      funext i
      fin_cases i
      exact hz.symm

theorem rv_label_focus_lift_eta {A : DefSet (M := M) S n m} {H : DefSet (M := M) S n l}
    {j : Fin n} {k : Fin m} (D : Focus A j k) (ρ : Fin m → Fin l)
    (hHA : ∀ p ∈ carrier H, retainVFLabels ρ p ∈ carrier A)
    (p : Point (M := M) n l) (hp : p ∈ carrier H) :
    retainVFLabels ρ ((rvLabelFocusLift D ρ hHA).toFocusGeometry.eta p) =
      D.toFocusGeometry.eta (retainVFLabels ρ p) := by
  have hh := subset_hull (carrier H) hp
  by_cases hc : retainVFLabels ρ p ∈ D.locus <;>
    simp [FocusGeometry.eta,rvLabelFocusLift,rvLabelFocusGeometry,hc,hh,retain_vf_labels_replace] <;> rfl

def rvLabelCanonicalProjection (ρ : Fin m → Fin l) : Fin (n+m) → Fin (n+l) :=
  Fin.addCases (Fin.castAdd l) (fun i => Fin.natAdd n (ρ i))

theorem retain_vf_labels_canonical (ρ : Fin m → Fin l) (p : Point (M := M) n l) :
    retainVFLabels (rvLabelCanonicalProjection (n := n) ρ) (canonical p) = canonical (retainVFLabels ρ p) := by
  refine Prod.ext rfl ?_
  funext i
  cases i using Fin.addCases <;> simp [retainVFLabels,rvLabelCanonicalProjection,canonical]

end IntegrationInACVF.Section7
