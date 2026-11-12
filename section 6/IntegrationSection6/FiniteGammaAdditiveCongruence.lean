import IntegrationSection6.FiniteGammaEquivalence
import Mathlib.GroupTheory.Congruence.Basic

/-! Lemma6.8: additive compatibility of actual Gamma-certified common
finite blowups, on actual RV[k] isomorphism classes at a presentation. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5 SpecialTransformations.Section7
namespace IntegrationInACVF.Section6.FiniteRV
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

variable {B : Base (M := M)} {S : Set M} {n : ℕ}

variable {κ : Cardinal} {hκ : Cardinal.aleph0 ≤ κ} {hs : Saturated M κ}

variable {h00 : M ⊨ Axioms.ACVF00} {hsmall : Cardinal.mk B.real < κ}

theorem GammaIspAt.corollary_6_6 {U V A C : GammaObjectAt B S n}
    (H : GammaIspAt hκ hs h00 hsmall  U V) (e : GammaIsoAt A U) (f : GammaIsoAt C V) :
    GammaIspAt hκ hs h00 hsmall  A C := (H.sourceIso e).symm.sourceIso f |>.symm

def GammaBlowupAt.coprodRight {U V : GammaObjectAt B S n}
    (H : GammaBlowupAt hκ hs h00 hsmall  U V) (Q : GammaObjectAt B S n) :
    GammaBlowupAt hκ hs h00 hsmall  (gammaCoprodAt U Q) (gammaCoprodAt V Q) := by
  letI : Fact (B.real ⊆ S) := ⟨U.real_contains⟩
  have hes : Nonempty (GammaIsoAt (gammaCoprodAt U Q) (gammaCoprodAt H.center (gammaCoprodAt H.remainder Q))) := by
    apply gammaIsoClassAt_eq_iff.mp
    rw [gammaIsoClassAt_coprod,gammaIsoClassAt_iso H.source]
    simp only [gammaIsoClassAt_coprod]
    abel
  have het : Nonempty (GammaIsoAt (gammaCoprodAt V Q)
      (gammaCoprodAt (gammaElementaryAt hκ hs h00 hsmall  H.center H.coordinate H.admissible) (gammaCoprodAt H.remainder Q))) := by
    apply gammaIsoClassAt_eq_iff.mp
    rw [gammaIsoClassAt_coprod,gammaIsoClassAt_iso H.result]
    simp only [gammaIsoClassAt_coprod]
    abel
  exact {
    center := H.center
    remainder := gammaCoprodAt H.remainder Q
    coordinate := H.coordinate
    admissible := H.admissible
    source := Classical.choice hes
    result := Classical.choice het }

theorem GammaIteratedBlowup.coprodRight {U V : GammaObjectAt B S n} {r : ℕ}
    (H : GammaIteratedBlowup hκ hs h00 hsmall  r U V) (Q : GammaObjectAt B S n) :
    GammaIteratedBlowup hκ hs h00 hsmall  r (gammaCoprodAt U Q) (gammaCoprodAt V Q) := by
  induction H with
  | zero he => exact .zero (he.map fun e => gammaCoprodIsoAt e (GammaIsoAt.refl Q))
  | cons he _ ih => exact .cons (he.map fun e => e.coprodRight Q) ih

theorem GammaIspAt.coprodRight {U V : GammaObjectAt B S n}
    (H : GammaIspAt hκ hs h00 hsmall  U V) (Q : GammaObjectAt B S n) :
    GammaIspAt hκ hs h00 hsmall  (gammaCoprodAt U Q) (gammaCoprodAt V Q) := by
  obtain ⟨r,s,A,C,hU,hV,he⟩ := H
  exact ⟨r,s,gammaCoprodAt A Q,gammaCoprodAt C Q,hU.coprodRight Q,hV.coprodRight Q,
    he.map fun e => gammaCoprodIsoAt e (GammaIsoAt.refl Q)⟩

theorem GammaIspAt.coprodLeft {U V : GammaObjectAt B S n}
    (H : GammaIspAt hκ hs h00 hsmall  U V) (Q : GammaObjectAt B S n) :
    GammaIspAt hκ hs h00 hsmall  (gammaCoprodAt Q U) (gammaCoprodAt Q V) := by
  letI : Fact (B.real ⊆ S) := ⟨U.real_contains⟩
  have he : Nonempty (GammaIsoAt (gammaCoprodAt Q U) (gammaCoprodAt U Q)) := by
    apply gammaIsoClassAt_eq_iff.mp
    simp only [gammaIsoClassAt_coprod]
    exact add_comm _ _
  have hf : Nonempty (GammaIsoAt (gammaCoprodAt Q V) (gammaCoprodAt V Q)) := by
    apply gammaIsoClassAt_eq_iff.mp
    simp only [gammaIsoClassAt_coprod]
    exact add_comm _ _
  exact (H.coprodRight Q).corollary_6_6 (Classical.choice he) (Classical.choice hf)

theorem GammaIspAt.coprod {U V A C : GammaObjectAt B S n}
    (H : GammaIspAt hκ hs h00 hsmall  U V) (G : GammaIspAt hκ hs h00 hsmall  A C) :
    GammaIspAt hκ hs h00 hsmall  (gammaCoprodAt U A) (gammaCoprodAt V C) :=
  (H.coprodRight A).trans (G.coprodLeft V)

def gammaClassIspAt (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (h00 : M ⊨ Axioms.ACVF00) (hsmall : Cardinal.mk B.real < κ) (a b : GammaIsoClassesAt B S n) : Prop :=
  ∃ U V : GammaObjectAt B S n, gammaIsoClassAt U = a ∧ gammaIsoClassAt V = b ∧ GammaIspAt hκ hs h00 hsmall  U V

theorem gammaClassIspAt_class_iff (U V : GammaObjectAt B S n) :
    gammaClassIspAt hκ hs h00 hsmall  (gammaIsoClassAt U) (gammaIsoClassAt V) ↔ GammaIspAt hκ hs h00 hsmall  U V := by
  constructor
  · rintro ⟨A,C,hA,hC,H⟩
    obtain ⟨e⟩ := gammaIsoClassAt_eq_iff.mp hA
    obtain ⟨f⟩ := gammaIsoClassAt_eq_iff.mp hC
    exact H.corollary_6_6 e.symm f.symm
  · intro H
    exact ⟨U,V,rfl,rfl,H⟩

def gammaIspAddConAt [Fact (B.real ⊆ S)] (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (h00 : M ⊨ Axioms.ACVF00) (hsmall : Cardinal.mk B.real < κ) :
    AddCon (GammaIsoClassesAt B S n) where
  r := gammaClassIspAt hκ hs h00 hsmall 
  iseqv := by
    constructor
    · intro a
      obtain ⟨U,rfl⟩ := gammaIsoClassAt_surjective a
      exact ⟨U,U,rfl,rfl,GammaIspAt.refl U⟩
    · rintro a b ⟨U,V,hU,hV,H⟩
      exact ⟨V,U,hV,hU,H.symm⟩
    · intro a b c hab hbc
      obtain ⟨U,rfl⟩ := gammaIsoClassAt_surjective a
      obtain ⟨V,rfl⟩ := gammaIsoClassAt_surjective b
      obtain ⟨W,rfl⟩ := gammaIsoClassAt_surjective c
      exact (gammaClassIspAt_class_iff U W).mpr
        (((gammaClassIspAt_class_iff U V).mp hab).trans ((gammaClassIspAt_class_iff V W).mp hbc))
  add' := by
    rintro a b c d ⟨U,V,rfl,rfl,H⟩ ⟨A,C,rfl,rfl,G⟩
    exact ⟨gammaCoprodAt U A,gammaCoprodAt V C,gammaIsoClassAt_coprod U A,gammaIsoClassAt_coprod V C,H.coprod G⟩

end IntegrationInACVF.Section6.FiniteRV
