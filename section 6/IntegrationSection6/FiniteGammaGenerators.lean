import IntegrationSection6.FiniteGammaAdditiveCongruence

/-! The original-Gamma finite common-blowup congruence is exactly the least
additive congruence containing genuine elementary replacements. -/
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

def gammaElementaryWholeBlowupAt (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (h00 : M ⊨ Axioms.ACVF00) (hsmall : Cardinal.mk B.real < κ) (U : GammaObjectAt B S n) (i : Fin n) (hAd : GammaAdmissible U.toGamma.toGammaRVObject i) :
    GammaBlowupAt hκ hs h00 hsmall  U (gammaElementaryAt hκ hs h00 hsmall  U i hAd) := by
  let E := gammaEmptyAt (n := n) U.real_contains
  let V := gammaElementaryAt hκ hs h00 hsmall  U i hAd
  letI : Fact (B.real ⊆ S) := ⟨U.real_contains⟩
  have hu : Nonempty (GammaIsoAt U (gammaCoprodAt U E)) := by
    apply gammaIsoClassAt_eq_iff.mp
    simp only [E,gammaIsoClassAt_coprod,gammaIsoClassAt_empty,add_zero]
  have hv : Nonempty (GammaIsoAt V (gammaCoprodAt V E)) := by
    apply gammaIsoClassAt_eq_iff.mp
    simp only [E,gammaIsoClassAt_coprod,gammaIsoClassAt_empty,add_zero]
  exact {
    center := U
    remainder := E
    coordinate := i
    admissible := hAd
    source := Classical.choice hu
    result := Classical.choice hv }

theorem GammaIteratedBlowup.single {U V : GammaObjectAt B S n}
    (H : GammaBlowupAt hκ hs h00 hsmall  U V) : GammaIteratedBlowup hκ hs h00 hsmall  1 U V :=
  .cons ⟨H⟩ (GammaIteratedBlowup.refl V)

theorem GammaIspAt.of_iterated {U V : GammaObjectAt B S n} {r : ℕ}
    (H : GammaIteratedBlowup hκ hs h00 hsmall  r U V) : GammaIspAt hκ hs h00 hsmall  U V :=
  ⟨r,0,V,V,H,GammaIteratedBlowup.refl V,⟨GammaIsoAt.refl V⟩⟩

theorem gammaElementary_ispAt (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (h00 : M ⊨ Axioms.ACVF00) (hsmall : Cardinal.mk B.real < κ) (U : GammaObjectAt B S n) (i : Fin n) (hAd : GammaAdmissible U.toGamma.toGammaRVObject i) :
    GammaIspAt hκ hs h00 hsmall  U (gammaElementaryAt hκ hs h00 hsmall  U i hAd) :=
  GammaIspAt.of_iterated (GammaIteratedBlowup.single (gammaElementaryWholeBlowupAt hκ hs h00 hsmall  U i hAd))

section Least
variable [Fact (B.real ⊆ S)]

variable (c : AddCon (GammaIsoClassesAt B S n))

variable (hgen : ∀ (U : GammaObjectAt B S n) (i : Fin n) (hAd : GammaAdmissible U.toGamma.toGammaRVObject i),
  c (gammaIsoClassAt U) (gammaIsoClassAt (gammaElementaryAt hκ hs h00 hsmall  U i hAd)))

include hgen in
theorem GammaBlowupAt.congruent {U V : GammaObjectAt B S n} (H : GammaBlowupAt hκ hs h00 hsmall  U V) :
    c (gammaIsoClassAt U) (gammaIsoClassAt V) := by
  rw [gammaIsoClassAt_iso H.source,gammaIsoClassAt_coprod,gammaIsoClassAt_iso H.result,gammaIsoClassAt_coprod]
  exact c.add (hgen H.center H.coordinate H.admissible) (c.refl _)

include hgen in
theorem GammaIteratedBlowup.congruent {U V : GammaObjectAt B S n} {r : ℕ}
    (H : GammaIteratedBlowup hκ hs h00 hsmall  r U V) : c (gammaIsoClassAt U) (gammaIsoClassAt V) := by
  induction H with
  | zero he =>
    obtain ⟨e⟩ := he
    rw [gammaIsoClassAt_iso e]
    exact c.refl _
  | cons he _ ih =>
    obtain ⟨e⟩ := he
    exact c.trans (e.congruent c hgen) ih

include hgen in
theorem GammaIspAt.congruent {U V : GammaObjectAt B S n} (H : GammaIspAt hκ hs h00 hsmall  U V) :
    c (gammaIsoClassAt U) (gammaIsoClassAt V) := by
  obtain ⟨r,s,A,C,hU,hV,⟨e⟩⟩ := H
  have hu := hU.congruent c hgen
  have hv := hV.congruent c hgen
  rw [gammaIsoClassAt_iso e] at hu
  exact c.trans hu (c.symm hv)

include hgen in
theorem gammaIspAddConAt_least : gammaIspAddConAt (S := S) (n := n) hκ hs h00 hsmall  ≤ c := by
  rintro a b ⟨U,V,rfl,rfl,H⟩
  exact H.congruent c hgen

end Least
end IntegrationInACVF.Section6.FiniteRV
