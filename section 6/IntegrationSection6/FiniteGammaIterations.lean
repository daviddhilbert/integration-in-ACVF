import IntegrationSection6.FiniteGammaBlowups
import IntegrationSection6.FiniteGammaChartLaws

/-! Finite forward blowups with original-Gamma charts at every stage.
Forgetting certificates gives the actual RV[k] relation, with every
intermediate finite-volume object retained. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5 SpecialTransformations.Section7
namespace IntegrationInACVF.Section6.FiniteRV
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

variable {B : Base (M := M)} {S : Set M} {n : ℕ}
local notation "N" => (@CanonicalStructure.normalize M sM)
local notation "hN" => (@CanonicalStructure.normalized_model M sM hM)

inductive GammaIteratedBlowup {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00) (hsmall : Cardinal.mk B.real < κ)
    : ℕ → GammaObjectAt B S n → GammaObjectAt B S n → Prop
  | zero {U V} : Nonempty (GammaIsoAt U V) → GammaIteratedBlowup hκ hs h00 hsmall  0 U V
  | cons {r U V W} : Nonempty (GammaBlowupAt hκ hs h00 hsmall  U V) →
      GammaIteratedBlowup hκ hs h00 hsmall  r V W →
      GammaIteratedBlowup hκ hs h00 hsmall  (r+1) U W

variable {κ : Cardinal} {hκ : Cardinal.aleph0 ≤ κ} {hs : Saturated M κ}

variable {h00 : M ⊨ Axioms.ACVF00} {hsmall : Cardinal.mk B.real < κ}

namespace GammaIteratedBlowup

theorem toFinite {r : ℕ} {U V : GammaObjectAt B S n}
    (H : GammaIteratedBlowup hκ hs h00 hsmall  r U V) :
    @IteratedBlowup M N hN S n r U.object V.object := by
  induction H with
  | zero he => exact @IteratedBlowup.zero M N hN S n _ _ (he.map GammaIsoAt.iso)
  | cons he _ ih => obtain ⟨e⟩ := he; exact @IteratedBlowup.cons M N hN S n _ _ _ _ e.toBlowup ih

theorem refl (U : GammaObjectAt B S n) : GammaIteratedBlowup hκ hs h00 hsmall  0 U U :=
  .zero ⟨GammaIsoAt.refl U⟩

theorem append {r s : ℕ} {U V W : GammaObjectAt B S n}
    (H : GammaIteratedBlowup hκ hs h00 hsmall  r U V)
    (K : GammaIteratedBlowup hκ hs h00 hsmall  s V W) :
    GammaIteratedBlowup hκ hs h00 hsmall  (r+s) U W := by
  induction H with
  | zero he =>
    obtain ⟨e⟩ := he
    cases K with
    | zero hf => exact .zero (hf.map fun f => e.trans f)
    | cons hf htail =>
      obtain ⟨f⟩ := hf
      simpa only [Nat.zero_add] using GammaIteratedBlowup.cons ⟨{f with source := e.trans f.source}⟩ htail
  | cons he _ ih =>
    simpa only [Nat.add_right_comm] using GammaIteratedBlowup.cons he (ih K)

theorem liftIso (hcan : CanonicalStructure.IsCanonical (M := M)) (hB : VFGammaGeneratedBase B)
    {r : ℕ} {U V : GammaObjectAt B S n}
    (H : GammaIteratedBlowup hκ hs h00 hsmall  r U V) :
    Nonempty (GammaIso B U.toGamma.lift V.toGamma.lift) := by
  induction H with
  | zero he =>
    obtain ⟨e⟩ := he
    exact SpecialTransformations.Section7.GammaRVIso.liftIso hcan hκ hs h00 hsmall hB e.toGamma
  | cons he _ ih =>
    obtain ⟨e⟩ := he
    obtain ⟨f⟩ := e.liftIso hcan hB
    obtain ⟨g⟩ := ih
    exact ⟨f.trans (gammaLogicInput B) g⟩

end GammaIteratedBlowup

/-- Definition6.7 at a fixed real code presentation, over the original Gamma base. -/
def GammaIspAt (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (h00 : M ⊨ Axioms.ACVF00) (hsmall : Cardinal.mk B.real < κ) (U V : GammaObjectAt B S n) : Prop :=
  ∃ r s A C, GammaIteratedBlowup hκ hs h00 hsmall  r U A ∧
    GammaIteratedBlowup hκ hs h00 hsmall  s V C ∧ Nonempty (GammaIsoAt A C)

theorem GammaIspAt.toFinite {U V : GammaObjectAt B S n}
    (H : GammaIspAt hκ hs h00 hsmall  U V) : @Isp M N hN S n U.object V.object := by
  obtain ⟨r,s,A,C,hU,hV,he⟩ := H
  exact ⟨r,s,A.object,C.object,hU.toFinite,hV.toFinite,he.map GammaIsoAt.iso⟩

/-- The lift-invariance direction of6.17, for actual finite blowup witnesses.
The general-chart lifting theorem's canonical-totalization assumption is explicit. -/
theorem GammaIspAt.liftIso (hcan : CanonicalStructure.IsCanonical (M := M)) (hB : VFGammaGeneratedBase B)
    {U V : GammaObjectAt B S n} (H : GammaIspAt hκ hs h00 hsmall  U V) :
    Nonempty (GammaIso B U.toGamma.lift V.toGamma.lift) := by
  obtain ⟨r,s,A,C,hU,hV,⟨e⟩⟩ := H
  obtain ⟨f⟩ := hU.liftIso hcan hB
  obtain ⟨g⟩ := hV.liftIso hcan hB
  obtain ⟨h⟩ := SpecialTransformations.Section7.GammaRVIso.liftIso hcan hκ hs h00 hsmall hB e.toGamma
  exact ⟨(f.trans (gammaLogicInput B) h).trans (gammaLogicInput B) (g.symm (gammaLogicInput B))⟩

end IntegrationInACVF.Section6.FiniteRV
