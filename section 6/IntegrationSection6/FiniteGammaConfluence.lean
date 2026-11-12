import IntegrationSection6.FiniteGammaOverlap
import IntegrationSection6.FiniteGammaElementaryPartitions
import IntegrationSection6.FiniteGammaElementaryIsos
import IntegrationSection6.FiniteGammaIsoClasses
import IntegrationSection6.FiniteGammaChainTransport

/-! The actual original-Gamma local diamond, exact finite grid and common
blowup equivalence in RV[k]. Only the original B.real is bounded. -/
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
variable {κ : Cardinal} {hκ : Cardinal.aleph0 ≤ κ} {hs : Saturated M κ}

variable {h00 : M ⊨ Axioms.ACVF00} {hsmall : Cardinal.mk B.real < κ}

variable {U V W : GammaObjectAt B S n}

def GammaBlowupAt.sourceIso (H : GammaBlowupAt hκ hs h00 hsmall  U V) (e : GammaIsoAt W U) :
    GammaBlowupAt hκ hs h00 hsmall  W V := {H with source := e.trans H.source}

def GammaBlowupAt.targetIso (H : GammaBlowupAt hκ hs h00 hsmall  U V) (e : GammaIsoAt V W) :
    GammaBlowupAt hκ hs h00 hsmall  U W := {H with result := e.symm.trans H.result}

theorem gammaBlowup_diamond (H : GammaBlowupAt hκ hs h00 hsmall  U V)
    (G : GammaBlowupAt hκ hs h00 hsmall  U W) :
    ∃ V' W', Nonempty (GammaBlowupAt hκ hs h00 hsmall  V V') ∧
      Nonempty (GammaBlowupAt hκ hs h00 hsmall  W W') ∧ Nonempty (GammaIsoAt V' W') := by
  let h := H.toLocus
  let g := G.toLocus
  let F := gammaOverlapRefinementAt h g
  let X := gammaRestrictAt h.center F.left F.left_subset F.left_graph
  let X' := gammaComplementAt h.center F.left F.left_graph
  let Y := gammaRestrictAt g.center F.right F.right_subset F.right_graph
  let Y' := gammaComplementAt g.center F.right F.right_graph
  have hX := gammaAdmissible_restrictAt h.center h.admissible F.left F.left_subset F.left_graph
  have hX' := gammaAdmissible_restrictAt h.center h.admissible
    (@IntegrationInACVF.Section6.complement M N S n h.center.object.obj F.left)
    (@complement_subset M N hN S n h.center.object.obj F.left) ((gammaLogicInput B).sdiff h.center.domain_graph F.left_graph)
  have hY := gammaAdmissible_restrictAt g.center g.admissible F.right F.right_subset F.right_graph
  have hY' := gammaAdmissible_restrictAt g.center g.admissible
    (@IntegrationInACVF.Section6.complement M N S n g.center.object.obj F.right)
    (@complement_subset M N hN S n g.center.object.obj F.right) ((gammaLogicInput B).sdiff g.center.domain_graph F.right_graph)
  let CX := gammaElementaryAt hκ hs h00 hsmall  X h.coordinate hX
  let CX' := gammaElementaryAt hκ hs h00 hsmall  X' h.coordinate hX'
  let CY := gammaElementaryAt hκ hs h00 hsmall  Y g.coordinate hY
  let CY' := gammaElementaryAt hκ hs h00 hsmall  Y' g.coordinate hY'
  let E := F.exterior
  let ev := h.result.trans (gammaCoprodIsoAt
    (gammaElementaryPartitionIsoAt hκ hs h00 hsmall  h.center h.coordinate h.admissible F.left F.left_subset F.left_graph).symm
      F.left_remainder)
  let ew := g.result.trans (gammaCoprodIsoAt
    (gammaElementaryPartitionIsoAt hκ hs h00 hsmall  g.center g.coordinate g.admissible F.right F.right_subset F.right_graph).symm
      F.right_remainder)
  letI : Fact (B.real ⊆ S) := ⟨U.real_contains⟩
  have hvs : Nonempty (GammaIsoAt V (gammaCoprodAt Y' (gammaCoprodAt (gammaCoprodAt CX CX') E))) := by
    apply gammaIsoClassAt_eq_iff.mp
    rw [gammaIsoClassAt_iso ev]
    simp only [gammaIsoClassAt_coprod]
    abel
  have hws : Nonempty (GammaIsoAt W (gammaCoprodAt X' (gammaCoprodAt (gammaCoprodAt CY CY') E))) := by
    apply gammaIsoClassAt_eq_iff.mp
    rw [gammaIsoClassAt_iso ew]
    simp only [gammaIsoClassAt_coprod]
    abel
  obtain ⟨evs⟩ := hvs
  obtain ⟨ews⟩ := hws
  let V' := gammaCoprodAt CY' (gammaCoprodAt (gammaCoprodAt CX CX') E)
  let W' := gammaCoprodAt CX' (gammaCoprodAt (gammaCoprodAt CY CY') E)
  let ec := gammaElementaryIsoAt hκ hs h00 hsmall  h.coordinate g.coordinate hX hY F.overlap
  let hV' : GammaBlowupAt hκ hs h00 hsmall  V V' := {
    center := Y'
    remainder := gammaCoprodAt (gammaCoprodAt CX CX') E
    coordinate := g.coordinate
    admissible := hY'
    source := evs
    result := GammaIsoAt.refl V' }
  let hW' : GammaBlowupAt hκ hs h00 hsmall  W W' := {
    center := X'
    remainder := gammaCoprodAt (gammaCoprodAt CY CY') E
    coordinate := h.coordinate
    admissible := hX'
    source := ews
    result := GammaIsoAt.refl W' }
  refine ⟨V',W',⟨hV'⟩,⟨hW'⟩,?_⟩
  apply gammaIsoClassAt_eq_iff.mp
  change gammaIsoClassAt (gammaCoprodAt CY' (gammaCoprodAt (gammaCoprodAt CX CX') E)) =
    gammaIsoClassAt (gammaCoprodAt CX' (gammaCoprodAt (gammaCoprodAt CY CY') E))
  simp only [gammaIsoClassAt_coprod]
  rw [gammaIsoClassAt_iso ec]
  abel

/-- One actual Gamma-certified blowup, on actual Gamma RV[k] iso classes. -/
def gammaClassBlowupAt (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (h00 : M ⊨ Axioms.ACVF00) (hsmall : Cardinal.mk B.real < κ) (a b : GammaIsoClassesAt B S n) : Prop :=
  ∃ U V : GammaObjectAt B S n, gammaIsoClassAt U = a ∧ gammaIsoClassAt V = b ∧
    Nonempty (GammaBlowupAt hκ hs h00 hsmall  U V)

theorem gammaClassBlowupAt_diamond : Iteration.Diamond (gammaClassBlowupAt (S := S) (n := n) hκ hs h00 hsmall ) := by
  intro a b c hab hac
  obtain ⟨U,V,hU,hV,⟨H⟩⟩ := hab
  obtain ⟨T,W,hT,hW,⟨G⟩⟩ := hac
  obtain ⟨e⟩ := gammaIsoClassAt_eq_iff.mp (hU.trans hT.symm)
  obtain ⟨V',W',hV',hW',⟨f⟩⟩ := gammaBlowup_diamond H (G.sourceIso e)
  exact ⟨gammaIsoClassAt V',⟨V,V',hV,rfl,hV'⟩,⟨W,W',hW,(gammaIsoClassAt_iso f).symm,hW'⟩⟩

theorem GammaIteratedBlowup.classSteps {r : ℕ} {U V : GammaObjectAt B S n}
    (H : GammaIteratedBlowup hκ hs h00 hsmall  r U V) :
    Iteration.Steps (gammaClassBlowupAt hκ hs h00 hsmall ) r (gammaIsoClassAt U) (gammaIsoClassAt V) := by
  induction H with
  | zero he =>
    obtain ⟨e⟩ := he
    rw [gammaIsoClassAt_iso e]
    exact .refl _
  | cons he _ ih => exact .cons ⟨_,_,rfl,rfl,he⟩ ih

theorem gammaIteratedBlowup_of_classSteps {a b : GammaIsoClassesAt B S n} {r : ℕ}
    (H : Iteration.Steps (gammaClassBlowupAt hκ hs h00 hsmall ) r a b)
    {U V : GammaObjectAt B S n} (hU : gammaIsoClassAt U = a) (hV : gammaIsoClassAt V = b) :
    GammaIteratedBlowup hκ hs h00 hsmall  r U V := by
  induction H generalizing U V with
  | refl => exact .zero (gammaIsoClassAt_eq_iff.mp (hU.trans hV.symm))
  | cons h _ ih =>
    obtain ⟨X,Y,hX,hY,⟨hXY⟩⟩ := h
    obtain ⟨e⟩ := gammaIsoClassAt_eq_iff.mp (hU.trans hX.symm)
    exact .cons ⟨hXY.sourceIso e⟩ (ih hY hV)

theorem lemma_6_5_gamma {U V A C : GammaObjectAt B S n} {r s : ℕ}
    (e : GammaIsoAt U V) (H : GammaIteratedBlowup hκ hs h00 hsmall  r U A)
    (G : GammaIteratedBlowup hκ hs h00 hsmall  s V C) :
    ∃ A' C', GammaIteratedBlowup hκ hs h00 hsmall  s A A' ∧
      GammaIteratedBlowup hκ hs h00 hsmall  r C C' ∧ Nonempty (GammaIsoAt A' C') := by
  obtain ⟨c,hac,hbc⟩ := Iteration.grid gammaClassBlowupAt_diamond H.classSteps (G.sourceIso e).classSteps
  obtain ⟨E,hE⟩ := gammaIsoClassAt_surjective c
  exact ⟨E,E,gammaIteratedBlowup_of_classSteps hac rfl hE,
    gammaIteratedBlowup_of_classSteps hbc rfl hE,⟨GammaIsoAt.refl E⟩⟩

theorem GammaIspAt.trans {U V W : GammaObjectAt B S n}
    (H : GammaIspAt hκ hs h00 hsmall  U V) (G : GammaIspAt hκ hs h00 hsmall  V W) :
    GammaIspAt hκ hs h00 hsmall  U W := by
  obtain ⟨r,s,A,C,hU,hV,⟨eAC⟩⟩ := H
  obtain ⟨p,q,D,E,hVD,hWE,⟨eDE⟩⟩ := G
  obtain ⟨C',D',hCC,hDD,he⟩ := lemma_6_5_gamma (GammaIsoAt.refl V) hV hVD
  exact ⟨r+p,q+s,C',D',hU.append (hCC.sourceIso eAC),hWE.append (hDD.sourceIso eDE.symm),he⟩

end IntegrationInACVF.Section6.FiniteRV
