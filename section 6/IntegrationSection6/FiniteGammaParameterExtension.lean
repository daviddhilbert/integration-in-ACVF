import IntegrationSection6.FiniteGammaCommonBlowups
import IntegrationSection6.ParameterExtension

/-! Enlarging internal real presentations preserves every original-Gamma
object and chart graph, and the exact finite number of blowups. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5 SpecialTransformations.Section7
namespace IntegrationInACVF.Section6.FiniteRV
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

variable {B : Base (M := M)} {S R : Set M} {n : ℕ}
local notation "N" => (@CanonicalStructure.normalize M sM)
local notation "hN" => (@CanonicalStructure.normalized_model M sM hM)

def GammaObjectAt.extend (hSR : S ⊆ R) (U : GammaObjectAt B S n) : GammaObjectAt B R n where
  object := @extendObject M N S R n hSR U.object
  real_contains := fun x hx => hSR (U.real_contains hx)
  domain_graph := U.domain_graph
  volume_graph := U.volume_graph

def GammaIsoAt.extend (hSR : S ⊆ R) {U V : GammaObjectAt B S n} (e : GammaIsoAt U V) :
    GammaIsoAt (U.extend hSR) (V.extend hSR) where
  iso := @rvFiniteIsoOfAmbient M N R n (U.extend hSR).object (V.extend hSR).object
    (@IntegrationInACVF.Section6.extendIso M N hN S R n hSR U.object.obj V.object.obj (isoAtAmbient e.iso))
  graph := e.graph

variable {κ : Cardinal} {hκ : Cardinal.aleph0 ≤ κ} {hs : Saturated M κ}

variable {h00 : M ⊨ Axioms.ACVF00} {hsmall : Cardinal.mk B.real < κ}

def GammaBlowupAt.extend (hSR : S ⊆ R) {U V : GammaObjectAt B S n}
    (H : GammaBlowupAt hκ hs h00 hsmall  U V) :
    GammaBlowupAt hκ hs h00 hsmall  (U.extend hSR) (V.extend hSR) where
  center := H.center.extend hSR
  remainder := H.remainder.extend hSR
  coordinate := H.coordinate
  admissible := ⟨H.admissible.nonzero,H.admissible.algebraic⟩
  source := H.source.extend hSR
  result := H.result.extend hSR

theorem GammaIteratedBlowup.extend (hSR : S ⊆ R) {U V : GammaObjectAt B S n} {r : ℕ}
    (H : GammaIteratedBlowup hκ hs h00 hsmall  r U V) :
    GammaIteratedBlowup hκ hs h00 hsmall  r (U.extend hSR) (V.extend hSR) := by
  induction H with
  | zero he => exact .zero (he.map (GammaIsoAt.extend hSR))
  | cons he _ ih => exact .cons (he.map (GammaBlowupAt.extend hSR)) ih

theorem GammaIspAt.extend (hSR : S ⊆ R) {U V : GammaObjectAt B S n}
    (H : GammaIspAt hκ hs h00 hsmall  U V) : GammaIspAt hκ hs h00 hsmall  (U.extend hSR) (V.extend hSR) := by
  obtain ⟨r,s,A,C,hU,hV,he⟩ := H
  exact ⟨r,s,A.extend hSR,C.extend hSR,hU.extend hSR,hV.extend hSR,he.map (GammaIsoAt.extend hSR)⟩

end IntegrationInACVF.Section6.FiniteRV
