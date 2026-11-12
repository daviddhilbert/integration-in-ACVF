import IntegrationSection6.FiniteGammaElementaryProducts
import IntegrationSection6.FiniteGammaProductDistribution
import IntegrationSection6.FiniteGammaProductIsos
import IntegrationSection6.FiniteGammaAdditiveCongruence

/-! An actual Gamma-certified finite blowup remains such a blowup after
multiplication by an unrelated finite RV object. No small internal code
set or field-generation assumption is used. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
namespace IntegrationInACVF.Section6.FiniteRV
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {S : Set M} {k l : ℕ}
variable {κ : Cardinal} {hκ : Cardinal.aleph0 ≤ κ} {hs : Saturated M κ}
variable {h00 : M ⊨ Axioms.ACVF00} {hsmall : Cardinal.mk B.real < κ}

def GammaBlowupAt.productRight {U V : GammaObjectAt B S k}
    (H : GammaBlowupAt hκ hs h00 hsmall U V) (R : GammaObjectAt B S l) :
    GammaBlowupAt hκ hs h00 hsmall (gammaProductAt U R) (gammaProductAt V R) where
  center := gammaProductAt H.center R
  remainder := gammaProductAt H.remainder R
  coordinate := Fin.castAdd l H.coordinate
  admissible := gammaAdmissible_product H.admissible R
  source := (gammaProductIsoAt H.source (GammaIsoAt.refl R)).trans
    (gammaProductLeftDistribIsoAt H.center H.remainder R)
  result := ((gammaProductIsoAt H.result (GammaIsoAt.refl R)).trans
    (gammaProductLeftDistribIsoAt (gammaElementaryAt hκ hs h00 hsmall H.center H.coordinate H.admissible) H.remainder R)).trans
    (gammaCoprodIsoAt (gammaElementaryProductIsoAt hκ hs h00 hsmall H.center R H.coordinate H.admissible).symm
      (GammaIsoAt.refl (gammaProductAt H.remainder R)))

theorem GammaIteratedBlowup.productRight {U V : GammaObjectAt B S k} {r : ℕ}
    (H : GammaIteratedBlowup hκ hs h00 hsmall r U V) (R : GammaObjectAt B S l) :
    GammaIteratedBlowup hκ hs h00 hsmall r (gammaProductAt U R) (gammaProductAt V R) := by
  induction H with
  | zero he => exact .zero (he.map fun e => gammaProductIsoAt e (GammaIsoAt.refl R))
  | cons he _ ih => exact .cons (he.map fun e => e.productRight R) ih

theorem GammaIspAt.productRight {U V : GammaObjectAt B S k}
    (H : GammaIspAt hκ hs h00 hsmall U V) (R : GammaObjectAt B S l) :
    GammaIspAt hκ hs h00 hsmall (gammaProductAt U R) (gammaProductAt V R) := by
  obtain ⟨r,s,A,C,hU,hV,he⟩ := H
  exact ⟨r,s,gammaProductAt A R,gammaProductAt C R,hU.productRight R,hV.productRight R,
    he.map fun e => gammaProductIsoAt e (GammaIsoAt.refl R)⟩

end IntegrationInACVF.Section6.FiniteRV
