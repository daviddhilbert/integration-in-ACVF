import IntegrationSection6.FiniteGammaElementaryRightProducts
import IntegrationSection6.FiniteGammaProductRightDistribution
import IntegrationSection6.FiniteGammaProductIsos
import IntegrationSection6.FiniteGammaProductBlowups

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

def GammaBlowupAt.productLeft {U V : GammaObjectAt B S k}
    (H : GammaBlowupAt hκ hs h00 hsmall U V) (R : GammaObjectAt B S l) :
    GammaBlowupAt hκ hs h00 hsmall (gammaProductAt R U) (gammaProductAt R V) where
  center := gammaProductAt R H.center
  remainder := gammaProductAt R H.remainder
  coordinate := Fin.natAdd l H.coordinate
  admissible := gammaAdmissible_product_left H.admissible R
  source := (gammaProductIsoAt (GammaIsoAt.refl R) H.source).trans
    (gammaProductRightDistribIsoAt H.center H.remainder R)
  result := ((gammaProductIsoAt (GammaIsoAt.refl R) H.result).trans
    (gammaProductRightDistribIsoAt (gammaElementaryAt hκ hs h00 hsmall H.center H.coordinate H.admissible) H.remainder R)).trans
    (gammaCoprodIsoAt (gammaElementaryRightProductIsoAt hκ hs h00 hsmall R H.center H.coordinate H.admissible).symm
      (GammaIsoAt.refl (gammaProductAt R H.remainder)))

theorem GammaIteratedBlowup.productLeft {U V : GammaObjectAt B S k} {r : ℕ}
    (H : GammaIteratedBlowup hκ hs h00 hsmall r U V) (R : GammaObjectAt B S l) :
    GammaIteratedBlowup hκ hs h00 hsmall r (gammaProductAt R U) (gammaProductAt R V) := by
  induction H with
  | zero he => exact .zero (he.map fun e => gammaProductIsoAt (GammaIsoAt.refl R) e)
  | cons he _ ih => exact .cons (he.map fun e => e.productLeft R) ih

theorem GammaIspAt.productLeft {U V : GammaObjectAt B S k}
    (H : GammaIspAt hκ hs h00 hsmall U V) (R : GammaObjectAt B S l) :
    GammaIspAt hκ hs h00 hsmall (gammaProductAt R U) (gammaProductAt R V) := by
  obtain ⟨r,s,A,C,hU,hV,he⟩ := H
  exact ⟨r,s,gammaProductAt R A,gammaProductAt R C,hU.productLeft R,hV.productLeft R,
    he.map fun e => gammaProductIsoAt (GammaIsoAt.refl R) e⟩

theorem GammaIspAt.product {U V : GammaObjectAt B S k} {R T : GammaObjectAt B S l}
    (H : GammaIspAt hκ hs h00 hsmall U V) (G : GammaIspAt hκ hs h00 hsmall R T) :
    GammaIspAt hκ hs h00 hsmall (gammaProductAt U R) (gammaProductAt V T) :=
  (H.productRight R).trans (G.productLeft V)

end IntegrationInACVF.Section6.FiniteRV
