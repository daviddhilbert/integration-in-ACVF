import IntegrationSection6.FiniteGammaConfluence
import IntegrationSection6.FiniteGammaParameterExtension

/-! Definition6.7/6.8 as an actual equivalence relation on finite RV objects
over the original Gamma base, including arbitrary internal presentations. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5 SpecialTransformations.Section7
namespace IntegrationInACVF.Section6.FiniteRV
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

variable {B : Base (M := M)} {S : Set M} {n : ℕ}

variable {κ : Cardinal} {hκ : Cardinal.aleph0 ≤ κ} {hs : Saturated M κ}

variable {h00 : M ⊨ Axioms.ACVF00} {hsmall : Cardinal.mk B.real < κ}

theorem GammaIsp.trans {U V W : GammaRVFiniteObject B n}
    (H : GammaIsp hκ hs h00 hsmall  U V) (G : GammaIsp hκ hs h00 hsmall  V W) :
    GammaIsp hκ hs h00 hsmall  U W := by
  obtain ⟨R,hUR,hVR,H⟩ := H
  obtain ⟨T,hVT,hWT,G⟩ := G
  have hRQ : R ⊆ R ∪ T := Set.subset_union_left
  have hTQ : T ⊆ R ∪ T := Set.subset_union_right
  exact ⟨R ∪ T,fun x hx => hRQ (hUR hx),fun x hx => hTQ (hWT hx),(H.extend hRQ).trans (G.extend hTQ)⟩

def gammaIspAtSetoid (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (h00 : M ⊨ Axioms.ACVF00) (hsmall : Cardinal.mk B.real < κ) :
    Setoid (GammaObjectAt B S n) where
  r := GammaIspAt hκ hs h00 hsmall 
  iseqv := ⟨GammaIspAt.refl,GammaIspAt.symm,GammaIspAt.trans⟩

def gammaIspSetoid (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (h00 : M ⊨ Axioms.ACVF00) (hsmall : Cardinal.mk B.real < κ) :
    Setoid (GammaRVFiniteObject B n) where
  r := GammaIsp hκ hs h00 hsmall 
  iseqv := ⟨GammaIsp.refl,GammaIsp.symm,GammaIsp.trans⟩

end IntegrationInACVF.Section6.FiniteRV
