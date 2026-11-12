import IntegrationSection6.FiniteGammaChainTransport

/-! The common finite-blowup relation over the original Gamma base.
A real presentation may be enlarged internally, while all object and
chart graphs remain over the unchanged named base B. -/
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

theorem GammaIspAt.refl (U : GammaObjectAt B S n) : GammaIspAt hκ hs h00 hsmall  U U :=
  ⟨0,0,U,U,GammaIteratedBlowup.refl U,GammaIteratedBlowup.refl U,⟨GammaIsoAt.refl U⟩⟩

theorem GammaIspAt.symm {U V : GammaObjectAt B S n} (H : GammaIspAt hκ hs h00 hsmall  U V) :
    GammaIspAt hκ hs h00 hsmall  V U := by
  obtain ⟨r,s,A,C,hU,hV,he⟩ := H
  exact ⟨s,r,C,A,hV,hU,he.map GammaIsoAt.symm⟩

theorem GammaIspAt.sourceIso {U V W : GammaObjectAt B S n}
    (H : GammaIspAt hκ hs h00 hsmall  U V) (e : GammaIsoAt W U) :
    GammaIspAt hκ hs h00 hsmall  W V := by
  obtain ⟨r,s,A,C,hU,hV,he⟩ := H
  exact ⟨r,s,A,C,hU.sourceIso e,hV,he⟩

/-- Definition6.7 for RV[k] with full original-Gamma certificates.
The existential real code set is internal and is never required small. -/
def GammaIsp (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (h00 : M ⊨ Axioms.ACVF00) (hsmall : Cardinal.mk B.real < κ) (U V : GammaRVFiniteObject B n) : Prop :=
  ∃ R : Set M, ∃ hUR : U.codes ⊆ R, ∃ hVR : V.codes ⊆ R,
    GammaIspAt hκ hs h00 hsmall  (gammaObjectAtExtend U hUR) (gammaObjectAtExtend V hVR)

theorem GammaIsp.refl (U : GammaRVFiniteObject B n) : GammaIsp hκ hs h00 hsmall  U U :=
  ⟨U.codes,Set.Subset.refl _,Set.Subset.refl _,GammaIspAt.refl _⟩

theorem GammaIsp.symm {U V : GammaRVFiniteObject B n} (H : GammaIsp hκ hs h00 hsmall  U V) :
    GammaIsp hκ hs h00 hsmall  V U := by
  obtain ⟨R,hUR,hVR,H⟩ := H
  exact ⟨R,hVR,hUR,H.symm⟩

theorem GammaIsp.liftIso (hcan : CanonicalStructure.IsCanonical (M := M)) (hB : VFGammaGeneratedBase B)
    {U V : GammaRVFiniteObject B n} (H : GammaIsp hκ hs h00 hsmall  U V) :
    Nonempty (GammaIso B U.lift V.lift) := by
  obtain ⟨R,hUR,hVR,H⟩ := H
  exact H.liftIso hcan hB

end IntegrationInACVF.Section6.FiniteRV
