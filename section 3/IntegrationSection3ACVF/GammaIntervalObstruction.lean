import IntegrationSection3ACVF.GammaPairedCellDecomposition
import IntegrationSection3ACVF.GammaSubtypeFunctions

/-! Independent closed-to-half-open/closed-ray obstruction on the
actual Gamma quotient. Finite paired point/open-cell decompositions prove
the count, with no Euler or Grothendieck-ring theorem as an input. -/

open Set Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3

namespace IntegrationInACVF.Section3ACVF.GammaIntervalObstruction

open FullGammaSyntax

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

theorem no_bijOn_closed_to_noMin {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (h00 : M ⊨ Axioms.ACVF00) (B : FullBaseAtomicity.Base (M := M)) (hsmall : Cardinal.mk B.real < κ)
    (a b : Values.Gamma (M := M)) (hab : a ≤ b) (J : Set (Values.Gamma (M := M)))
    (hJ : OrdConnected J) (ν : Values.Gamma (M := M)) (hGreatest : IsGreatest J ν)
    (hNoMin : ∀ p ∈ J, ∃ x ∈ J, x < p)
    (f : Values.Gamma (M := M) → Values.Gamma (M := M))
    (hG : Definable B (GammaFunctionSyntax.graph (Set.Icc a b) f))
    (hBij : Set.BijOn f (Set.Icc a b) J) : False := by
  obtain ⟨G,K,L,hPoints⟩ := GammaPairedCellDecomposition.exists_paired hκ hs h00 B hsmall
    a b hab J hJ ν hGreatest f hG hBij
  exact OrderedCellDecomposition.closed_noMin_obstruction a b hab K L hJ hNoMin hPoints

theorem no_bijOn_Ioc {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (h00 : M ⊨ Axioms.ACVF00) (B : FullBaseAtomicity.Base (M := M)) (hsmall : Cardinal.mk B.real < κ)
    (a b σ ν : Values.Gamma (M := M)) (hab : a ≤ b)
    (f : Values.Gamma (M := M) → Values.Gamma (M := M))
    (hG : Definable B (GammaFunctionSyntax.graph (Set.Icc a b) f))
    (hBij : Set.BijOn f (Set.Icc a b) (Set.Ioc σ ν)) : False := by
  have hTarget := hBij.1 (show a ∈ Set.Icc a b from ⟨le_rfl,hab⟩)
  have hσν : σ < ν := hTarget.1.trans_le hTarget.2
  apply no_bijOn_closed_to_noMin hκ hs h00 B hsmall a b hab (Set.Ioc σ ν) Set.ordConnected_Ioc ν
    ⟨⟨hσν,le_rfl⟩,fun x hx => hx.2⟩ _ f hG hBij
  intro p hp
  obtain ⟨x,hσx,hxp⟩ := exists_between hp.1
  exact ⟨x,⟨hσx,hxp.le.trans hp.2⟩,hxp⟩

theorem no_bijOn_Iic {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (h00 : M ⊨ Axioms.ACVF00) (B : FullBaseAtomicity.Base (M := M)) (hsmall : Cardinal.mk B.real < κ)
    (a b ν : Values.Gamma (M := M)) (hab : a ≤ b)
    (f : Values.Gamma (M := M) → Values.Gamma (M := M))
    (hG : Definable B (GammaFunctionSyntax.graph (Set.Icc a b) f))
    (hBij : Set.BijOn f (Set.Icc a b) (Set.Iic ν)) : False := by
  apply no_bijOn_closed_to_noMin hκ hs h00 B hsmall a b hab (Set.Iic ν) Set.ordConnected_Iic ν
    ⟨(by change ν ≤ ν; exact le_rfl),fun x hx => hx⟩ _ f hG hBij
  intro p hp
  obtain ⟨x,hxp⟩ := exists_lt p
  exact ⟨x,hxp.le.trans hp,hxp⟩

theorem no_subtype_bijection {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (h00 : M ⊨ Axioms.ACVF00) (B : FullBaseAtomicity.Base (M := M)) (hsmall : Cardinal.mk B.real < κ)
    (a b ν : Values.Gamma (M := M)) (hab : a ≤ b)
    (J : Set (Values.Gamma (M := M))) (hJ : J = Set.Iic ν ∨ ∃ σ, J = Set.Ioc σ ν)
    (q : Set.Icc a b → J) (hBij : Function.Bijective q)
    (hG : Definable B (DefinableGammaMatching.graph (Set.Icc a b) J q)) : False := by
  obtain ⟨f,hf,hBijF⟩ := GammaSubtypeFunctions.exists_partial B (Set.Icc a b) J q hBij hG
  rcases hJ with rfl | ⟨σ,rfl⟩
  · exact no_bijOn_Iic hκ hs h00 B hsmall a b ν hab f hf hBijF
  · exact no_bijOn_Ioc hκ hs h00 B hsmall a b σ ν hab f hf hBijF

end IntegrationInACVF.Section3ACVF.GammaIntervalObstruction
