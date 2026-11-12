import IntegrationSection6.GammaThroughIspTransitions
import IntegrationSection6.GammaNonzeroQuotientLift
import IntegrationSection6.GammaNonzeroThroughTransitions
import IntegrationSection6.GammaIspPadding

/-! The nonzero-coordinate filtered form of fixed-degree integration. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5 SpecialTransformations.Section7
open SpecialTransformations.Section4.PositiveAdditiveGrothendieck
namespace IntegrationInACVF.Section6.FiniteRV
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {k : ℕ} {S : Set M}
local instance : Fact (B.real ⊆ (Set.univ : Set M)) := ⟨Set.subset_univ _⟩
variable {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
variable (h00 : M ⊨ Axioms.ACVF00) (hreal : Cardinal.mk B.real < κ) (FBase : VFFieldBase B.real)
variable (hgamma : Cardinal.mk B.gamma < κ) (δ : Values.Gamma (M := M)) (hδ : δ ∈ B.gamma) (hδ1 : 1 < δ)
variable (h58 : Section5TwoOrderInputAll hκ hs)

variable (hB : VFGammaGeneratedBase B)

theorem gammaThrough_common_stage_eq {i j l : ℕ} (hil : i ≤ l) (hjl : j ≤ l)
    (a : GammaNonzeroThroughAt (B := B) (S := Set.univ) i) (b : GammaNonzeroThroughAt (B := B) (S := Set.univ) j)
    (he : gammaThroughToGradedAt i a = gammaThroughToGradedAt j b) :
    gammaThroughTransitionAt hil a = gammaThroughTransitionAt hjl b := by
  apply gammaThroughToGradedAt_injective l
  rw [gammaThroughTransitionAt_embed,gammaThroughTransitionAt_embed]
  exact he

def gammaNonzeroIspUnionAddCon : AddCon (GammaNonzeroGradedAt (B := B) (S := Set.univ)) where
  r := gammaNonzeroIspRelation hκ hs h00 hreal
  iseqv := ⟨by
    intro a
    obtain ⟨i,x,hx⟩ := gammaThroughToGradedAt_exhaustive a
    exact ⟨i,x,x,hx,hx,(gammaNonzeroThroughIspAt hκ hs h00 hreal i).refl x⟩,
    by
      rintro a b ⟨i,x,y,hx,hy,H⟩
      exact ⟨i,y,x,hy,hx,(gammaNonzeroThroughIspAt hκ hs h00 hreal i).symm H⟩,
    by
      rintro a b c ⟨i,x,y,hx,hy,H⟩ ⟨j,w,z,hw,hz,G⟩
      let l := max i j
      have hil : i ≤ l := le_max_left _ _
      have hjl : j ≤ l := le_max_right _ _
      have H' := (gammaThroughIsp_transition_iff hκ hs h00 hreal FBase hgamma δ hδ hδ1 h58 hB hil x y).mpr H
      have G' := (gammaThroughIsp_transition_iff hκ hs h00 hreal FBase hgamma δ hδ hδ1 h58 hB hjl w z).mpr G
      have he := gammaThrough_common_stage_eq hil hjl y w (hy.trans hw.symm)
      rw [← he] at G'
      exact ⟨l,gammaThroughTransitionAt hil x,gammaThroughTransitionAt hjl z,
        (gammaThroughTransitionAt_embed hil x).trans hx,(gammaThroughTransitionAt_embed hjl z).trans hz,
        (gammaNonzeroThroughIspAt hκ hs h00 hreal l).trans H' G'⟩⟩
  add' := by
    rintro a b c d ⟨i,x,y,hx,hy,H⟩ ⟨j,w,z,hw,hz,G⟩
    let l := max i j
    have hil : i ≤ l := le_max_left _ _
    have hjl : j ≤ l := le_max_right _ _
    have H' := (gammaThroughIsp_transition_iff hκ hs h00 hreal FBase hgamma δ hδ hδ1 h58 hB hil x y).mpr H
    have G' := (gammaThroughIsp_transition_iff hκ hs h00 hreal FBase hgamma δ hδ hδ1 h58 hB hjl w z).mpr G
    refine ⟨l,gammaThroughTransitionAt hil x + gammaThroughTransitionAt hjl w,
      gammaThroughTransitionAt hil y + gammaThroughTransitionAt hjl z,?_,?_,
      (gammaNonzeroThroughIspAt hκ hs h00 hreal l).add H' G'⟩
    · rw [map_add,gammaThroughTransitionAt_embed,gammaThroughTransitionAt_embed,hx,hw]
    · rw [map_add,gammaThroughTransitionAt_embed,gammaThroughTransitionAt_embed,hy,hz]

theorem gammaNonzeroIspUnionAddCon_stage_iff (i : ℕ)
    (x y : GammaNonzeroThroughAt (B := B) (S := Set.univ) i) :
    gammaNonzeroIspUnionAddCon hκ hs h00 hreal FBase hgamma δ hδ hδ1 h58 hB
      (gammaThroughToGradedAt i x) (gammaThroughToGradedAt i y) ↔ gammaNonzeroThroughIspAt hκ hs h00 hreal i x y := by
  constructor
  · rintro ⟨j,w,z,hw,hz,H⟩
    let l := max i j
    have hil : i ≤ l := le_max_left _ _
    have hjl : j ≤ l := le_max_right _ _
    have H' := (gammaThroughIsp_transition_iff hκ hs h00 hreal FBase hgamma δ hδ hδ1 h58 hB hjl w z).mpr H
    have hew := gammaThrough_common_stage_eq hil hjl x w hw.symm
    have hez := gammaThrough_common_stage_eq hil hjl y z hz.symm
    rw [← hew,← hez] at H'
    exact (gammaThroughIsp_transition_iff hκ hs h00 hreal FBase hgamma δ hδ hδ1 h58 hB hil x y).mp H'
  · intro H
    exact ⟨i,x,y,rfl,rfl,H⟩

end IntegrationInACVF.Section6.FiniteRV
