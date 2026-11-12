import IntegrationSection6.GammaIspPadding

/-! Injective transition maps on the actual integration quotients. -/
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

def integrationTargetPadding : IntegrationTarget hκ hs h00 hreal k →+
    IntegrationTarget hκ hs h00 hreal (k+1) :=
  (gammaIspAddConAt hκ hs h00 hreal).lift
    (((gammaIspAddConAt (B := B) (S := Set.univ) (n := k+1) hκ hs h00 hreal).mk').comp gammaPaddingClassesAt)
    (by
      intro a b hab
      exact (gammaIspAddConAt hκ hs h00 hreal).eq.mpr
        ((gammaClassIspAt_padding_iff hκ hs h00 hreal FBase hgamma δ hδ hδ1 h58 hB a b).mpr hab))

theorem integrationTargetPadding_class (U : GammaObjectAt B Set.univ k) :
    integrationTargetPadding hκ hs h00 hreal FBase hgamma δ hδ hδ1 h58 hB
      (rvIntegralClass hκ hs h00 hreal U.toGamma) = rvIntegralClass hκ hs h00 hreal (gammaPadAt U).toGamma := by
  change (gammaIspAddConAt hκ hs h00 hreal).mk' (gammaPaddingClassesAt (gammaIsoClassAt U)) = _
  rw [gammaPaddingClassesAt_class]
  rfl

theorem integrationTargetPadding_injective : Function.Injective
    (integrationTargetPadding (B := B) (k := k) hκ hs h00 hreal FBase hgamma δ hδ hδ1 h58 hB) := by
  intro a b he
  obtain ⟨a,rfl⟩ := (gammaIspAddConAt (B := B) (S := Set.univ) (n := k) hκ hs h00 hreal).mk'_surjective a
  obtain ⟨b,rfl⟩ := (gammaIspAddConAt (B := B) (S := Set.univ) (n := k) hκ hs h00 hreal).mk'_surjective b
  apply (gammaIspAddConAt hκ hs h00 hreal).eq.mpr
  exact (gammaClassIspAt_padding_iff hκ hs h00 hreal FBase hgamma δ hδ hδ1 h58 hB a b).mp
    ((gammaIspAddConAt hκ hs h00 hreal).eq.mp he)

end IntegrationInACVF.Section6.FiniteRV
