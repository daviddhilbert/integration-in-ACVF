import IntegrationSection6.GammaFiniteWeightAssembly
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

def gammaNonzeroThroughIspAt (n : ℕ) : AddCon (GammaNonzeroThroughAt (B := B) (S := Set.univ) n) :=
  AddCon.comap (gammaFiniteWeightAssemblyAt (B := B) (S := Set.univ) n).toAddMonoidHom
    (map_add _) (gammaIspAddConAt hκ hs h00 hreal)

def gammaNonzeroThroughQuotientEquivAt (n : ℕ) :
    (gammaNonzeroThroughIspAt (B := B) hκ hs h00 hreal n).Quotient ≃+
      IntegrationTarget hκ hs h00 hreal n :=
  AddCon.comapQuotientEquivOfSurj (gammaIspAddConAt (B := B) (S := Set.univ) (n := n) hκ hs h00 hreal)
    (gammaFiniteWeightAssemblyAt (B := B) (S := Set.univ) n).toAddMonoidHom
    (gammaFiniteWeightAssemblyAt (B := B) (S := Set.univ) n).surjective

include FBase hgamma δ hδ hδ1 h58 hB in
theorem gammaNonzeroThroughIspAt_compatible (n : ℕ)
    (a b : GammaNonzeroThroughAt (B := B) (S := Set.univ) n) :
    gammaNonzeroThroughIspAt hκ hs h00 hreal (n+1) (gammaNonzeroThroughInclusionAt n a) (gammaNonzeroThroughInclusionAt n b) ↔
      gammaNonzeroThroughIspAt hκ hs h00 hreal n a b := by
  change gammaClassIspAt hκ hs h00 hreal
    (gammaFiniteWeightAssemblyAt (n+1) (gammaNonzeroThroughInclusionAt n a))
    (gammaFiniteWeightAssemblyAt (n+1) (gammaNonzeroThroughInclusionAt n b)) ↔ _
  rw [gammaFiniteWeightAssemblyAt_compatible,gammaFiniteWeightAssemblyAt_compatible]
  exact gammaClassIspAt_padding_iff hκ hs h00 hreal FBase hgamma δ hδ hδ1 h58 hB _ _

def integrationThroughAt (n : ℕ) : KPlus (gammaVFFinitePresentation B n) ≃+
    (gammaNonzeroThroughIspAt (B := B) hκ hs h00 hreal n).Quotient :=
  (proposition_6_18 hκ hs h00 hreal FBase hgamma δ hδ hδ1 h58 hB).trans
    (gammaNonzeroThroughQuotientEquivAt hκ hs h00 hreal n).symm

end IntegrationInACVF.Section6.FiniteRV
