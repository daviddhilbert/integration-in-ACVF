module

public import Integration7.CompletedSection6Kernel
public import Integration7.ClosedSection6GammaIspPadding
public import IntegrationSection6.FiniteNonzeroIntegration
public import IntegrationSection6.GammaFiniteWeightAssembly
public import IntegrationSection6.GammaIspPadding

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! Closed generated-base Section6 integration. The former universal
Section5 input is replaced by the canonical-model certificate; its kernel
uses the proved generated-base contraction comparison. Original finite
objects, actual lifting, scissor addition and Cartesian products are retained.
This module keeps the dependent data and consumers in one coherent interface. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5 SpecialTransformations.Section7
open SpecialTransformations.Section4.PositiveAdditiveGrothendieck
open IntegrationInACVF.Section6 IntegrationInACVF.Section6.FiniteRV
namespace IntegrationInACVF.Section7.CompletedSection6
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {k : ℕ} {S : Set M}
local instance : Fact (B.real ⊆ (Set.univ : Set M)) := ⟨Set.subset_univ _⟩
variable {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
variable (h00 : M ⊨ Axioms.ACVF00) (hreal : Cardinal.mk B.real < κ) (FBase : VFFieldBase B.real)
variable (hgamma : Cardinal.mk B.gamma < κ) (δ : Values.Gamma (M := M)) (hδ : δ ∈ B.gamma) (hδ1 : 1 < δ)
variable (hc : CanonicalStructure.IsCanonical (M := M))

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

include FBase hgamma δ hδ hδ1 hc hB in
theorem gammaNonzeroThroughIspAt_compatible (n : ℕ)
    (a b : GammaNonzeroThroughAt (B := B) (S := Set.univ) n) :
    gammaNonzeroThroughIspAt hκ hs h00 hreal (n+1) (gammaNonzeroThroughInclusionAt n a) (gammaNonzeroThroughInclusionAt n b) ↔
      gammaNonzeroThroughIspAt hκ hs h00 hreal n a b := by
  change gammaClassIspAt hκ hs h00 hreal
    (gammaFiniteWeightAssemblyAt (n+1) (gammaNonzeroThroughInclusionAt n a))
    (gammaFiniteWeightAssemblyAt (n+1) (gammaNonzeroThroughInclusionAt n b)) ↔ _
  rw [gammaFiniteWeightAssemblyAt_compatible,gammaFiniteWeightAssemblyAt_compatible]
  exact gammaClassIspAt_padding_iff hκ hs h00 hreal FBase hgamma δ hδ hδ1 hc hB _ _

def integrationThroughAt (n : ℕ) : KPlus (gammaVFFinitePresentation B n) ≃+
    (gammaNonzeroThroughIspAt (B := B) hκ hs h00 hreal n).Quotient :=
  (proposition_6_18 hκ hs h00 hreal FBase hgamma δ hδ hδ1 hc hB).trans
    (gammaNonzeroThroughQuotientEquivAt hκ hs h00 hreal n).symm

end IntegrationInACVF.Section7.CompletedSection6
