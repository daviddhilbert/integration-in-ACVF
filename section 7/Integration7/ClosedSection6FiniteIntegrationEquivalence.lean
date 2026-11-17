module

public import Integration7.CompletedSection6Kernel
public import Integration7.ClosedSection6FiniteIntegrationMap
public import IntegrationSection6.FiniteIntegrationEquivalence
public import IntegrationSection6.FiniteIntegrationMap

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
variable {B : Base (M := M)} {k : ℕ}
local instance : Fact (B.real ⊆ (Set.univ : Set M)) := ⟨Set.subset_univ _⟩
variable {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
variable (h00 : M ⊨ Axioms.ACVF00) (hreal : Cardinal.mk B.real < κ) (FBase : VFFieldBase B.real)
variable (hgamma : Cardinal.mk B.gamma < κ) (δ : Values.Gamma (M := M)) (hδ : δ ∈ B.gamma) (hδ1 : 1 < δ)
variable (hc : CanonicalStructure.IsCanonical (M := M))

variable (hB : VFGammaGeneratedBase B)


theorem integrationAt_quotient_lift :
    ((integrationAt (hgen := ⟨hB⟩)) hκ hs h00 hreal FBase hgamma δ hδ hδ1 hc).comp
      (nativeGammaQuotientLiftAt (S := Set.univ) (k := k) hκ hs h00 hreal hB) = AddMonoidHom.id _ := by
  apply AddMonoidHom.ext
  intro z
  obtain ⟨a,rfl⟩ := (gammaIspAddConAt (B := B) (S := Set.univ) (n := k) hκ hs h00 hreal).mk'_surjective z
  obtain ⟨U,rfl⟩ := gammaIsoClassAt_surjective a
  change (integrationAt (hgen := ⟨hB⟩)) hκ hs h00 hreal FBase hgamma δ hδ hδ1 hc
    (nativeGammaQuotientLiftAt hκ hs h00 hreal hB
      ((gammaIspAddConAt hκ hs h00 hreal).mk' (gammaIsoClassAt U))) = _
  rw [nativeGammaQuotientLiftAt_class,(integrationAt_lift_class (hgen := ⟨hB⟩))]
  rfl

theorem nativeQuotientLift_rvIntegralClass (U : GammaRVFiniteObject B k) :
    nativeGammaQuotientLiftAt (S := Set.univ) hκ hs h00 hreal hB (rvIntegralClass hκ hs h00 hreal U) =
      gammaFiniteLiftScissorClass U := by
  change nativeGammaQuotientLiftAt hκ hs h00 hreal hB
    ((gammaIspAddConAt hκ hs h00 hreal).mk' (gammaIsoClassAt (gammaUniversalObject U))) = _
  rw [nativeGammaQuotientLiftAt_class]
  obtain ⟨e⟩ := gammaRVIso_liftIso hκ hs h00 hreal hB (gammaObjectPresentationIso U (Set.subset_univ _))
  exact (of_iso (gammaVFFinitePresentation B k) ⟨e⟩).symm

theorem quotientLift_integrationAt :
    (nativeGammaQuotientLiftAt (S := Set.univ) (k := k) hκ hs h00 hreal hB).comp
      ((integrationAt (hgen := ⟨hB⟩)) hκ hs h00 hreal FBase hgamma δ hδ hδ1 hc) = AddMonoidHom.id _ := by
  apply hom_ext (gammaVFFinitePresentation B k)
  intro A
  change nativeGammaQuotientLiftAt hκ hs h00 hreal hB
    ((integrationAt (hgen := ⟨hB⟩)) hκ hs h00 hreal FBase hgamma δ hδ hδ1 hc (of (gammaVFFinitePresentation B k) A)) = _
  rw [(integrationAt_class (hgen := ⟨hB⟩))]
  change nativeGammaQuotientLiftAt hκ hs h00 hreal hB
    (rvIntegralClass hκ hs h00 hreal ((finiteVFLiftRepresentative (hgen := ⟨hB⟩)) hκ hs h00 hreal FBase A).1) = _
  rw [nativeQuotientLift_rvIntegralClass]
  exact (of_iso (gammaVFFinitePresentation B k) ⟨((finiteVFLiftRepresentative (hgen := ⟨hB⟩)) hκ hs h00 hreal FBase A).2⟩).symm

/-- Proposition6.18 in RV[k]: additive integration is inverse to actual lifting. -/
def proposition_6_18 : KPlus (gammaVFFinitePresentation B k) ≃+ IntegrationTarget hκ hs h00 hreal k where
  toFun := (integrationAt (hgen := ⟨hB⟩)) hκ hs h00 hreal FBase hgamma δ hδ hδ1 hc
  invFun := nativeGammaQuotientLiftAt hκ hs h00 hreal hB
  left_inv x := DFunLike.congr_fun (quotientLift_integrationAt hκ hs h00 hreal FBase hgamma δ hδ hδ1 hc hB) x
  right_inv x := DFunLike.congr_fun (integrationAt_quotient_lift hκ hs h00 hreal FBase hgamma δ hδ hδ1 hc hB) x
  map_add' := map_add _

theorem proposition_6_18_lift (U : GammaRVFiniteObject B k) :
    proposition_6_18 hκ hs h00 hreal FBase hgamma δ hδ hδ1 hc hB (gammaFiniteLiftScissorClass U) =
      rvIntegralClass hκ hs h00 hreal U :=
  (integrationAt_lift_class (hgen := ⟨hB⟩)) hκ hs h00 hreal FBase hgamma δ hδ hδ1 hc U

end IntegrationInACVF.Section7.CompletedSection6
