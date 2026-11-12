import IntegrationSection6.FiniteIntegrationMap

/-! The actual additive integration equivalence, Proposition6.18. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5 SpecialTransformations.Section7
open SpecialTransformations.Section4.PositiveAdditiveGrothendieck
namespace IntegrationInACVF.Section6.FiniteRV
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {k : ℕ}
local instance : Fact (B.real ⊆ (Set.univ : Set M)) := ⟨Set.subset_univ _⟩
variable {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
variable (h00 : M ⊨ Axioms.ACVF00) (hreal : Cardinal.mk B.real < κ) (FBase : VFFieldBase B.real)
variable (hgamma : Cardinal.mk B.gamma < κ) (δ : Values.Gamma (M := M)) (hδ : δ ∈ B.gamma) (hδ1 : 1 < δ)
variable (h58 : Section5TwoOrderInputAll hκ hs)

variable (hB : VFGammaGeneratedBase B)

theorem integrationAt_quotient_lift :
    (integrationAt hκ hs h00 hreal FBase hgamma δ hδ hδ1 h58).comp
      (nativeGammaQuotientLiftAt (S := Set.univ) (k := k) hκ hs h00 hreal hB) = AddMonoidHom.id _ := by
  apply AddMonoidHom.ext
  intro z
  obtain ⟨a,rfl⟩ := (gammaIspAddConAt (B := B) (S := Set.univ) (n := k) hκ hs h00 hreal).mk'_surjective z
  obtain ⟨U,rfl⟩ := gammaIsoClassAt_surjective a
  change integrationAt hκ hs h00 hreal FBase hgamma δ hδ hδ1 h58
    (nativeGammaQuotientLiftAt hκ hs h00 hreal hB
      ((gammaIspAddConAt hκ hs h00 hreal).mk' (gammaIsoClassAt U))) = _
  rw [nativeGammaQuotientLiftAt_class,integrationAt_lift_class]
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
      (integrationAt hκ hs h00 hreal FBase hgamma δ hδ hδ1 h58) = AddMonoidHom.id _ := by
  apply hom_ext (gammaVFFinitePresentation B k)
  intro A
  change nativeGammaQuotientLiftAt hκ hs h00 hreal hB
    (integrationAt hκ hs h00 hreal FBase hgamma δ hδ hδ1 h58 (of (gammaVFFinitePresentation B k) A)) = _
  rw [integrationAt_class]
  change nativeGammaQuotientLiftAt hκ hs h00 hreal hB
    (rvIntegralClass hκ hs h00 hreal (finiteVFLiftRepresentative hκ hs h00 hreal FBase A).1) = _
  rw [nativeQuotientLift_rvIntegralClass]
  exact (of_iso (gammaVFFinitePresentation B k) ⟨(finiteVFLiftRepresentative hκ hs h00 hreal FBase A).2⟩).symm

/-- Proposition6.18 in RV[k]: additive integration is inverse to actual lifting. -/
def proposition_6_18 : KPlus (gammaVFFinitePresentation B k) ≃+ IntegrationTarget hκ hs h00 hreal k where
  toFun := integrationAt hκ hs h00 hreal FBase hgamma δ hδ hδ1 h58
  invFun := nativeGammaQuotientLiftAt hκ hs h00 hreal hB
  left_inv x := DFunLike.congr_fun (quotientLift_integrationAt hκ hs h00 hreal FBase hgamma δ hδ hδ1 h58 hB) x
  right_inv x := DFunLike.congr_fun (integrationAt_quotient_lift hκ hs h00 hreal FBase hgamma δ hδ hδ1 h58 hB) x
  map_add' := map_add _

theorem proposition_6_18_lift (U : GammaRVFiniteObject B k) :
    proposition_6_18 hκ hs h00 hreal FBase hgamma δ hδ hδ1 h58 hB (gammaFiniteLiftScissorClass U) =
      rvIntegralClass hκ hs h00 hreal U :=
  integrationAt_lift_class hκ hs h00 hreal FBase hgamma δ hδ hδ1 h58 U

end IntegrationInACVF.Section6.FiniteRV
