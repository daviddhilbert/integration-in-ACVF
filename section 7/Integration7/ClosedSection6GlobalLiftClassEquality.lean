import Integration7.CompletedSection6Kernel
import Integration7.ClosedSection6GlobalIntegrationCharacterization
import IntegrationSection6.GlobalLiftClassEquality
import IntegrationSection6.GlobalIntegrationCharacterization
import IntegrationSection6.GammaRVArbitraryPadding

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

variable {S : Set M}


theorem rvGlobalIntegralClass_at (U : GammaObjectAt B Set.univ k) :
    rvGlobalIntegralClass hκ hs h00 hreal FBase hgamma δ hδ hδ1 hc hB U.toGamma =
      (gammaNonzeroIspUnionRingCon hκ hs h00 hreal FBase hgamma δ hδ hδ1 hc hB).mk'
        (gammaNonzeroResolutionAt k (gammaIsoClassAt U)) := rfl

theorem rvGlobalIntegralClass_eq_iff (U V : GammaRVFiniteObject B k) :
    rvGlobalIntegralClass hκ hs h00 hreal FBase hgamma δ hδ hδ1 hc hB U =
      rvGlobalIntegralClass hκ hs h00 hreal FBase hgamma δ hδ hδ1 hc hB V ↔
        GammaIsp hκ hs h00 hreal U V := by
  change integrationTargetToGlobal hκ hs h00 hreal FBase hgamma δ hδ hδ1 hc hB k
      (rvIntegralClass hκ hs h00 hreal U) =
    integrationTargetToGlobal hκ hs h00 hreal FBase hgamma δ hδ hδ1 hc hB k
      (rvIntegralClass hκ hs h00 hreal V) ↔ _
  exact (integrationTargetToGlobal_injective hκ hs h00 hreal FBase hgamma δ hδ hδ1 hc hB k).eq_iff.trans
    (rvIntegralClass_eq_iff hκ hs h00 hreal U V)

theorem rvGlobalIntegralClass_raise {i j : ℕ} (hij : i ≤ j) (U : GammaObjectAt B Set.univ i) :
    rvGlobalIntegralClass hκ hs h00 hreal FBase hgamma δ hδ hδ1 hc hB (gammaRaiseRVToAt hij U).toGamma =
      rvGlobalIntegralClass hκ hs h00 hreal FBase hgamma δ hδ hδ1 hc hB U.toGamma := by
  rw [rvGlobalIntegralClass_at,rvGlobalIntegralClass_at,gammaRaiseRVToAt_resolution]

theorem rvGlobalIntegralClass_eq_iff_liftIso {i j : ℕ}
    (U : GammaObjectAt B Set.univ i) (V : GammaObjectAt B Set.univ j) :
    rvGlobalIntegralClass hκ hs h00 hreal FBase hgamma δ hδ hδ1 hc hB U.toGamma =
      rvGlobalIntegralClass hκ hs h00 hreal FBase hgamma δ hδ hδ1 hc hB V.toGamma ↔
        Nonempty (GammaIso B U.toGamma.lift V.toGamma.lift) := by
  let l := max i j
  let W := gammaRaiseRVToAt (show i ≤ l from le_max_left i j) U
  let Z := gammaRaiseRVToAt (show j ≤ l from le_max_right i j) V
  obtain ⟨eU⟩ := gammaRaiseRVToAt_lift (show i ≤ l from le_max_left i j) U
  obtain ⟨eV⟩ := gammaRaiseRVToAt_lift (show j ≤ l from le_max_right i j) V
  have hU := rvGlobalIntegralClass_raise hκ hs h00 hreal FBase hgamma δ hδ hδ1 hc hB
    (show i ≤ l from le_max_left i j) U
  have hV := rvGlobalIntegralClass_raise hκ hs h00 hreal FBase hgamma δ hδ hδ1 hc hB
    (show j ≤ l from le_max_right i j) V
  constructor
  · intro he
    have hWZ : rvGlobalIntegralClass hκ hs h00 hreal FBase hgamma δ hδ hδ1 hc hB W.toGamma =
        rvGlobalIntegralClass hκ hs h00 hreal FBase hgamma δ hδ hδ1 hc hB Z.toGamma :=
      hU.trans (he.trans hV.symm)
    obtain ⟨e⟩ := ((rvGlobalIntegralClass_eq_iff hκ hs h00 hreal FBase hgamma δ hδ hδ1 hc hB
      W.toGamma Z.toGamma).mp hWZ).liftIsoNative hB
    exact ⟨(eU.trans (gammaLogicInput B) e).trans (gammaLogicInput B) (eV.symm (gammaLogicInput B))⟩
  · rintro ⟨e⟩
    let f := ((eU.symm (gammaLogicInput B)).trans (gammaLogicInput B) e).trans (gammaLogicInput B) eV
    have H := (lemma_6_17_kernel (hgen := ⟨hB⟩)) hκ hs h00 hreal hgamma δ hδ hδ1 FBase hc W.toGamma Z.toGamma f
    exact hU.symm.trans (((rvGlobalIntegralClass_eq_iff hκ hs h00 hreal FBase hgamma δ hδ hδ1 hc hB
      W.toGamma Z.toGamma).mpr H).trans hV)

end IntegrationInACVF.Section7.CompletedSection6
