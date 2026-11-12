import IntegrationSection6.GlobalIntegrationCharacterization
import IntegrationSection6.GammaRVArbitraryPadding

/-! Equality of global RV integrals is exactly actual lift isomorphism,
including representatives in different finite degrees. -/
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

variable {S : Set M}

theorem rvGlobalIntegralClass_at (U : GammaObjectAt B Set.univ k) :
    rvGlobalIntegralClass hκ hs h00 hreal FBase hgamma δ hδ hδ1 h58 hB U.toGamma =
      (gammaNonzeroIspUnionRingCon hκ hs h00 hreal FBase hgamma δ hδ hδ1 h58 hB).mk'
        (gammaNonzeroResolutionAt k (gammaIsoClassAt U)) := rfl

theorem rvGlobalIntegralClass_eq_iff (U V : GammaRVFiniteObject B k) :
    rvGlobalIntegralClass hκ hs h00 hreal FBase hgamma δ hδ hδ1 h58 hB U =
      rvGlobalIntegralClass hκ hs h00 hreal FBase hgamma δ hδ hδ1 h58 hB V ↔
        GammaIsp hκ hs h00 hreal U V := by
  change integrationTargetToGlobal hκ hs h00 hreal FBase hgamma δ hδ hδ1 h58 hB k
      (rvIntegralClass hκ hs h00 hreal U) =
    integrationTargetToGlobal hκ hs h00 hreal FBase hgamma δ hδ hδ1 h58 hB k
      (rvIntegralClass hκ hs h00 hreal V) ↔ _
  exact (integrationTargetToGlobal_injective hκ hs h00 hreal FBase hgamma δ hδ hδ1 h58 hB k).eq_iff.trans
    (rvIntegralClass_eq_iff hκ hs h00 hreal U V)

theorem rvGlobalIntegralClass_raise {i j : ℕ} (hij : i ≤ j) (U : GammaObjectAt B Set.univ i) :
    rvGlobalIntegralClass hκ hs h00 hreal FBase hgamma δ hδ hδ1 h58 hB (gammaRaiseRVToAt hij U).toGamma =
      rvGlobalIntegralClass hκ hs h00 hreal FBase hgamma δ hδ hδ1 h58 hB U.toGamma := by
  rw [rvGlobalIntegralClass_at,rvGlobalIntegralClass_at,gammaRaiseRVToAt_resolution]

theorem rvGlobalIntegralClass_eq_iff_liftIso {i j : ℕ}
    (U : GammaObjectAt B Set.univ i) (V : GammaObjectAt B Set.univ j) :
    rvGlobalIntegralClass hκ hs h00 hreal FBase hgamma δ hδ hδ1 h58 hB U.toGamma =
      rvGlobalIntegralClass hκ hs h00 hreal FBase hgamma δ hδ hδ1 h58 hB V.toGamma ↔
        Nonempty (GammaIso B U.toGamma.lift V.toGamma.lift) := by
  let l := max i j
  let W := gammaRaiseRVToAt (show i ≤ l from le_max_left i j) U
  let Z := gammaRaiseRVToAt (show j ≤ l from le_max_right i j) V
  obtain ⟨eU⟩ := gammaRaiseRVToAt_lift (show i ≤ l from le_max_left i j) U
  obtain ⟨eV⟩ := gammaRaiseRVToAt_lift (show j ≤ l from le_max_right i j) V
  have hU := rvGlobalIntegralClass_raise hκ hs h00 hreal FBase hgamma δ hδ hδ1 h58 hB
    (show i ≤ l from le_max_left i j) U
  have hV := rvGlobalIntegralClass_raise hκ hs h00 hreal FBase hgamma δ hδ hδ1 h58 hB
    (show j ≤ l from le_max_right i j) V
  constructor
  · intro he
    have hWZ : rvGlobalIntegralClass hκ hs h00 hreal FBase hgamma δ hδ hδ1 h58 hB W.toGamma =
        rvGlobalIntegralClass hκ hs h00 hreal FBase hgamma δ hδ hδ1 h58 hB Z.toGamma :=
      hU.trans (he.trans hV.symm)
    obtain ⟨e⟩ := ((rvGlobalIntegralClass_eq_iff hκ hs h00 hreal FBase hgamma δ hδ hδ1 h58 hB
      W.toGamma Z.toGamma).mp hWZ).liftIsoNative hB
    exact ⟨(eU.trans (gammaLogicInput B) e).trans (gammaLogicInput B) (eV.symm (gammaLogicInput B))⟩
  · rintro ⟨e⟩
    let f := ((eU.symm (gammaLogicInput B)).trans (gammaLogicInput B) e).trans (gammaLogicInput B) eV
    have H := lemma_6_17_kernel hκ hs h00 hreal hgamma δ hδ hδ1 FBase h58 W.toGamma Z.toGamma f
    exact hU.symm.trans (((rvGlobalIntegralClass_eq_iff hκ hs h00 hreal FBase hgamma δ hδ hδ1 h58 hB
      W.toGamma Z.toGamma).mpr H).trans hV)

end IntegrationInACVF.Section6.FiniteRV
