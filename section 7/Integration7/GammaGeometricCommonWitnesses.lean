module

public import Integration7.GammaChartedVolumeCommonPromotion
public import Integration7.FormulaVolumeUniformityContexts

@[expose] public section

/-! Original-Gamma geometric witnesses can live in arbitrary containing
contexts. Their formula promotion supplies the general preparation theorem
without identifying the context with a named term closure. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
open IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {p a b k : ℕ} {sp : Fin p → SortTag}

def GammaRVVolumeSchema.commonByGammaGeometry (F : GammaRVVolumeSchema B p a k sp)
    (G : GammaRVVolumeSchema B p b k sp) (z : Fin p → M) : Prop :=
  ∃ C : BaseContext M,
    ∃ U V : GammaVolumeObjects ⟨B.real ∪ Set.range z,B.gamma⟩ (C.base : Set M) k,
      ∃ (ha : U.val.underlying.obj.arity = a) (hb : V.val.underlying.obj.arity = b),
        RVVolumeSchemaRow U.val (ha.symm ▸ F) z ∧ RVVolumeSchemaRow V.val (hb.symm ▸ G) z ∧
          GammaVolumeBlowupEquivalent ⟨B.real ∪ Set.range z,B.gamma⟩ (C.base : Set M) k U V

theorem gamma_volume_formula_witness_from_geometry {κ : Cardinal}
    (hc : CanonicalStructure.IsCanonical (M := M))
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (hreal : Cardinal.mk B.real < κ) (hgamma : Cardinal.mk B.gamma < κ)
    (F : GammaRVVolumeSchema B p a k sp) (G : GammaRVVolumeSchema B p b k sp)
    (z : Fin p → M) (hF : F.valid z) (hG : G.valid z) (h : F.commonByGammaGeometry G z) :
    ∃ H : GammaVolumeCommonSchema F G, H.valid z := by
  obtain ⟨C,U,V,ha,hb,PU,PV,h⟩ := h
  subst a b
  exact gamma_charted_volume_common_promotion hc C hκ hs h00 hreal hgamma z hF.1.1
    F G hF hG PU PV h

theorem gamma_geometric_prepared_volume_uniformity {κ : Cardinal}
    (hc : CanonicalStructure.IsCanonical (M := M))
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (hreal : Cardinal.mk B.real < κ) (hgamma : Cardinal.mk B.gamma < κ)
    (C₀ : BaseContext M) (hBC₀ : B.real ⊆ (C₀.base : Set M))
    (A : DefSet (M := M) (C₀.base : Set M) p 0) (hA : GammaSetDefinable B (carrier A))
    (F : GammaRVVolumeSchema B p a k (fun _ => .vf)) (G : GammaRVVolumeSchema B p b k (fun _ => .vf))
    (hF : ∀ x : A, F.valid (rawVFParameter x.val))
    (hG : ∀ x : A, G.valid (rawVFParameter x.val))
    (h : ∀ x : A, F.commonByGammaGeometry G (rawVFParameter x.val)) :
    ∃ D : BaseContext M, ∃ hC₀D : (C₀.base : Set M) ⊆ (D.base : Set M),
      HasPreparedVolumeCommonComparison hc (SpecialTransformations.Section5.extendBase A hC₀D) F G := by
  apply volume_formula_prepared_common_uniformity_in_context hc hκ hs h00 hreal hgamma C₀ hBC₀ A hA F G hF hG
  intro x
  exact gamma_volume_formula_witness_from_geometry hc hκ hs h00 hreal hgamma F G _ (hF x) (hG x) (h x)

end IntegrationInACVF.Section7
