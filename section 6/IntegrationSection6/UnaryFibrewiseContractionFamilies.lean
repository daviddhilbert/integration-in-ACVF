import IntegrationSection6.UnaryFibrewiseContractionComparison
import IntegrationSection6.FiniteSchemaContractions

/-! Unary Lemma6.14 for arbitrary finite family presentations. Both
contraction objects, their finiteness and their complete Gamma certificates
are constructed from the family data. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5 SpecialTransformations.Section7
open IntegrationInACVF.Section5
namespace IntegrationInACVF.Section6
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {S R : Set M} {a b k : ℕ}
open FiniteRV

theorem lemma_6_14_unary_families {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (hreal : Cardinal.mk B.real < κ) (hgamma : Cardinal.mk B.gamma < κ)
    (δ : Values.Gamma (M := M)) (hδ : δ ∈ B.gamma) (hδ1 : 1 < δ) (FBase : VFFieldBase B.real)
    (hBS : B.real ⊆ S) (hBR : B.real ⊆ R)
    (A : DefSet (M := M) S 1 0) (hA : GammaSetDefinable B (carrier A))
    (F : GammaFiniteRVSchema B 1 a k) (G : GammaFiniteRVSchema B 1 b k)
    (ρ : Fin k → Fin a) (τ : Fin k → Fin b)
    (hF : ∀ x : A, F.finiteRow (rawVFParameter x.val))
    (hG : ∀ x : A, G.finiteRow (rawVFParameter x.val))
    (hLF : ∀ x : A, ∀ r y, F.rowVolume (rawVFParameter x.val) r y ↔
      r ∈ F.rowDomain (rawVFParameter x.val) ∧ r ∘ ρ = y)
    (hLG : ∀ x : A, ∀ r y, G.rowVolume (rawVFParameter x.val) r y ↔
      r ∈ G.rowDomain (rawVFParameter x.val) ∧ r ∘ τ = y)
    (hCommon : ∀ x : A,
      ∀ P : GammaFiniteGraphPresentation ⟨B.real ∪ Set.range (rawVFParameter x.val),B.gamma⟩ a k
        (F.rowDomain (rawVFParameter x.val)) (F.rowVolume (rawVFParameter x.val)),
      ∀ Q : GammaFiniteGraphPresentation ⟨B.real ∪ Set.range (rawVFParameter x.val),B.gamma⟩ b k
        (G.rowDomain (rawVFParameter x.val)) (G.rowVolume (rawVFParameter x.val)),
      GammaIsp hκ hs h00 (small_union_range hκ B.real hreal (rawVFParameter x.val)) P.toGamma Q.toGamma)
    (U : DefSet (M := M) R 1 a) (V : DefSet (M := M) R 1 b)
    (hUF : carrier U = vfSchemaSource (carrier A) F) (hVG : carrier V = vfSchemaSource (carrier A) G)
    {σ υ : Equiv.Perm (Fin 1)} (T : StandardContraction U σ) (E : StandardContraction V υ)
    (hT : GammaProgramDefinable B T.program) (hE : GammaProgramDefinable B E.program) :
    GammaIsp hκ hs h00 hreal
      (gammaFiniteSchemaContraction hκ hs hreal hBR (carrier A) hA F ρ hF hLF U hUF T hT)
      (gammaFiniteSchemaContraction hκ hs hreal hBR (carrier A) hA G τ hG hLG V hVG E hE) :=
  lemma_6_14_unary_presented hκ hs h00 hreal hgamma δ hδ hδ1 FBase hBS hBR A hA F G ρ τ
    hF hG hLF hLG hCommon U V (schemaSource_gamma (carrier A) hA F U hUF)
    (schemaSource_gamma (carrier A) hA G V hVG) hUF hVG
    (schemaSource_selected_fibres (carrier A) F ρ hF hLF U hUF)
    (schemaSource_selected_fibres (carrier A) G τ hG hLG V hVG) T E hT hE

end IntegrationInACVF.Section6
