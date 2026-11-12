import IntegrationSection6.GammaUnaryPreparedContractionComparison
import IntegrationSection6.GammaVFPreparedUniformity
import IntegrationSection6.GammaSwappedCommonBlowups

/-! The one-VF-parameter case of Lemma6.14 for full finite-volume family
presentations and arbitrary unary standard contractions. Selected old RV
labels are kept as volume coordinates. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.DefinableGeometry.Space.prod
  SpecialTransformations.Section4.realSpace SpecialTransformations.Milestone0.sortEval
  SpecialTransformations.Section4.vfSpace SpecialTransformations.Section4.rvSpace
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5 SpecialTransformations.Section7
open IntegrationInACVF.Section5
namespace IntegrationInACVF.Section6
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {S R : Set M} {a b k : ℕ}
open FiniteRV

theorem lemma_6_14_unary_presented {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (hreal : Cardinal.mk B.real < κ) (hgamma : Cardinal.mk B.gamma < κ)
    (δ : Values.Gamma (M := M)) (hδ : δ ∈ B.gamma) (hδ1 : 1 < δ) (FBase : VFFieldBase B.real)
    (hBS : B.real ⊆ S) (hBR : B.real ⊆ R)
    (A : SpecialTransformations.Section5.DefSet (M := M) S 1 0) (hA : GammaSetDefinable B (carrier A))
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
    (U : SpecialTransformations.Section5.DefSet (M := M) R 1 a)
    (V : SpecialTransformations.Section5.DefSet (M := M) R 1 b)
    (hU : GammaSetDefinable B (carrier U)) (hV : GammaSetDefinable B (carrier V))
    (hUF : carrier U = vfSchemaSource (carrier A) F) (hVG : carrier V = vfSchemaSource (carrier A) G)
    (hfinU : ∀ (x : Fin 1 → VF (M := M)) (t : Fin k → RV (M := M)),
      {r : Fin a → RV (M := M) | (x,r) ∈ carrier U ∧ r ∘ ρ = t}.Finite)
    (hfinV : ∀ (x : Fin 1 → VF (M := M)) (t : Fin k → RV (M := M)),
      {r : Fin b → RV (M := M) | (x,r) ∈ carrier V ∧ r ∘ τ = t}.Finite)
    {σ υ : Equiv.Perm (Fin 1)} (T : StandardContraction U σ) (E : StandardContraction V υ)
    (hT : GammaProgramDefinable B T.program) (hE : GammaProgramDefinable B E.program) :
    GammaIsp hκ hs h00 hreal (gammaFiniteSelectedContraction hκ hs hreal hBR hU ρ hfinU T hT)
      (gammaFiniteSelectedContraction hκ hs hreal hBR hV τ hfinV E hE) := by
  obtain ⟨l,C,K,hK,hC,BP,hRF,hRG,_,_,hIsp⟩ :=
    gamma_vf_prepared_common_uniformity hκ hs h00 hreal hgamma FBase hBS A hA F G hF hG hCommon
  let e : GammaIso B (carrier A) (carrier C) :=
    ⟨K.equiv,GammaChainDefinable.graph (gammaLogicInput B) K.chain hK⟩
  let D := GammaParameterRecode.prepared K hK
  have hDF : ∀ t ∈ preparedKeyDomain C, (D.object F).finiteRow (fun j => (t j).val) := by
    rintro t ⟨c,rfl⟩
    exact (hRF c).finiteRows.mp (hF (K.inverseMap c))
  have hDG : ∀ t ∈ preparedKeyDomain C, (D.object G).finiteRow (fun j => (t j).val) := by
    rintro t ⟨c,rfl⟩
    exact (hRG c).finiteRows.mp (hG (K.inverseMap c))
  let P := (D.object F).indexedPresentation_finiteRows BP hDF
  let Q := (D.object G).indexedPresentation_finiteRows BP hDG
  have hP := gamma_unary_prepared_contraction_comparison hκ hs h00 hreal hgamma δ hδ hδ1 FBase
    C e hA hC F (D.object F) ρ hRF BP hDF (prepared_selected_rows C e F (D.object F) ρ hRF hLF)
    P U hBR hU hUF hfinU T hT
  have hQ := gamma_unary_prepared_contraction_comparison hκ hs h00 hreal hgamma δ hδ hδ1 FBase
    C e hA hC G (D.object G) τ hRG BP hDG (prepared_selected_rows C e G (D.object G) τ hRG hLG)
    Q V hBR hV hVG hfinV E hE
  have h : GammaIsp hκ hs h00 hreal P.toGamma Q.toGamma :=
    ⟨Set.univ,Set.subset_univ _,Set.subset_univ _,hIsp P Q⟩
  have h' := hP.trans (h.swapVolumeBlocks.trans hQ.symm)
  exact GammaIsp.of_swapVolumeBlocks h'

end IntegrationInACVF.Section6
