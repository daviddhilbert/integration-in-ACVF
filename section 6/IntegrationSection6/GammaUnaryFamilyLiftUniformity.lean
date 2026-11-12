import IntegrationSection6.GammaUnaryPresentedLiftComparison
import IntegrationSection6.GammaVFPreparedUniformityWithoutField
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

theorem gamma_unary_family_lift_uniformity {κ : Cardinal}
    (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (hreal : Cardinal.mk B.real < κ) (hgamma : Cardinal.mk B.gamma < κ)
    (δ : Values.Gamma (M := M)) (hδ : δ ∈ B.gamma) (hδ1 : 1 < δ)
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
      GammaIsp hκ.le hs h00 (small_union_range hκ.le B.real hreal (rawVFParameter x.val)) P.toGamma Q.toGamma)
    (Z W : GammaRVFiniteObject B (k+1))
    (hZ : ∀ t : Fin k → RV (M := M),
      ∀ P : GammaFiniteGraphPresentation ⟨B.real ∪ Set.range (fun j => (t j).val),B.gamma⟩
        (rvObjectArity Z.object) 1 ((gammaVolumeSliceSchema Z).rowDomain (fun j => (t j).val))
        ((gammaVolumeSliceSchema Z).rowVolume (fun j => (t j).val)),
      Nonempty (GammaIso ⟨B.real ∪ Set.range (fun j => (t j).val),B.gamma⟩
        (vfSchemaSource (carrier A) F ∩ {q | q.2 ∘ ρ = t}) P.toGamma.lift))
    (hW : ∀ t : Fin k → RV (M := M),
      ∀ Q : GammaFiniteGraphPresentation ⟨B.real ∪ Set.range (fun j => (t j).val),B.gamma⟩
        (rvObjectArity W.object) 1 ((gammaVolumeSliceSchema W).rowDomain (fun j => (t j).val))
        ((gammaVolumeSliceSchema W).rowVolume (fun j => (t j).val)),
      Nonempty (GammaIso ⟨B.real ∪ Set.range (fun j => (t j).val),B.gamma⟩
        (vfSchemaSource (carrier A) G ∩ {q | q.2 ∘ τ = t}) Q.toGamma.lift)) :
    GammaIsp hκ.le hs h00 hreal Z W := by
  obtain ⟨Rcode,l,C,e,hC,DF,DG,BP,hRF,hRG,hDF,hDG,hIsp⟩ :=
    gamma_vf_prepared_common_uniformity_without_field hκ hs h00 hreal hgamma A hA F G hF hG hCommon
  let P := DF.indexedPresentation_finiteRows BP hDF
  let Q := DG.indexedPresentation_finiteRows BP hDG
  have hP := gamma_unary_prepared_lift_comparison hκ hs h00 hreal hgamma δ hδ hδ1
    C e hA hC F DF ρ hRF BP hDF (prepared_selected_rows C e F DF ρ hRF hLF) P Z hZ
  have hQ := gamma_unary_prepared_lift_comparison hκ hs h00 hreal hgamma δ hδ hδ1
    C e hA hC G DG τ hRG BP hDG (prepared_selected_rows C e G DG τ hRG hLG) Q W hW
  exact hP.trans ((hIsp P Q).swapVolumeBlocks.trans hQ.symm)

end IntegrationInACVF.Section6
