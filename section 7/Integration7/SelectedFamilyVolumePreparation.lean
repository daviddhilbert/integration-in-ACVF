import Integration7.SelectedFamilyVolumeSchemata
import Integration7.SelectedDensityGraphRowMaps
import Integration7.GammaVFPreparedVolumeUniformity
import Integration7.VolumeBlowupEquivalence

/-! The fibrewise hypothesis of positive selected Lemma 7.5 supplies
the exact inputs to simultaneous volume-witness preparation and gluing. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4
open SpecialTransformations.Section5 (VF GammaSetDefinable gammaLogicInput carrier setDefinable)
open IntegrationInACVF.Section6
namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {C : BaseContext M} {n a b k : ℕ}

theorem selected_densityGraph_common
    (hc : CanonicalStructure.IsCanonical (M := M))
    (F : SelectedVFVolumeFamily C n a k) (G : SelectedVFVolumeFamily C n b k)
    (x : Fin n → VFType (M := M))
    (h : VolumeBlowupEquivalent (F.rowInContext x) (G.rowInContext x)) :
    VolumeBlowupEquivalent (F.densityGraph.rowInContext x) (G.densityGraph.rowInContext x) :=
  ((VolumeBlowupEquivalent.of_iso (vfParameterVolumeContext C x)
    ((F.densityGraphRowIso hc x).symm hc (vfParameterVolumeContext C x))).trans hc
      (vfParameterVolumeContext C x) h).trans hc (vfParameterVolumeContext C x)
        (VolumeBlowupEquivalent.of_iso (vfParameterVolumeContext C x) (G.densityGraphRowIso hc x))

theorem selected_densityGraph_named_common
    (hc : CanonicalStructure.IsCanonical (M := M)) (Ξ : Set (Values.Gamma (M := M)))
    (F : SelectedVFVolumeFamily C n a k) (G : SelectedVFVolumeFamily C n b k) (NF NG : ℕ)
    (x : Fin n → VFType (M := M))
    (h : VolumeBlowupEquivalent (F.rowInContext x) (G.rowInContext x)) :
    ((F.densityGraphSchema hc Ξ).withBound NF).commonInNamedContext
      ((G.densityGraphSchema hc Ξ).withBound NG) (fun j => (x j).val) := by
  refine ⟨vfParameterVolumeContext C x,rfl,F.densityGraph.rowInContext x,G.densityGraph.rowInContext x,
    rfl,rfl,?_,?_,selected_densityGraph_common hc F G x h⟩
  · exact (F.densityGraphSchema_rows hc Ξ x).congr
      (GammaRVVolumeSchema.sameRow_symm ((F.densityGraphSchema hc Ξ).withBound_sameRow NF _
        (fun j => (x j).property)))
  · exact (G.densityGraphSchema_rows hc Ξ x).congr
      (GammaRVVolumeSchema.sameRow_symm ((G.densityGraphSchema hc Ξ).withBound_sameRow NG _
        (fun j => (x j).property)))

theorem selected_family_volume_preparation
    (hc : CanonicalStructure.IsCanonical (M := M)) (Ξ : Set (Values.Gamma (M := M)))
    (hΞ : Cardinal.mk Ξ < C.κ) (FBase : VFFieldBase (C.base : Set M))
    (F : SelectedVFVolumeFamily C n a k) (G : SelectedVFVolumeFamily C n b k)
    (hCommon : ∀ x : Fin n → VFType (M := M),
      VolumeBlowupEquivalent (F.rowInContext x) (G.rowInContext x)) :
    ∃ NF NG : ℕ,
      (∀ x : Fin n → VFType (M := M), ((F.densityGraphSchema hc Ξ).withBound NF).valid (fun j => (x j).val)) ∧
      (∀ x : Fin n → VFType (M := M), ((G.densityGraphSchema hc Ξ).withBound NG).valid (fun j => (x j).val)) ∧
      HasPreparedVolumeCommonComparison hc
        (SpecialTransformations.Section5.PresentedSet.univ
          (SpecialTransformations.Section5.pointSpace (M := M) n 0) (C.base : Set M))
        ((F.densityGraphSchema hc Ξ).withBound NF) ((G.densityGraphSchema hc Ξ).withBound NG) := by
  obtain ⟨NF,hNF⟩ := F.densityGraphSchema_uniform_bound hc Ξ hΞ
  obtain ⟨NG,hNG⟩ := G.densityGraphSchema_uniform_bound hc Ξ hΞ
  refine ⟨NF,NG,hNF,hNG,?_⟩
  let A := SpecialTransformations.Section5.PresentedSet.univ
    (SpecialTransformations.Section5.pointSpace (M := M) n 0) (C.base : Set M)
  have hA : GammaSetDefinable (⟨(C.base : Set M),Ξ⟩ : Base (M := M)) (carrier A) :=
    (gammaLogicInput _).real_set _ (setDefinable A)
  exact gamma_vf_prepared_volume_common_uniformity hc C.uncountable.le C.saturated C.model00 C.small hΞ
    FBase (Set.Subset.refl _) A hA _ _ (fun x => hNF x.val.1) (fun x => hNG x.val.1)
    (fun x => selected_densityGraph_named_common hc Ξ F G NF NG x.val.1 (hCommon x.val.1))

end IntegrationInACVF.Section7
