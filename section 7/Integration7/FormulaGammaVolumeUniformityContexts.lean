module

public import Integration7.PreparedVolumeGeometryGammaGluing
public import Integration7.PreparedGammaVolumeComparisons
public import Integration7.PreparedVolumeGeometryContexts
public import Integration7.GammaVFPreparedVolumeUniformity
public import Integration7.VolumeFormulaWitnessCovers
public import IntegrationSection6.GammaVFParameterBases
public import IntegrationSection6.GammaPreparedIndexPresentation

@[expose] public section

/-! Pointwise valid common-witness formulas with arbitrary auxiliary exception
parameters give one
preparation in a genuine small context and actual common blowups of the
assembled positive objects, without a VF-field hypothesis on the base or
a named-context equality. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
open IntegrationInACVF.Section6
namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {S : Set M} {p a b k : ℕ}

theorem volume_formula_prepared_gamma_uniformity_in_context {κ : Cardinal}
    (hc : CanonicalStructure.IsCanonical (M := M))
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (hreal : Cardinal.mk B.real < κ) (hgamma : Cardinal.mk B.gamma < κ)
    (C₀ : BaseContext M) (hBC₀ : B.real ⊆ (C₀.base : Set M))
    (A : DefSet (M := M) (C₀.base : Set M) p 0) (hA : GammaSetDefinable B (carrier A))
    (F : GammaRVVolumeSchema B p a k (fun _ => .vf)) (G : GammaRVVolumeSchema B p b k (fun _ => .vf))
    (hF : ∀ x : A, F.valid (rawVFParameter x.val))
    (hG : ∀ x : A, G.valid (rawVFParameter x.val))
    (hWitness : ∀ x : A, ∃ H : GammaVolumeCommonSchema F G, H.valid (rawVFParameter x.val)) :
    ∃ D : BaseContext M, ∃ hC₀D : (C₀.base : Set M) ⊆ (D.base : Set M),
      HasPreparedGammaVolumeCommonComparison hc (SpecialTransformations.Section5.extendBase A hC₀D) F G := by
  obtain ⟨J,N,hJ⟩ := volume_formula_common_finite_cover hc hκ hs hreal hgamma F G
    (rawVFParameter '' carrier A) (gamma_raw_vf_parameter_base hA)
    (by rintro z ⟨x,hx,rfl⟩; exact hWitness ⟨x,hx⟩)
  have hCover : ∀ x : A, ∃ W ∈ J, W.valid (rawVFParameter x.val) := by
    intro x
    obtain ⟨W,hW,_,_,hv⟩ := hJ _ ⟨x.val,x.property,rfl⟩
    exact ⟨W,hW,hv⟩
  obtain ⟨D,hC₀D,l,Z,T,hT,hZ,hFA,hGA,hCover'⟩ :=
    prepare_volume_geometry_cover_in_context C₀ hBC₀ A hA F G J hCover
  obtain ⟨BP⟩ := gamma_prepared_index_presentation_exists hκ hs hreal (hBC₀.trans hC₀D) T hT hZ
  have hDF : ∀ t ∈ preparedKeyDomain Z,
      ((GammaVolumeParameterRecode.prepared T hT).volumeObject F).valid (rvValues t) := by
    rintro t ⟨x,rfl⟩
    exact (GammaVolumeParameterRecode.prepared T hT).volumeObject_valid F _ _
      (fun j => ((flatKey x.val).2 j).property) (hFA x) (hF ⟨(T.inverseMap x).val,(T.inverseMap x).property⟩)
  have hDG : ∀ t ∈ preparedKeyDomain Z,
      ((GammaVolumeParameterRecode.prepared T hT).volumeObject G).valid (rvValues t) := by
    rintro t ⟨x,rfl⟩
    exact (GammaVolumeParameterRecode.prepared T hT).volumeObject_valid G _ _
      (fun j => ((flatKey x.val).2 j).property) (hGA x) (hG ⟨(T.inverseMap x).val,(T.inverseMap x).property⟩)
  refine ⟨D,hC₀D,l,Z,T,hT,hZ,BP,hFA,hGA,hDF,hDG,?_⟩
  intro C P Q hP hQ hBP hB
  exact prepared_volume_geometry_gamma_gluing hc F G J T hT (fun x => hF ⟨x.val,x.property⟩) (fun x => hG ⟨x.val,x.property⟩) hFA hGA hCover' C BP
    (fun _ h => h) P Q hP hQ hBP hB

end IntegrationInACVF.Section7
