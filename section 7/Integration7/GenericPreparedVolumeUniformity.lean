module

public import Integration7.PreparedFiniteVolumeGeometry
public import Integration7.PreparedEssentialVolumeGluing
public import Integration7.PreparedGenericRVCells
public import Integration7.GenericGammaWitnessCovers
public import Integration7.PreparedGammaVolumeComparisons
public import IntegrationSection6.GammaVFParameterBases

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section
/-! Generic VF witnesses suffice for actual Gamma common blowups of the
whole prepared indexed objects. Every essential prepared base cell has a
generic inverse image; zero-coordinate base cells have no essential labels. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
open IntegrationInACVF.Section6
namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {S : Set M} {p a b k : ℕ}

theorem generic_volume_formula_prepared_uniformity_in_context {κ : Cardinal}
    (hc : CanonicalStructure.IsCanonical (M := M))
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (hreal : Cardinal.mk B.real < κ) (hgamma : Cardinal.mk B.gamma < κ)
    (C₀ : BaseContext M) (hBC₀ : B.real ⊆ (C₀.base : Set M))
    (A : DefSet (M := M) (C₀.base : Set M) p 0) (hA : GammaSetDefinable B (carrier A))
    (F : GammaRVVolumeSchema B p a k (fun _ => .vf)) (G : GammaRVVolumeSchema B p b k (fun _ => .vf))
    (hF : ∀ x : A, F.valid (rawVFParameter x.val))
    (hG : ∀ x : A, G.valid (rawVFParameter x.val))
    (hWitness : ∀ x : Fin p → VFType (M := M),
      AlgebraicIndependent (vfParameterField B.real) x →
      ∃ H : GammaVolumeCommonSchema F G, H.valid (vfValues x)) :
    ∃ D : BaseContext M, ∃ hC₀D : (C₀.base : Set M) ⊆ (D.base : Set M),
      HasPreparedGammaVolumeCommonComparison hc (SpecialTransformations.Section5.extendBase A hC₀D) F G := by
  obtain ⟨J,hJ⟩ := gamma_finite_witnesses_at_generic_points B hκ hs hreal hgamma
    (fun H : GammaVolumeCommonSchema F G => {z | H.valid z}) (fun H => H.valid_definable hc) hWitness
  obtain ⟨D,hC₀D,l,Z,T,hT,hZ,hFA,hGA,hAg⟩ :=
    prepare_volume_geometry_in_context C₀ hBC₀ A hA F G J
  have hCover : ∀ x : Z, (∀ j, (rv (x.val.1 j)).val ≠ iRVZero) → ∃ W ∈ J,
      ((GammaVolumeParameterRecode.prepared T hT).commonWithFrozenParameters W).valid (rawPreparedKey x.val) := by
    intro x hx
    obtain ⟨y,hy,hind⟩ := exists_generic_inverse_in_prepared_cell hc D T hZ x hx
    have hindB := independent_over_smaller_real_base (hBC₀.trans hC₀D) hind
    obtain ⟨W,hW,hvalid⟩ := hJ (T.inverseMap y).val.1 hindB
    have hRecoded := (GammaVolumeParameterRecode.prepared T hT).commonWithFrozenParameters_valid W _ _
      (fun j => ((T.inverseMap y).val.1 j).property) (fun j => ((flatKey y.val).2 j).property)
      (hFA y) (hGA y) (hAg W hW y) hvalid
    have hk : rawPreparedKey y.val = rawPreparedKey x.val :=
      congrArg (fun q => fun j => (q.2 j).val) ((flatKey_eq_iff _ _).mpr hy)
    exact ⟨W,hW,hk ▸ hRecoded⟩
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
  exact prepared_volume_essential_geometry_gluing hc hκ hs hreal hgamma F G J T hT
    (fun x => hF ⟨x.val,x.property⟩) (fun x => hG ⟨x.val,x.property⟩)
    hFA hGA hCover C BP P Q hP hQ hBP hB

end IntegrationInACVF.Section7
