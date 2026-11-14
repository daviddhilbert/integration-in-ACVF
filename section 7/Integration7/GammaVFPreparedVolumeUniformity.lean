import Integration7.GammaPreparedVolumeGluing
import Integration7.ZeroAuxVolumeWitnessCompactness
import IntegrationSection6.GammaVFParameterBases
import IntegrationSection6.GammaPreparedIndexPresentation

/-! Pointwise common volume blowups over named VF parameters give one
preparation and actual common blowups of the assembled positive objects. -/
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

def HasPreparedVolumeCommonComparison
    (hc : CanonicalStructure.IsCanonical (M := M))
    (A : DefSet (M := M) S p 0)
    (F : GammaRVVolumeSchema B p a k (fun _ => .vf))
    (G : GammaRVVolumeSchema B p b k (fun _ => .vf)) : Prop :=
    ∃ l : ℕ, ∃ Z : DefSet (M := M) S p l, ∃ T : SpecialBijection A Z,
      ∃ hT : GammaChainDefinable B T.chain, ∃ hZ : IsRVPullback (carrier Z),
      ∃ BP : PreparedIndexPresentation B Z,
        (∀ x : Z, (GammaVolumeParameterRecode.prepared T hT).VolumeObjectAgreement F
          (rawVFParameter (T.inverseMap x).val) (rawPreparedKey x.val)) ∧
        (∀ x : Z, (GammaVolumeParameterRecode.prepared T hT).VolumeObjectAgreement G
          (rawVFParameter (T.inverseMap x).val) (rawPreparedKey x.val)) ∧
        (∀ t ∈ preparedKeyDomain Z,
          ((GammaVolumeParameterRecode.prepared T hT).volumeObject F).valid (rvValues t)) ∧
        (∀ t ∈ preparedKeyDomain Z,
          ((GammaVolumeParameterRecode.prepared T hT).volumeObject G).valid (rvValues t)) ∧
        ∀ (C : BaseContext M)
          (P : ((GammaVolumeParameterRecode.prepared T hT).volumeObject F).IndexedPresentation BP)
          (Q : ((GammaVolumeParameterRecode.prepared T hT).volumeObject G).IndexedPresentation BP)
          (hP : P.finite.codes ⊆ (C.base : Set M)) (hQ : Q.finite.codes ⊆ (C.base : Set M)),
          BP.codes ⊆ (C.base : Set M) → B.real ⊆ (C.base : Set M) →
          ∃ D : BaseContext M, ∃ hCD : (C.base : Set M) ⊆ (D.base : Set M),
            VolumeBlowupEquivalent ((P.inContext hc C hP).toObject.extend hCD)
              ((Q.inContext hc C hQ).toObject.extend hCD)

theorem gamma_vf_prepared_volume_common_uniformity {κ : Cardinal}
    (hc : CanonicalStructure.IsCanonical (M := M))
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (hreal : Cardinal.mk B.real < κ) (hgamma : Cardinal.mk B.gamma < κ)
    (FBase : VFFieldBase B.real) (hBS : B.real ⊆ S)
    (A : DefSet (M := M) S p 0) (hA : GammaSetDefinable B (carrier A))
    (F : GammaRVVolumeSchema B p a k (fun _ => .vf)) (G : GammaRVVolumeSchema B p b k (fun _ => .vf))
    (hF : ∀ x : A, F.valid (rawVFParameter x.val))
    (hG : ∀ x : A, G.valid (rawVFParameter x.val))
    (hCommon : ∀ x : A, F.commonInNamedContext G (rawVFParameter x.val)) :
    HasPreparedVolumeCommonComparison hc A F G := by
  obtain ⟨J,N,hJ⟩ := gamma_volume_common_finite_cover_no_auxiliary hc hκ hs h00 hreal hgamma F G
    (rawVFParameter '' carrier A) (gamma_raw_vf_parameter_base hA)
    (by rintro z ⟨x,hx,rfl⟩; exact hF ⟨x,hx⟩)
    (by rintro z ⟨x,hx,rfl⟩; exact hG ⟨x,hx⟩)
    (by rintro z ⟨x,hx,rfl⟩; exact hCommon ⟨x,hx⟩)
  have hCover : ∀ x : A, ∃ W ∈ J, W.val.valid (rawVFParameter x.val) := by
    intro x
    obtain ⟨W,hW,_,_,hv⟩ := hJ _ ⟨x.val,x.property,rfl⟩
    exact ⟨W,hW,hv⟩
  obtain ⟨l,Z,T,hT,hZ,hFA,hGA,hCover'⟩ :=
    gamma_prepare_volume_common_witness_cover hs h00 hreal FBase hBS A hA F G J hCover
  obtain ⟨BP⟩ := gamma_prepared_index_presentation_exists hκ hs hreal hBS T hT hZ
  have hDF : ∀ t ∈ preparedKeyDomain Z,
      ((GammaVolumeParameterRecode.prepared T hT).volumeObject F).valid (rvValues t) := by
    rintro t ⟨x,rfl⟩
    exact (GammaVolumeParameterRecode.prepared T hT).volumeObject_valid F _ _
      (fun j => ((flatKey x.val).2 j).property) (hFA x) (hF (T.inverseMap x))
  have hDG : ∀ t ∈ preparedKeyDomain Z,
      ((GammaVolumeParameterRecode.prepared T hT).volumeObject G).valid (rvValues t) := by
    rintro t ⟨x,rfl⟩
    exact (GammaVolumeParameterRecode.prepared T hT).volumeObject_valid G _ _
      (fun j => ((flatKey x.val).2 j).property) (hGA x) (hG (T.inverseMap x))
  refine ⟨l,Z,T,hT,hZ,BP,hFA,hGA,hDF,hDG,?_⟩
  intro C P Q hP hQ hBP hB
  exact gamma_prepared_volume_witness_gluing hc F G J T hT hF hG hFA hGA hCover' C BP
    (fun _ h => h) P Q hP hQ hBP hB

end IntegrationInACVF.Section7
