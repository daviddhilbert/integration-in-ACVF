import IntegrationSection6.GammaPreparedWitnessGluing
import IntegrationSection6.GammaPreparedIndexPresentation
import IntegrationSection6.GammaVFParameterBases
import IntegrationSection6.GammaCommonFiniteRowCompactness

/-! Pointwise common blowups in a VF-parameter family have simultaneous
preparation and an actual common blowup of the assembled RV[p+k] objects.
All descent data are obtained from genuine finite witnesses over the
original real/Gamma base. -/
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
namespace IntegrationInACVF.Section6
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {S : Set M} {p a b k : ℕ}
open FiniteRV

theorem gamma_vf_prepared_common_uniformity {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (hreal : Cardinal.mk B.real < κ) (hgamma : Cardinal.mk B.gamma < κ)
    (FBase : VFFieldBase B.real) (hBS : B.real ⊆ S)
    (A : DefSet (M := M) S p 0) (hA : GammaSetDefinable B (carrier A))
    (F : GammaFiniteRVSchema B p a k (fun _ => .vf)) (G : GammaFiniteRVSchema B p b k (fun _ => .vf))
    (hF : ∀ x : A, F.finiteRow (rawVFParameter x.val))
    (hG : ∀ x : A, G.finiteRow (rawVFParameter x.val))
    (hCommon : ∀ x : A,
      ∀ P : GammaFiniteGraphPresentation ⟨B.real ∪ Set.range (rawVFParameter x.val),B.gamma⟩ a k
        (F.rowDomain (rawVFParameter x.val)) (F.rowVolume (rawVFParameter x.val)),
      ∀ Q : GammaFiniteGraphPresentation ⟨B.real ∪ Set.range (rawVFParameter x.val),B.gamma⟩ b k
        (G.rowDomain (rawVFParameter x.val)) (G.rowVolume (rawVFParameter x.val)),
      GammaIsp hκ hs h00 (small_union_range hκ B.real hreal (rawVFParameter x.val)) P.toGamma Q.toGamma) :
    ∃ l : ℕ, ∃ C : DefSet (M := M) S p l, ∃ T : SpecialBijection A C,
      ∃ hT : GammaChainDefinable B T.chain, ∃ hC : IsRVPullback (carrier C),
      ∃ BP : PreparedIndexPresentation B C,
        (∀ x : C, (GammaParameterRecode.prepared T hT).ObjectAgreement F
          (rawVFParameter (T.inverseMap x).val) (rawPreparedKey x.val)) ∧
        (∀ x : C, (GammaParameterRecode.prepared T hT).ObjectAgreement G
          (rawVFParameter (T.inverseMap x).val) (rawPreparedKey x.val)) ∧
        Nonempty (((GammaParameterRecode.prepared T hT).object F).IndexedPresentation BP) ∧
        Nonempty (((GammaParameterRecode.prepared T hT).object G).IndexedPresentation BP) ∧
        ∀ (P : ((GammaParameterRecode.prepared T hT).object F).IndexedPresentation BP)
          (Q : ((GammaParameterRecode.prepared T hT).object G).IndexedPresentation BP),
          GammaIspAt hκ hs h00 hreal (gammaUniversalObject P.toGamma) (gammaUniversalObject Q.toGamma) := by
  have hFA : ∀ z ∈ rawVFParameter '' carrier A, F.finiteRow z := by
    rintro z ⟨x,hx,rfl⟩
    exact hF ⟨x,hx⟩
  have hGA : ∀ z ∈ rawVFParameter '' carrier A, G.finiteRow z := by
    rintro z ⟨x,hx,rfl⟩
    exact hG ⟨x,hx⟩
  obtain ⟨J,hJ⟩ := gamma_common_finite_cover_of_finiteRows hκ hs h00 hreal hgamma F G
    (rawVFParameter '' carrier A) (gamma_raw_vf_parameter_base hA) hFA hGA (by
      rintro z ⟨x,hx,rfl⟩
      exact hCommon ⟨x,hx⟩)
  have hCover : ∀ x : A, ∃ W ∈ J, W.valid (rawVFParameter x.val) :=
    fun x => hJ _ ⟨x.val,x.property,rfl⟩
  obtain ⟨l,C,T,hT,hC,hAgF,hAgG,hCover'⟩ :=
    gamma_prepare_common_witness_cover hs h00 hreal FBase hBS A hA F G J hCover
  obtain ⟨BP⟩ := gamma_prepared_index_presentation_exists hκ hs hreal hBS T hT hC
  have hDF : ∀ t ∈ preparedKeyDomain C,
      ((GammaParameterRecode.prepared T hT).object F).finiteRow (fun j => (t j).val) := by
    rintro t ⟨x,rfl⟩
    exact (hAgF x).finiteRows.mp (hF (T.inverseMap x))
  have hDG : ∀ t ∈ preparedKeyDomain C,
      ((GammaParameterRecode.prepared T hT).object G).finiteRow (fun j => (t j).val) := by
    rintro t ⟨x,rfl⟩
    exact (hAgG x).finiteRows.mp (hG (T.inverseMap x))
  exact ⟨l,C,T,hT,hC,BP,hAgF,hAgG,
    ⟨((GammaParameterRecode.prepared T hT).object F).indexedPresentation_finiteRows BP hDF⟩,
    ⟨((GammaParameterRecode.prepared T hT).object G).indexedPresentation_finiteRows BP hDG⟩,
    gamma_prepared_witness_gluing hκ hs h00 hreal F G J T hT hF hG hAgF hAgG hCover' BP
      (fun _ h => h)⟩

end IntegrationInACVF.Section6
