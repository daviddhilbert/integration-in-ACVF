import IntegrationSection6.GammaPreparedWitnessCoverWithoutField
import IntegrationSection6.GammaVFPreparedUniformity

/-! VF-parameter common-blowup uniformity over an arbitrary small base
under uncountable saturation. The coefficient field is internal; every
object, special map and geometric witness retains the original Gamma base. -/
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

theorem gamma_vf_prepared_common_uniformity_without_field {κ : Cardinal}
    (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (hreal : Cardinal.mk B.real < κ) (hgamma : Cardinal.mk B.gamma < κ)
    (A : DefSet (M := M) S p 0) (hA : GammaSetDefinable B (carrier A))
    (F : GammaFiniteRVSchema B p a k) (G : GammaFiniteRVSchema B p b k)
    (hF : ∀ x : A, F.finiteRow (rawVFParameter x.val))
    (hG : ∀ x : A, G.finiteRow (rawVFParameter x.val))
    (hCommon : ∀ x : A,
      ∀ P : GammaFiniteGraphPresentation ⟨B.real ∪ Set.range (rawVFParameter x.val),B.gamma⟩ a k
        (F.rowDomain (rawVFParameter x.val)) (F.rowVolume (rawVFParameter x.val)),
      ∀ Q : GammaFiniteGraphPresentation ⟨B.real ∪ Set.range (rawVFParameter x.val),B.gamma⟩ b k
        (G.rowDomain (rawVFParameter x.val)) (G.rowVolume (rawVFParameter x.val)),
      GammaIsp hκ.le hs h00 (small_union_range hκ.le B.real hreal (rawVFParameter x.val)) P.toGamma Q.toGamma) :
    ∃ R : Set M, ∃ l : ℕ, ∃ C : DefSet (M := M) R p l,
      ∃ e : GammaIso B (carrier A) (carrier C), IsRVPullback (carrier C) ∧
      ∃ DF : GammaFiniteRVSchema B (p+l) a k (fun _ => .rv),
      ∃ DG : GammaFiniteRVSchema B (p+l) b k (fun _ => .rv), ∃ BP : PreparedIndexPresentation B C,
        (∀ c : C, GammaSchemaRowAgreement F (rawVFParameter (e.equiv.symm c).val) DF (rawPreparedKey c.val)) ∧
        (∀ c : C, GammaSchemaRowAgreement G (rawVFParameter (e.equiv.symm c).val) DG (rawPreparedKey c.val)) ∧
        (∀ t ∈ preparedKeyDomain C, DF.finiteRow (fun j => (t j).val)) ∧
        (∀ t ∈ preparedKeyDomain C, DG.finiteRow (fun j => (t j).val)) ∧
        ∀ (P : DF.IndexedPresentation BP) (Q : DG.IndexedPresentation BP),
          GammaIsp hκ.le hs h00 hreal P.toGamma Q.toGamma := by
  have hFA : ∀ z ∈ rawVFParameter '' carrier A, F.finiteRow z := by
    rintro z ⟨x,hx,rfl⟩
    exact hF ⟨x,hx⟩
  have hGA : ∀ z ∈ rawVFParameter '' carrier A, G.finiteRow z := by
    rintro z ⟨x,hx,rfl⟩
    exact hG ⟨x,hx⟩
  obtain ⟨J,hJ⟩ := gamma_common_finite_cover_of_finiteRows hκ.le hs h00 hreal hgamma F G
    (rawVFParameter '' carrier A) (gamma_raw_vf_parameter_base hA) hFA hGA (by
      rintro z ⟨x,hx,rfl⟩
      exact hCommon ⟨x,hx⟩)
  have hCover : ∀ x : A, ∃ W ∈ J, W.valid (rawVFParameter x.val) :=
    fun x => hJ _ ⟨x.val,x.property,rfl⟩
  obtain ⟨R,hSR,hBR,l,C,T,hT,hC,hRF,hRG,hCover'⟩ :=
    gamma_prepare_common_witness_cover_without_field hκ hs h00 hreal A hA F G J hCover
  let e : GammaIso B (carrier A) (carrier C) :=
    ⟨T.equiv,GammaChainDefinable.graph (gammaLogicInput B) T.chain hT⟩
  let D := GammaParameterRecode.prepared T hT
  obtain ⟨BP⟩ := gamma_prepared_index_presentation_exists hκ.le hs hreal hBR T hT hC
  have hDF : ∀ t ∈ preparedKeyDomain C, (D.object F).finiteRow (fun j => (t j).val) := by
    rintro t ⟨c,rfl⟩
    exact (hRF c).finiteRows.mp (hF ⟨(T.inverseMap c).val,(T.inverseMap c).property⟩)
  have hDG : ∀ t ∈ preparedKeyDomain C, (D.object G).finiteRow (fun j => (t j).val) := by
    rintro t ⟨c,rfl⟩
    exact (hRG c).finiteRows.mp (hG ⟨(T.inverseMap c).val,(T.inverseMap c).property⟩)
  refine ⟨R,l,C,e,hC,D.object F,D.object G,BP,hRF,hRG,hDF,hDG,?_⟩
  intro P Q
  exact ⟨Set.univ,Set.subset_univ _,Set.subset_univ _,
    gamma_prepared_witness_gluing hκ.le hs h00 hreal F G J T hT
      (fun x => hF ⟨x.val,x.property⟩) (fun x => hG ⟨x.val,x.property⟩)
      hRF hRG hCover' BP (fun _ h => h) P Q⟩

end IntegrationInACVF.Section6
