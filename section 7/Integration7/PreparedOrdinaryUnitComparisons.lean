module

public import Integration7.GenericFiniteIsomorphismPreparation
public import Integration7.GammaOrdinaryEssentialUniformity
public import IntegrationSection6.GammaPreparedIndexPresentation
public import IntegrationSection6.GammaPreparedIndexValues

@[expose] public section

/-! Generic finite-row isomorphisms construct a genuine simultaneous
ordinary preparation and original-Gamma unit-volume comparison. -/
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
variable {B : Base (M := M)} {S : Set M} {a b : ℕ}

def HasPreparedOrdinaryUnitComparison
    (hc : CanonicalStructure.IsCanonical (M := M))
    (A : DefSet (M := M) S 1 0)
    (F : GammaFiniteRVSchema B 1 a 0) (G : GammaFiniteRVSchema B 1 b 0) : Prop :=
  ∃ l : ℕ, ∃ Z : DefSet (M := M) S 1 l, ∃ T : SpecialBijection A Z,
  ∃ hT : GammaChainDefinable B T.chain, ∃ hZ : IsRVPullback (carrier Z),
  ∃ BP : PreparedIndexPresentation B Z,
    (∀ q : Z, (GammaParameterRecode.prepared T hT).ObjectAgreement F
      (rawVFParameter (T.inverseMap q).val) (rawPreparedKey q.val)) ∧
    (∀ q : Z, (GammaParameterRecode.prepared T hT).ObjectAgreement G
      (rawVFParameter (T.inverseMap q).val) (rawPreparedKey q.val)) ∧
    (∀ t ∈ preparedKeyDomain Z, ((GammaParameterRecode.prepared T hT).object F).valid (rvValues t)) ∧
    (∀ t ∈ preparedKeyDomain Z, ((GammaParameterRecode.prepared T hT).object G).valid (rvValues t)) ∧
    ∀ (C : BaseContext M)
      (P : ((GammaParameterRecode.prepared T hT).object F).IndexedPresentation BP)
      (Q : ((GammaParameterRecode.prepared T hT).object G).IndexedPresentation BP)
      (hPC : P.codes ⊆ (C.base : Set M)) (hQC : Q.codes ⊆ (C.base : Set M)),
      B.real ⊆ (C.base : Set M) →
      ∃ D : BaseContext M, ∃ hCD : (C.base : Set M) ⊆ (D.base : Set M),
      ∃ e : RVVolumeIso ((gammaUnitVolumeObject hc C P.toGamma hPC).extend hCD)
        ((gammaUnitVolumeObject hc C Q.toGamma hQC).extend hCD), e.GammaDefinable B

theorem generic_ordinary_unit_comparison_preparation {κ : Cardinal}
    (hc : CanonicalStructure.IsCanonical (M := M))
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (hreal : Cardinal.mk B.real < κ) (hgamma : Cardinal.mk B.gamma < κ)
    (C₀ : BaseContext M) (hBC₀ : B.real ⊆ (C₀.base : Set M))
    (A : DefSet (M := M) (C₀.base : Set M) 1 0) (hA : GammaSetDefinable B (carrier A))
    (F : GammaFiniteRVSchema B 1 a 0) (G : GammaFiniteRVSchema B 1 b 0)
    (hF : ∀ x : A, F.valid (rawVFParameter x.val))
    (hG : ∀ x : A, G.valid (rawVFParameter x.val))
    (hWitness : ∀ x : Fin 1 → VFType (M := M), AlgebraicIndependent (vfParameterField B.real) x →
      ∃ H : GammaRelationFormula B 1 a b (fun _ => .vf), (gammaFiniteRowChartSchema F G H).valid (vfValues x)) :
    ∃ D : BaseContext M, ∃ hC₀D : (C₀.base : Set M) ⊆ (D.base : Set M),
      HasPreparedOrdinaryUnitComparison hc (extendBase A hC₀D) F G := by
  obtain ⟨J,D,hC₀D,l,Z,T,hT,hZ,hFA,hGA,hCover⟩ := generic_finite_isomorphism_preparation_in_context
    hc hκ hs hreal hgamma C₀ hBC₀ A hA F G hWitness
  let K := GammaParameterRecode.prepared T hT
  obtain ⟨BP⟩ := gamma_prepared_index_presentation_exists hκ hs hreal (hBC₀.trans hC₀D) T hT hZ
  have hDF : ∀ t ∈ preparedKeyDomain Z, (K.object F).valid (rvValues t) := by
    rintro t ⟨q,rfl⟩
    exact K.object_valid F _ _ (fun j => ((flatKey q.val).2 j).property) (hFA q)
      (hF ⟨(T.inverseMap q).val,(T.inverseMap q).property⟩)
  have hDG : ∀ t ∈ preparedKeyDomain Z, (K.object G).valid (rvValues t) := by
    rintro t ⟨q,rfl⟩
    exact K.object_valid G _ _ (fun j => ((flatKey q.val).2 j).property) (hGA q)
      (hG ⟨(T.inverseMap q).val,(T.inverseMap q).property⟩)
  refine ⟨D,hC₀D,l,Z,T,hT,hZ,BP,hFA,hGA,hDF,hDG,?_⟩
  intro C P Q hPC hQC hBC
  apply gamma_ordinary_indexed_uniformity_on_essential_indices hc hκ hs hreal hgamma
    BP (K.object F) (K.object G) hDF hDG ?_ C P Q hPC hQC hBC
  rintro t ⟨q,rfl⟩ hNZ
  have hNZ' : ∀ j, (rv (q.val.1 j)).val ≠ iRVZero := by
    intro j hz
    apply hNZ j
    have hv := congrFun (PreparedIndexPresentation.totalVolume_eq Z BP (flatKey q.val).2 ⟨q,rfl⟩) j
    calc
      (BP.totalVolume (flatKey q.val).2 j).val =
          ((flatKey q.val).2 (Fin.castAdd l j)).val := congrArg Subtype.val hv
      _ = (rv (q.val.1 j)).val := by simp only [flatKey,Fin.append_left,key]
      _ = iRVZero := hz
  obtain ⟨H,_,hH⟩ := hCover q hNZ'
  exact ⟨K.relation H,hH⟩

end IntegrationInACVF.Section7
