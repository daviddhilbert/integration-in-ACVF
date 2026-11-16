module

public import Integration7.GammaVolumeLiteralCharts
public import Integration7.GammaVolumeChainFocusSteps
public import Integration7.GammaVolumeChainSchemata
public import IntegrationSection6.FiniteGammaChartedChains

@[expose] public section

/-! Alternating unary special chains admit finite volume blowup formula
witnesses over their original Gamma base. Canonical steps are absorbed
into the next source chart; centripetal steps contribute one blowup. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section5
open IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {p : ℕ} {sp : Fin p → SortTag}
local notation "N" => (@CanonicalStructure.normalize M sM)
local notation "hN" => (@CanonicalStructure.normalized_model M sM hM)

private theorem chain_exists_cast {a b r s : ℕ}
    {F : GammaRVVolumeSchema B p a 0 sp} {G : GammaRVVolumeSchema B p b 0 sp}
    (z : Fin p → M) (h : r = s) :
    (∃ H : GammaVolumeChainSchema F G r, H.valid z) ↔
      (∃ H : GammaVolumeChainSchema F G s, H.valid z) := by
  cases h
  rfl

set_option maxHeartbeats 1600000 in
theorem gamma_unary_special_volume_schema_pair {κ : Cardinal}
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (hreal : Cardinal.mk B.real < κ) (hgamma : Cardinal.mk B.gamma < κ)
    (z : Fin p → M) (hz : ∀ i, sortEval (sp i) (z i))
    (hBS : B.real ∪ Set.range z ⊆ (C.base : Set M))
    {m l : ℕ} {A : SpecialTransformations.Section5.DefSet (M := M) (C.base : Set M) 1 m}
    {Z : SpecialTransformations.Section5.DefSet (M := M) (C.base : Set M) 1 l}
    (T : Chain (C.base : Set M) 1 A Z) :
    ∀ hΓ : GammaChainDefinable ⟨B.real ∪ Set.range z,B.gamma⟩ T,
    (∀ (V : @DefSet LRV M N (@rawRVSpace M N m) (C.base : Set M))
       (v : @Map LRV M N _ _ (C.base : Set M) V (@DefSet.univ LRV M N (@rawRVSpace M N 1) (C.base : Set M)))
       (hV : @Map.FiniteFibres LRV M N _ _ (C.base : Set M) _ _ v)
       (ω : VolumeForm (canonicalRawRVDomain hc V))
       (h : @PresentsLift M N hN (C.base : Set M) 1 (@RVObject.mk M N (C.base : Set M) 1 m V v) (normalizedPointSet A))
       (δ : Fin m) (hDensity : ∀ u, ω.value u = u.val δ),
       T.Alternating none →
       ∀ (hZF : @Map.FiniteFibres LRV M N _ _ (C.base : Set M) _ _ (rvObjectVolume (pullbackObject Z)))
       (hδZ : ∀ t : Z, (t.val.2 (T.labelIndex δ)).val ≠ iRVZero)
       (Ω : PositiveRVVolumeObject (M := M) (C.base : Set M) 0)
       (e : RVVolumeIso Ω
         (⟨canonicalFiniteRVObject hc ⟨@RVObject.mk M N (C.base : Set M) 1 m V v,hV⟩,ω⟩ :
           PositiveRVVolumeObject (M := M) (C.base : Set M) 0)),
       e.GammaDefinable ⟨B.real ∪ Set.range z,B.gamma⟩ →
       ∀ (F : GammaRVVolumeSchema B p Ω.underlying.obj.arity 0 sp)
         (G : GammaRVVolumeSchema B p (1+l) 0 sp),
       F.valid z → G.valid z → RVVolumeSchemaRow Ω F z →
       RVVolumeSchemaRow (pullbackCoordinateVolumeObject hc Z hZF (T.labelIndex δ) hδZ) G z →
       ∃ H : GammaVolumeChainSchema F G T.length, H.valid z) ∧
    (∀ (hAF : @Map.FiniteFibres LRV M N _ _ (C.base : Set M) _ _ (rvObjectVolume (pullbackObject A)))
       (δ : Fin m) (hδ : ∀ a : A, (a.val.2 δ).val ≠ iRVZero),
       IsRVPullback (carrier A) → T.Alternating (some true) →
       ∀ (hZF : @Map.FiniteFibres LRV M N _ _ (C.base : Set M) _ _ (rvObjectVolume (pullbackObject Z)))
       (hδZ : ∀ t : Z, (t.val.2 (T.labelIndex δ)).val ≠ iRVZero)
       (Ω : PositiveRVVolumeObject (M := M) (C.base : Set M) 0)
       (e : RVVolumeIso Ω (pullbackCoordinateVolumeObject hc A hAF δ hδ)),
       e.GammaDefinable ⟨B.real ∪ Set.range z,B.gamma⟩ →
       ∀ (F : GammaRVVolumeSchema B p Ω.underlying.obj.arity 0 sp)
         (G : GammaRVVolumeSchema B p (1+l) 0 sp),
       F.valid z → G.valid z → RVVolumeSchemaRow Ω F z →
       RVVolumeSchemaRow (pullbackCoordinateVolumeObject hc Z hZF (T.labelIndex δ) hδZ) G z →
       ∃ H : GammaVolumeChainSchema F G T.length, H.valid z) := by
  induction T with
  | nil A =>
    intro hΓ
    constructor
    · intro V v hV ω h δ hDensity hT hZF hδZ Ω e he F G hF hG PF PG
      let U := FiniteRV.gammaLiteralAt hBS ⟨@RVObject.mk M N (C.base : Set M) 1 _ V v,hV⟩ h hΓ
      let f := (pullbackVolumePresentationIso hc C U.object ω h δ hDensity).symm hc C
      have hf := (gamma_volume_literal_presentation hc C U ω h hΓ δ hDensity).symm hc C _
      obtain ⟨I,hIS,hIT,hI,_⟩ := gamma_volume_row_comparison_promotion_free hc hκ hs hreal hgamma
        C z hz F G hF hG PF PG (e.trans hc C f) (he.trans hc C _ hf)
      refine ⟨.iso I,hI,?_,?_⟩
      · rw [hIS]; exact F.sameRow_refl z hz
      · rw [hIT]; exact G.sameRow_refl z hz
    · intro hAF δ hδ hAP hT hZF hδZ Ω e he F G hF hG PF PG
      obtain ⟨I,hIS,hIT,hI,_⟩ := gamma_volume_row_comparison_promotion_free hc hκ hs hreal hgamma
        C z hz F G hF hG PF PG e he
      refine ⟨.iso I,hI,?_,?_⟩
      · rw [hIS]; exact F.sameRow_refl z hz
      · rw [hIT]; exact G.sameRow_refl z hz
  | @cons m l r A D Z q tail ih =>
    intro hΓ
    have ih := ih hΓ.2
    cases q with
    | canonical A =>
      constructor
      · intro V v hV ω h δ hDensity hT hZF hδZ Ω e he F G hF hG PF PG
        let U := FiniteRV.gammaLiteralAt hBS ⟨@RVObject.mk M N (C.base : Set M) 1 m V v,hV⟩ h hΓ.1
        let U' := canonicalFiniteRVKeys U.object
        let ω' := canonicalFiniteVolumeForm hc U.object ω
        have hRep := normalizedPresentsLift_canonical h
        have hf := gamma_volume_canonical_family hc C U ω h hΓ.1
        obtain ⟨H,hH⟩ := ih.1 (@RVObject.domain M N (C.base : Set M) 1 U'.obj)
          (@RVObject.volume M N (C.base : Set M) 1 U'.obj) U'.property ω' hRep (Fin.natAdd 1 δ)
          (canonicalFiniteVolumeForm_density hc U.object ω δ hDensity) (chainAlternating_none hT.2)
          hZF hδZ Ω (e.trans hc C (canonicalVolumeFamilyIso hc C U.object ω)) (he.trans hc C _ hf)
          F G hF hG PF PG
        change ∃ H : GammaVolumeChainSchema F G (0+tail.length), H.valid z
        exact (chain_exists_cast z (zero_add tail.length)).mpr ⟨H,hH⟩
      · intro hAF δ hδ hAP hT hZF hδZ Ω e he F G hF hG PF PG
        let U : @RVFiniteObject M N (C.base : Set M) 1 := ⟨pullbackObject A,hAF⟩
        let P := pullbackCoordinateVolumeObject hc A hAF δ hδ
        have hRep := normalizedCanonicalImage_presents A hAP
        obtain ⟨H,hH⟩ := ih.1 (@RVObject.domain M N (C.base : Set M) 1 U.obj)
          (@RVObject.volume M N (C.base : Set M) 1 U.obj) U.property P.form hRep (Fin.natAdd 1 δ)
          (fun _ => rfl) (chainAlternating_none hT.2) hZF hδZ Ω e he F G hF hG PF PG
        change ∃ H : GammaVolumeChainSchema F G (0+tail.length), H.valid z
        exact (chain_exists_cast z (zero_add tail.length)).mpr ⟨H,hH⟩
    | @centripetal m i j D =>
      have hi : i = Fin.last 0 := Subsingleton.elim _ _
      subst i
      constructor
      · intro V v hV ω h δ hDensity hT hZF hδZ Ω e he F G hF hG PF PG
        let U := FiniteRV.gammaLiteralAt hBS ⟨@RVObject.mk M N (C.base : Set M) 1 m V v,hV⟩ h hΓ.1.1
        have hAP := (pullback_normalize (carrier A)).mp
          (@PresentsLift.pullback M N hN (C.base : Set M) 1 U.object.obj (normalizedPointSet A) h)
        have hDF := partialFocusImage_finite C U.object h D
        have hδD := focus_density_label_nonzero D δ
          (lift_density_label_nonzero
            (⟨canonicalFiniteRVObject hc U.object,ω⟩ : PositiveRVVolumeObject (M := M) (C.base : Set M) 0)
            (canonicalRVObject_presentsLift hc h) δ hDensity)
        let P := partialFocusVolumeImage hc C U.object ω h D δ hDensity
        let PΓ := FiniteRV.gammaPullbackAt hBS D.etaImage
          (GammaPrimitiveDefinable.target (gammaLogicInput _) (.centripetal D) hΓ.1) hDF
        obtain ⟨W,hW,PW⟩ := gamma_canonical_label_object_promotion hc C hκ hs hreal hgamma z hz PΓ P.form
          (Fin.natAdd 1 δ) (fun _ => rfl)
        obtain ⟨head,hhead⟩ := gamma_partial_focus_volume_schema_precomposed hc C hκ hs hreal hgamma z hz
          U ω h D hΓ.1.1 hΓ.1.2 δ hDensity Ω e he F W hF hW PF PW
        have hid := gamma_volume_refl hc C P (canonical_gamma_object_volume_graph hc PΓ)
        obtain ⟨rest,hrest⟩ := ih.2 hDF δ hδD (D.etaImage_pullback hAP) hT.2 hZF hδZ P
          (RVVolumeIso.refl hc C P) hid W G hW hG PW PG
        change ∃ H : GammaVolumeChainSchema F G (1+tail.length), H.valid z
        rw [Nat.add_comm 1 tail.length]
        exact ⟨.step W head rest,hW,hhead,hrest⟩
      · intro hAF δ hδ hAP hT
        exact False.elim (hT.1 rfl)

end IntegrationInACVF.Section7
