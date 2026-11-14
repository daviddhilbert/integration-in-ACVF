import Integration7.PartialFocusVolumeBlowups
import Integration7.CanonicalVolumeFamilySteps
import Integration7.VolumeBlowupTransport
import IntegrationSection6.SpecialChainBlowup

/-! Alternating unary special chains give actual finite chains of
volume blowups. Canonical labels contribute isomorphisms, and every
centripetal step contributes one blowup with the retained density. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section5 (Chain Primitive carrier IsRVPullback pullbackObject rvObjectVolume)
open SpecialTransformations.DefinableGeometry
namespace IntegrationInACVF.Section7
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
local notation "N" => (@CanonicalStructure.normalize M sM)
local notation "hN" => (@CanonicalStructure.normalized_model M sM hM)

theorem unary_special_volume_chain_pair
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    {m l : ℕ} {A : SpecialTransformations.Section5.DefSet (M := M) (C.base : Set M) 1 m}
    {Z : SpecialTransformations.Section5.DefSet (M := M) (C.base : Set M) 1 l}
    (T : Chain (C.base : Set M) 1 A Z) :
    (∀ (V : @DefSet LRV M N (@rawRVSpace M N m) (C.base : Set M))
       (v : @Map LRV M N _ _ (C.base : Set M) V (@DefSet.univ LRV M N (@rawRVSpace M N 1) (C.base : Set M)))
       (hV : @Map.FiniteFibres LRV M N _ _ (C.base : Set M) _ _ v)
       (ω : VolumeForm (canonicalRawRVDomain hc V))
       (h : @Section6.PresentsLift M N hN (C.base : Set M) 1 (@RVObject.mk M N (C.base : Set M) 1 m V v)
         (Section6.normalizedPointSet A)) (δ : Fin m) (hDensity : ∀ u, ω.value u = u.val δ),
       T.Alternating none →
       ∃ hZF : @Map.FiniteFibres LRV M N _ _ (C.base : Set M) _ _ (rvObjectVolume (pullbackObject Z)),
       ∃ hδZ : ∀ z : Z, (z.val.2 (T.labelIndex δ)).val ≠ iRVZero,
       ∃ W : PositiveRVVolumeObject (M := M) (C.base : Set M) 0,
         IteratedVolumeBlowup T.length
           (⟨canonicalFiniteRVObject hc ⟨@RVObject.mk M N (C.base : Set M) 1 m V v,hV⟩,ω⟩ :
             PositiveRVVolumeObject (M := M) (C.base : Set M) 0) W ∧
         Nonempty (RVVolumeIso W (pullbackCoordinateVolumeObject hc Z hZF (T.labelIndex δ) hδZ))) ∧
    (∀ (hAF : @Map.FiniteFibres LRV M N _ _ (C.base : Set M) _ _ (rvObjectVolume (pullbackObject A)))
       (δ : Fin m) (hδ : ∀ a : A, (a.val.2 δ).val ≠ iRVZero),
       IsRVPullback (carrier A) → T.Alternating (some true) →
       ∃ hZF : @Map.FiniteFibres LRV M N _ _ (C.base : Set M) _ _ (rvObjectVolume (pullbackObject Z)),
       ∃ hδZ : ∀ z : Z, (z.val.2 (T.labelIndex δ)).val ≠ iRVZero,
       ∃ W : PositiveRVVolumeObject (M := M) (C.base : Set M) 0,
         IteratedVolumeBlowup T.length (pullbackCoordinateVolumeObject hc A hAF δ hδ) W ∧
         Nonempty (RVVolumeIso W (pullbackCoordinateVolumeObject hc Z hZF (T.labelIndex δ) hδZ))) := by
  induction T with
  | nil A =>
    constructor
    · intro V v hV ω h δ hDensity hT
      let F : @RVFiniteObject M N (C.base : Set M) 1 := ⟨@RVObject.mk M N (C.base : Set M) 1 _ V v,hV⟩
      let U : PositiveRVVolumeObject (M := M) (C.base : Set M) 0 := ⟨canonicalFiniteRVObject hc F,ω⟩
      have hAF := (@Section6.finite_volume_iso M N hN (C.base : Set M) 1 (pullbackObject A) F.obj
        (Section6.pullbackPresentationIso h)).mpr F.property
      have hδ := lift_density_label_nonzero U (canonicalRVObject_presentsLift hc h) δ hDensity
      exact ⟨hAF,hδ,U,.refl U,⟨(pullbackVolumePresentationIso hc C F ω h δ hDensity).symm hc C⟩⟩
    · intro hAF δ hδ hAP hT
      let U := pullbackCoordinateVolumeObject hc A hAF δ hδ
      exact ⟨hAF,hδ,U,.refl U,⟨RVVolumeIso.refl hc C U⟩⟩
  | @cons m l r A B Z p tail ih =>
    cases p with
    | canonical A =>
      constructor
      · intro V v hV ω h δ hDensity hT
        let F : @RVFiniteObject M N (C.base : Set M) 1 := ⟨@RVObject.mk M N (C.base : Set M) 1 m V v,hV⟩
        let F' := canonicalFiniteRVKeys F
        let ω' := canonicalFiniteVolumeForm hc F ω
        have hRep := Section6.normalizedPresentsLift_canonical h
        obtain ⟨hZF,hδZ,W,hW,⟨e⟩⟩ := ih.1 (@RVObject.domain M N (C.base : Set M) 1 F'.obj)
          (@RVObject.volume M N (C.base : Set M) 1 F'.obj) F'.property ω' hRep (Fin.natAdd 1 δ)
          (canonicalFiniteVolumeForm_density hc F ω δ hDensity) (Section6.chainAlternating_none hT.2)
        obtain ⟨W',hW',⟨f⟩⟩ := hW.transport_source hc C (canonicalVolumeFamilyIso hc C F ω)
        exact ⟨hZF,hδZ,W',by simpa only [Chain.length,Primitive.length,zero_add] using hW',⟨f.trans hc C e⟩⟩
      · intro hAF δ hδ hAP hT
        let F : @RVFiniteObject M N (C.base : Set M) 1 := ⟨pullbackObject A,hAF⟩
        let U := pullbackCoordinateVolumeObject hc A hAF δ hδ
        have hRep := Section6.normalizedCanonicalImage_presents A hAP
        obtain ⟨hZF,hδZ,W,hW,he⟩ := ih.1 (@RVObject.domain M N (C.base : Set M) 1 F.obj)
          (@RVObject.volume M N (C.base : Set M) 1 F.obj) F.property U.form hRep (Fin.natAdd 1 δ)
          (fun _ => rfl) (Section6.chainAlternating_none hT.2)
        change IteratedVolumeBlowup tail.length U W at hW
        exact ⟨hZF,hδZ,W,by simpa only [Chain.length,Primitive.length,zero_add] using hW,he⟩
    | @centripetal m i j D =>
      have hi : i = Fin.last 0 := Subsingleton.elim _ _
      subst i
      constructor
      · intro V v hV ω h δ hDensity hT
        let F : @RVFiniteObject M N (C.base : Set M) 1 := ⟨@RVObject.mk M N (C.base : Set M) 1 m V v,hV⟩
        let U : PositiveRVVolumeObject (M := M) (C.base : Set M) 0 := ⟨canonicalFiniteRVObject hc F,ω⟩
        have hAP := (Section6.pullback_normalize (carrier A)).mp
          (@Section6.PresentsLift.pullback M N hN (C.base : Set M) 1 F.obj (Section6.normalizedPointSet A) h)
        have hDF := partialFocusImage_finite C F h D
        have hδD := focus_density_label_nonzero D δ
          (lift_density_label_nonzero U (canonicalRVObject_presentsLift hc h) δ hDensity)
        obtain ⟨hZF,hδZ,W,hW,he⟩ := ih.2 hDF δ hδD (D.etaImage_pullback hAP) hT.2
        refine ⟨hZF,hδZ,W,?_,he⟩
        simpa only [Chain.length,Primitive.length,Nat.add_comm] using
          (IteratedVolumeBlowup.step ⟨partialFocusVolumeBlowup hc C F ω h D δ hDensity⟩ hW)
      · intro hAF δ hδ hAP hT
        exact False.elim (hT.1 rfl)

end IntegrationInACVF.Section7
