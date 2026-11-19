import Integration7.GammaFunZeroHeadAdditivity

/-! Additivity of Gamma-named Jacobian transforms: away from a small Gamma set the Jacobian
transform of a sum has literally the same rows as the sum of the Jacobian transforms, since all
three prescribed Jacobian value maps agree with the pure Jacobian there. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section9
open SpecialTransformations.Section5 (Point GammaSetDefinable GammaGraphDefinable gammaLogicInput carrier VF RV)
open IntegrationInACVF.Section5 IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {C : BaseContext M} {n a b k : ℕ}

theorem selected_volume_family_sum_base (F : SelectedVFVolumeFamily C n a k) (H : SelectedVFVolumeFamily C n b k)
    (P : (Fin n → VFType (M := M)) → Prop) (hF : ∀ p : F.domain, P p.val.1) (hH : ∀ p : H.domain, P p.val.1)
    (p : (selectedVolumeFamilySum F H).domain) : P p.val.1 := by
  rcases (mem_selected_volume_family_sum F H p.val).mp p.property with ⟨u,hu⟩ | ⟨v,hv⟩
  · rw [← hu]
    exact hF u
  · rw [← hv]
    exact hH v

variable {X Y : SpecialTransformations.DefinableGeometry.DefSet
  (SpecialTransformations.Section4.rawVFSpace (M := M) n) (C.base : Set M)}

theorem jacobian_sum_carrier (F : SelectedVFVolumeFamily C n a k) (H : SelectedVFVolumeFamily C n b k)
    (φ : SpecialTransformations.DefinableGeometry.Map X Y) (hφ : Function.Bijective φ)
    (hS : ∀ p : (selectedVolumeFamilySum F H).domain, p.val.1 ∈ X.carrier)
    (hF : ∀ p : F.domain, p.val.1 ∈ X.carrier) (hH : ∀ p : H.domain, p.val.1 ∈ X.carrier)
    (jS : SpecialTransformations.DefinableGeometry.Map (selectedVolumeFamilySum F H).domain
      (SpecialTransformations.DefinableGeometry.DefSet.univ (SpecialTransformations.Section4.rawVFSpace (M := M) 1)
        (C.base : Set M)))
    (jF : SpecialTransformations.DefinableGeometry.Map F.domain
      (SpecialTransformations.DefinableGeometry.DefSet.univ (SpecialTransformations.Section4.rawVFSpace (M := M) 1)
        (C.base : Set M)))
    (jH : SpecialTransformations.DefinableGeometry.Map H.domain
      (SpecialTransformations.DefinableGeometry.DefSet.univ (SpecialTransformations.Section4.rawVFSpace (M := M) 1)
        (C.base : Set M)))
    (q : Point (M := M) n ((1+(a+b))+(k+1))) :
    q ∈ ((selectedVolumeFamilySum F H).jacobianPushforwardWith φ hφ hS jS).domain.carrier ↔
      q ∈ (selectedVolumeFamilySum (F.jacobianPushforwardWith φ hφ hF jF)
        (H.jacobianPushforwardWith φ hφ hH jH)).domain.carrier := by
  rw [mem_selected_volume_family_sum]
  constructor
  · rintro ⟨p,rfl⟩
    rcases (mem_selected_volume_family_sum F H p.val).mp p.property with ⟨u,hu⟩ | ⟨v,hv⟩
    · left
      refine ⟨⟨_,⟨u,rfl⟩⟩,?_⟩
      have hp : p = ⟨sumLeftPoint F b u.val,(mem_selected_volume_family_sum F H _).mpr (Or.inl ⟨u,rfl⟩)⟩ :=
        Subtype.ext hu.symm
      subst hp
      rfl
    · right
      refine ⟨⟨_,⟨v,rfl⟩⟩,?_⟩
      have hp : p = ⟨sumRightPoint H a v.val,(mem_selected_volume_family_sum F H _).mpr (Or.inr ⟨v,rfl⟩)⟩ :=
        Subtype.ext hv.symm
      subst hp
      rfl
  · rintro (⟨⟨_,⟨u,rfl⟩⟩,rfl⟩ | ⟨⟨_,⟨v,rfl⟩⟩,rfl⟩)
    · exact ⟨⟨sumLeftPoint F b u.val,(mem_selected_volume_family_sum F H _).mpr (Or.inl ⟨u,rfl⟩)⟩,rfl⟩
    · exact ⟨⟨sumRightPoint H a v.val,(mem_selected_volume_family_sum F H _).mpr (Or.inr ⟨v,rfl⟩)⟩,rfl⟩

end IntegrationInACVF.Section7

namespace IntegrationInACVF.Section7.GammaFun
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n k : ℕ}
variable (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
variable (Ξ : Set (Values.Gamma (M := M))) (hΞ : Cardinal.mk Ξ < C.κ)

set_option quotPrecheck false
local notation "𝔅" => gammaNamedBase C Ξ
local notation "𝔇" => gammaNamedCodeContext C Ξ hΞ
local notation "𝔖" => ((gammaNamedCodeContext C Ξ hΞ).base : Set M)

theorem presentation_add_supported {X : GammaVFSet C Ξ hΞ n} (F H : Presentation C Ξ hΞ n k)
    (hF : F.SupportedIn C Ξ hΞ X) (hH : H.SupportedIn C Ξ hΞ X) : (F.add C Ξ hΞ H).SupportedIn C Ξ hΞ X :=
  selected_volume_family_sum_base F.family H.family (· ∈ X.set.carrier) hF hH

theorem presentation_zero_supported (X : GammaVFSet C Ξ hΞ n) :
    (Presentation.zero C Ξ hΞ n k).SupportedIn C Ξ hΞ X := fun p => p.property.elim

set_option maxHeartbeats 4000000 in
/-- **Additivity of Gamma Jacobian transforms** (almost everywhere). -/
theorem presentation_jacobian_add {X Y : GammaVFSet C Ξ hΞ n} (F H : Presentation C Ξ hΞ n k)
    (φ : GammaVFBijection C Ξ hΞ X Y) (hF : F.SupportedIn C Ξ hΞ X) (hH : H.SupportedIn C Ξ hΞ X) :
    AEEquivalent hc C Ξ hΞ ((F.add C Ξ hΞ H).jacobian hc C Ξ hΞ φ (presentation_add_supported C Ξ hΞ F H hF hH))
      ((F.jacobian hc C Ξ hΞ φ hF).add C Ξ hΞ (H.jacobian hc C Ξ hΞ φ hH)) := by
  let S := F.add C Ξ hΞ H
  have hS := presentation_add_supported C Ξ hΞ F H hF hH
  have h0 : SpecialTransformations.Section4.vfDim (SpecialTransformations.Section4.rawRVSpace (M := M) 1)
      (GammaVFSet.empty C Ξ hΞ n).set < n+1 :=
    (SpecialTransformations.DefinableGeometry.Dimension.dim_empty SpecialTransformations.Section4.rawVFSpace
      (SpecialTransformations.Section4.AuxiliaryCoordinates.space (SpecialTransformations.Section4.rawRVSpace (M := M) 1))
      (SpecialTransformations.Section4.AuxiliaryCoordinates.rv 0)).trans_lt (Nat.zero_lt_succ n)
  obtain ⟨E1,hE1,hg1⟩ := jacobian_ae_exceptional hc C Ξ hΞ S F φ hS hF (GammaVFSet.empty C Ξ hΞ n) h0
  obtain ⟨E2,hE2,hg2⟩ := jacobian_ae_exceptional hc C Ξ hΞ S H φ hS hH (GammaVFSet.empty C Ξ hΞ n) h0
  refine ⟨E1.union C Ξ hΞ E2,?_,?_⟩
  · change SpecialTransformations.Section4.vfDim _ (E1.set.union E2.set) < n+1
    rw [pure_vf_dim_union hc 𝔇]
    exact max_lt hE1 hE2
  intro y hy
  let JS := S.jacobian hc C Ξ hΞ φ hS
  let JF := F.jacobian hc C Ξ hΞ φ hF
  let JH := H.jacobian hc C Ξ hΞ φ hH
  let K := JF.add C Ξ hΞ JH
  let Cy := vfParameterVolumeContext 𝔇 y
  let By := rowGammaBase 𝔅 y
  have hcar := jacobian_sum_carrier F.family H.family φ.map φ.bijective hS hF hH
    (S.jacobianValue hc C Ξ hΞ φ hS) (F.jacobianValue hc C Ξ hΞ φ hF) (H.jacobianValue hc C Ξ hΞ φ hH)
  let f : SpecialTransformations.DefinableGeometry.Map (JS.family.rowInContext y).underlying.obj.domain
      (K.family.rowInContext y).underlying.obj.domain :=
    SpecialTransformations.DefinableGeometry.Map.inclusion (fun t ht => (hcar (y,t)).mp ht)
  have hf : Function.Bijective f :=
    ⟨fun s s' h => Subtype.ext (congrArg (fun w : (K.family.rowInContext y).underlying.obj.domain => w.val) h),
      fun t => ⟨⟨t.val,(hcar (y,t.val)).mpr t.property⟩,rfl⟩⟩
  have hCoord : ∀ s, (K.family.rowInContext y).underlying.obj.value (f s) =
      (JS.family.rowInContext y).underlying.obj.value s := fun _ => rfl
  have hForm : ∀ s, (K.family.rowInContext y).form.value (f s) = (JS.family.rowInContext y).form.value s := by
    intro s
    obtain ⟨p,hp⟩ := s.property
    have hyY : y ∈ Y.set.carrier := by
      have := (φ.map ⟨p.val.1,hS p⟩).property
      rw [show (φ.map ⟨p.val.1,hS p⟩).val = y from congrArg Prod.fst hp] at this
      exact this
    let y' : Y.set := ⟨y,hyY⟩
    have hpx : p.val.1 = (φ.map.inverse φ.bijective y').val := by
      have h1 : φ.map ⟨p.val.1,hS p⟩ = y' := Subtype.ext (congrArg Prod.fst hp)
      rw [← h1,SpecialTransformations.DefinableGeometry.Map.inverse_apply]
    have hyE1 : y ∉ E1.set.carrier := fun h => hy (Or.inl h)
    have hyE2 : y ∉ E2.set.carrier := fun h => hy (Or.inr h)
    obtain ⟨-,hgS,hgF⟩ := hg1 y' hyE1
    obtain ⟨-,-,hgH⟩ := hg2 y' hyE2
    have hjS : (S.jacobianValue hc C Ξ hΞ φ hS p).val 0 =
        (φ.pureJacobian hc C Ξ hΞ (pureVFEmptyGraphMap X.set ⟨p.val.1,hS p⟩)).val 0 := by
      by_contra hne
      exact hgS p hne hpx
    have hs : s = ⟨(y,s.val).2,s.property⟩ := rfl
    change (K.family.form.value ⟨(y,s.val),(hcar (y,s.val)).mp s.property⟩) =
      JS.family.form.value ⟨(y,s.val),s.property⟩
    have hJS : (⟨(y,s.val),s.property⟩ : JS.family.domain) =
        (mixedVFBaseMap φ.map S.family.domain hS).toImage p := Subtype.ext hp.symm
    rw [hJS]
    change _ = (jacobianTransportedForm (mixedVFBaseMap φ.map S.family.domain hS).toImage _
      (S.jacobianValue hc C Ξ hΞ φ hS) S.family.form).value _
    rw [jacobian_transported_form_value]
    rcases (mem_selected_volume_family_sum F.family H.family p.val).mp p.property with ⟨u,hu⟩ | ⟨v,hv⟩
    · have hux : u.val.1 = (φ.map.inverse φ.bijective y').val := (congrArg Prod.fst hu).trans hpx
      have hjF : (F.jacobianValue hc C Ξ hΞ φ hF u).val 0 =
          (φ.pureJacobian hc C Ξ hΞ (pureVFEmptyGraphMap X.set ⟨u.val.1,hF u⟩)).val 0 := by
        by_contra hne
        exact hgF u hne hux
      have hpu : p = ⟨sumLeftPoint F.family H.arity u.val,
          (mem_selected_volume_family_sum F.family H.family _).mpr (Or.inl ⟨u,rfl⟩)⟩ := Subtype.ext hu.symm
      have hxx : (⟨p.val.1,hS p⟩ : X.set) = ⟨u.val.1,hF u⟩ := Subtype.ext (congrArg Prod.fst hu).symm
      have hK : (⟨(y,s.val),(hcar (y,s.val)).mp s.property⟩ : K.family.domain) =
          ⟨sumLeftPoint JF.family H.arity ((mixedVFBaseMap φ.map F.family.domain hF).toImage u).val,
            (mem_selected_volume_family_sum JF.family JH.family _).mpr (Or.inl ⟨_,rfl⟩)⟩ := by
        apply Subtype.ext
        exact hp.symm.trans (Prod.ext (congrArg (fun z => (φ.map z).val) hxx) (congrArg Prod.snd hu).symm)
      rw [hK]
      refine (selected_volume_family_sum_density_left JF.family JH.family _ _).trans ?_
      change (jacobianTransportedForm (mixedVFBaseMap φ.map F.family.domain hF).toImage _
        (F.jacobianValue hc C Ξ hΞ φ hF) F.family.form).value _ = _
      rw [jacobian_transported_form_value]
      have hd := jacobian_value_density_congr (S.jacobianValue hc C Ξ hΞ φ hS) (F.jacobianValue hc C Ξ hΞ φ hF)
        p u (hjS.trans ((congrArg (fun z => (φ.pureJacobian hc C Ξ hΞ (pureVFEmptyGraphMap X.set z)).val 0) hxx).trans
          hjF.symm))
      rw [hd]
      congr 1
      rw [hpu]
      exact (selected_volume_family_sum_density_left F.family H.family u _).symm
    · have hvx : v.val.1 = (φ.map.inverse φ.bijective y').val := (congrArg Prod.fst hv).trans hpx
      have hjH : (H.jacobianValue hc C Ξ hΞ φ hH v).val 0 =
          (φ.pureJacobian hc C Ξ hΞ (pureVFEmptyGraphMap X.set ⟨v.val.1,hH v⟩)).val 0 := by
        by_contra hne
        exact hgH v hne hvx
      have hpv : p = ⟨sumRightPoint H.family F.arity v.val,
          (mem_selected_volume_family_sum F.family H.family _).mpr (Or.inr ⟨v,rfl⟩)⟩ := Subtype.ext hv.symm
      have hxx : (⟨p.val.1,hS p⟩ : X.set) = ⟨v.val.1,hH v⟩ := Subtype.ext (congrArg Prod.fst hv).symm
      have hK : (⟨(y,s.val),(hcar (y,s.val)).mp s.property⟩ : K.family.domain) =
          ⟨sumRightPoint JH.family F.arity ((mixedVFBaseMap φ.map H.family.domain hH).toImage v).val,
            (mem_selected_volume_family_sum JF.family JH.family _).mpr (Or.inr ⟨_,rfl⟩)⟩ := by
        apply Subtype.ext
        exact hp.symm.trans (Prod.ext (congrArg (fun z => (φ.map z).val) hxx) (congrArg Prod.snd hv).symm)
      rw [hK]
      refine (selected_volume_family_sum_density_right JF.family JH.family _ _).trans ?_
      change (jacobianTransportedForm (mixedVFBaseMap φ.map H.family.domain hH).toImage _
        (H.jacobianValue hc C Ξ hΞ φ hH) H.family.form).value _ = _
      rw [jacobian_transported_form_value]
      have hd := jacobian_value_density_congr (S.jacobianValue hc C Ξ hΞ φ hS) (H.jacobianValue hc C Ξ hΞ φ hH)
        p v (hjS.trans ((congrArg (fun z => (φ.pureJacobian hc C Ξ hΞ (pureVFEmptyGraphMap X.set z)).val 0) hxx).trans
          hjH.symm))
      rw [hd]
      congr 1
      rw [hpv]
      exact (selected_volume_family_sum_density_right F.family H.family v _).symm
  have hJ := JS.gamma.row hc y
  refine gammaVolumeBlowupClass_iso hc Cy By (RVVolumeIso.of_preserving_coordinates_full hc Cy
    (SpecialTransformations.Section4.rvFiniteIsoOfAmbient
      (SpecialTransformations.Section4.rvIsoOfVolumePreservingBijection f hf hCoord)) hCoord hForm) ?_
  exact gamma_volume_iso_of_full_map _ f (gamma_essential_volume_domain _ hJ.coordinates)
    (gamma_rv_coordinate_map hc _ id hJ.domain_graph (fun _ => rfl)) (fun _ => rfl)

end IntegrationInACVF.Section7.GammaFun
