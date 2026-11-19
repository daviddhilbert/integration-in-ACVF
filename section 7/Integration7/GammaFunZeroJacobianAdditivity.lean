import Integration7.GammaFunJacobianAdditivity

/-! Additivity of Gamma-named Jacobian transforms of weighted degree-zero presentations. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section9
open SpecialTransformations.Section5 (Point GammaSetDefinable GammaGraphDefinable gammaLogicInput carrier VF RV)
open IntegrationInACVF.Section5 IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {C : BaseContext M} {n a b : ℕ}

theorem zero_family_coprod_base (F : HK.ZeroVFVolumeFamily C (n+1) a) (H : HK.ZeroVFVolumeFamily C (n+1) b)
    (P : (Fin (n+1) → VFType (M := M)) → Prop) (hF : ∀ p : F.domain, P p.val.1) (hH : ∀ p : H.domain, P p.val.1)
    (p : (F.coprod H).domain) : P p.val.1 := by
  rcases vf_volume_coprod_cases F.fullVFObject H.fullVFObject p with ⟨u,rfl⟩ | ⟨v,rfl⟩
  · exact hF u
  · exact hH v

variable {X Y : SpecialTransformations.DefinableGeometry.DefSet
  (SpecialTransformations.Section4.rawVFSpace (M := M) (n+1)) (C.base : Set M)}

theorem zero_jacobian_sum_carrier (F : HK.ZeroVFVolumeFamily C (n+1) a) (H : HK.ZeroVFVolumeFamily C (n+1) b)
    (φ : SpecialTransformations.DefinableGeometry.Map X Y) (hφ : Function.Bijective φ)
    (hS : ∀ p : (F.coprod H).domain, p.val.1 ∈ X.carrier)
    (hF : ∀ p : F.domain, p.val.1 ∈ X.carrier) (hH : ∀ p : H.domain, p.val.1 ∈ X.carrier)
    (jS : SpecialTransformations.DefinableGeometry.Map (F.coprod H).domain
      (SpecialTransformations.DefinableGeometry.DefSet.univ (SpecialTransformations.Section4.rawVFSpace (M := M) 1)
        (C.base : Set M)))
    (jF : SpecialTransformations.DefinableGeometry.Map F.domain
      (SpecialTransformations.DefinableGeometry.DefSet.univ (SpecialTransformations.Section4.rawVFSpace (M := M) 1)
        (C.base : Set M)))
    (jH : SpecialTransformations.DefinableGeometry.Map H.domain
      (SpecialTransformations.DefinableGeometry.DefSet.univ (SpecialTransformations.Section4.rawVFSpace (M := M) 1)
        (C.base : Set M)))
    (q : Point (M := M) (n+1) (1+(a+b))) :
    q ∈ ((F.coprod H).jacobianPushforwardWith φ hφ hS jS).domain.carrier ↔
      q ∈ ((F.jacobianPushforwardWith φ hφ hF jF).coprod (H.jacobianPushforwardWith φ hφ hH jH)).domain.carrier := by
  constructor
  · rintro ⟨p,rfl⟩
    rcases vf_volume_coprod_cases F.fullVFObject H.fullVFObject p with ⟨u,rfl⟩ | ⟨v,rfl⟩
    · exact Or.inl ⟨⟨_,⟨u,rfl⟩⟩,rfl⟩
    · exact Or.inr ⟨⟨_,⟨v,rfl⟩⟩,rfl⟩
  · rintro (⟨⟨_,⟨u,rfl⟩⟩,rfl⟩ | ⟨⟨_,⟨v,rfl⟩⟩,rfl⟩)
    · exact ⟨vfVolumeCoprodLeftMap F.fullVFObject H.fullVFObject u,rfl⟩
    · exact ⟨vfVolumeCoprodRightMap F.fullVFObject H.fullVFObject v,rfl⟩

end IntegrationInACVF.Section7

namespace IntegrationInACVF.Section7.GammaFun
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n : ℕ}
variable (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
variable (Ξ : Set (Values.Gamma (M := M))) (hΞ : Cardinal.mk Ξ < C.κ)

set_option quotPrecheck false
local notation "𝔅" => gammaNamedBase C Ξ
local notation "𝔇" => gammaNamedCodeContext C Ξ hΞ
local notation "𝔖" => ((gammaNamedCodeContext C Ξ hΞ).base : Set M)

theorem zero_presentation_add_supported {X : GammaVFSet C Ξ hΞ n} (F H : ZeroPresentation C Ξ hΞ n)
    (hF : F.SupportedIn C Ξ hΞ X) (hH : H.SupportedIn C Ξ hΞ X) : (F.add C Ξ hΞ H).SupportedIn C Ξ hΞ X :=
  zero_family_coprod_base F.family H.family (· ∈ X.set.carrier) hF hH

theorem zero_presentation_zero_supported (X : GammaVFSet C Ξ hΞ n) :
    (ZeroPresentation.zero C Ξ hΞ n).SupportedIn C Ξ hΞ X := fun p => p.property.elim

set_option maxHeartbeats 4000000 in
/-- **Additivity of zero-degree Gamma Jacobian transforms** (almost everywhere). -/
theorem zero_presentation_jacobian_add {X Y : GammaVFSet C Ξ hΞ n} (F H : ZeroPresentation C Ξ hΞ n)
    (φ : GammaVFBijection C Ξ hΞ X Y) (hF : F.SupportedIn C Ξ hΞ X) (hH : H.SupportedIn C Ξ hΞ X) :
    ZeroAEEquivalent C Ξ hΞ
      ((F.add C Ξ hΞ H).jacobian hc C Ξ hΞ φ (zero_presentation_add_supported C Ξ hΞ F H hF hH))
      ((F.jacobian hc C Ξ hΞ φ hF).add C Ξ hΞ (H.jacobian hc C Ξ hΞ φ hH)) := by
  let S := F.add C Ξ hΞ H
  have hS := zero_presentation_add_supported C Ξ hΞ F H hF hH
  have h0 : SpecialTransformations.Section4.vfDim (SpecialTransformations.Section4.rawRVSpace (M := M) 1)
      (GammaVFSet.empty C Ξ hΞ n).set < n+1 :=
    (SpecialTransformations.DefinableGeometry.Dimension.dim_empty SpecialTransformations.Section4.rawVFSpace
      (SpecialTransformations.Section4.AuxiliaryCoordinates.space (SpecialTransformations.Section4.rawRVSpace (M := M) 1))
      (SpecialTransformations.Section4.AuxiliaryCoordinates.rv 0)).trans_lt (Nat.zero_lt_succ n)
  obtain ⟨E1,hE1,hg1⟩ := domain_jacobian_ae_exceptional hc C Ξ hΞ φ S.family.domain F.family.domain
    S.gamma.domain F.gamma.domain hS hF (S.jacobianValue hc C Ξ hΞ φ hS) (F.jacobianValue hc C Ξ hΞ φ hF)
    (S.jacobianValue_gamma hc C Ξ hΞ φ hS) (F.jacobianValue_gamma hc C Ξ hΞ φ hF)
    (S.jacobianValue_spec hc C Ξ hΞ φ hS) (F.jacobianValue_spec hc C Ξ hΞ φ hF) (GammaVFSet.empty C Ξ hΞ n) h0
  obtain ⟨E2,hE2,hg2⟩ := domain_jacobian_ae_exceptional hc C Ξ hΞ φ S.family.domain H.family.domain
    S.gamma.domain H.gamma.domain hS hH (S.jacobianValue hc C Ξ hΞ φ hS) (H.jacobianValue hc C Ξ hΞ φ hH)
    (S.jacobianValue_gamma hc C Ξ hΞ φ hS) (H.jacobianValue_gamma hc C Ξ hΞ φ hH)
    (S.jacobianValue_spec hc C Ξ hΞ φ hS) (H.jacobianValue_spec hc C Ξ hΞ φ hH) (GammaVFSet.empty C Ξ hΞ n) h0
  refine ⟨E1.union C Ξ hΞ E2,?_,?_⟩
  · change SpecialTransformations.Section4.vfDim _ (E1.set.union E2.set) < n+1
    rw [pure_vf_dim_union hc 𝔇]
    exact max_lt hE1 hE2
  intro y hy
  let JS := S.jacobian hc C Ξ hΞ φ hS
  let JF := F.jacobian hc C Ξ hΞ φ hF
  let JH := H.jacobian hc C Ξ hΞ φ hH
  let K := JF.add C Ξ hΞ JH
  let By := rowGammaBase 𝔅 y
  have hcar := zero_jacobian_sum_carrier F.family H.family φ.map φ.bijective hS hF hH
    (S.jacobianValue hc C Ξ hΞ φ hS) (F.jacobianValue hc C Ξ hΞ φ hF) (H.jacobianValue hc C Ξ hΞ φ hH)
  let f : SpecialTransformations.DefinableGeometry.Map (JS.family.rowInContext y).underlying.obj.domain
      (K.family.rowInContext y).underlying.obj.domain :=
    SpecialTransformations.DefinableGeometry.Map.inclusion (fun t ht => (hcar (y,t)).mp ht)
  have hf : Function.Bijective f :=
    ⟨fun s s' h => Subtype.ext (congrArg (fun w : (K.family.rowInContext y).underlying.obj.domain => w.val) h),
      fun t => ⟨⟨t.val,(hcar (y,t.val)).mpr t.property⟩,rfl⟩⟩
  let e := finiteIsoOfNondegenerateBijection f hf (fun _ i => i.elim0) (fun _ i => i.elim0)
  have hForm : ∀ s, (JS.family.rowInContext y).form.value s = (K.family.rowInContext y).form.value (finiteIsoMap e s) := by
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
    change JS.family.form.value ⟨(y,s.val),s.property⟩ =
      K.family.form.value ⟨(y,s.val),(hcar (y,s.val)).mp s.property⟩
    have hJS : (⟨(y,s.val),s.property⟩ : JS.family.domain) =
        (mixedVFBaseMap φ.map S.family.domain hS).toImage p := Subtype.ext hp.symm
    rw [hJS]
    change (jacobianTransportedForm (mixedVFBaseMap φ.map S.family.domain hS).toImage _
      (S.jacobianValue hc C Ξ hΞ φ hS) S.family.form).value _ = _
    rw [jacobian_transported_form_value]
    rcases vf_volume_coprod_cases F.family.fullVFObject H.family.fullVFObject p with ⟨u,rfl⟩ | ⟨v,rfl⟩
    · have hux : u.val.1 = (φ.map.inverse φ.bijective y').val := hpx
      have hjF : (F.jacobianValue hc C Ξ hΞ φ hF u).val 0 =
          (φ.pureJacobian hc C Ξ hΞ (pureVFEmptyGraphMap X.set ⟨u.val.1,hF u⟩)).val 0 := by
        by_contra hne
        exact hgF u hne hux
      have hK : (⟨(y,s.val),(hcar (y,s.val)).mp s.property⟩ : K.family.domain) =
          vfVolumeCoprodLeftMap JF.family.fullVFObject JH.family.fullVFObject
            ((mixedVFBaseMap φ.map F.family.domain hF).toImage u) := Subtype.ext hp.symm
      rw [hK]
      refine Eq.trans ?_ (vf_volume_coprod_density_left JF.family.fullVFObject JH.family.fullVFObject _).symm
      change _ = (jacobianTransportedForm (mixedVFBaseMap φ.map F.family.domain hF).toImage _
        (F.jacobianValue hc C Ξ hΞ φ hF) F.family.form).value _
      rw [jacobian_transported_form_value]
      have hd := jacobian_value_density_congr (S.jacobianValue hc C Ξ hΞ φ hS) (F.jacobianValue hc C Ξ hΞ φ hF)
        _ u (hjS.trans hjF.symm)
      rw [hd]
      congr 1
      exact vf_volume_coprod_density_left F.family.fullVFObject H.family.fullVFObject u
    · have hvx : v.val.1 = (φ.map.inverse φ.bijective y').val := hpx
      have hjH : (H.jacobianValue hc C Ξ hΞ φ hH v).val 0 =
          (φ.pureJacobian hc C Ξ hΞ (pureVFEmptyGraphMap X.set ⟨v.val.1,hH v⟩)).val 0 := by
        by_contra hne
        exact hgH v hne hvx
      have hK : (⟨(y,s.val),(hcar (y,s.val)).mp s.property⟩ : K.family.domain) =
          vfVolumeCoprodRightMap JF.family.fullVFObject JH.family.fullVFObject
            ((mixedVFBaseMap φ.map H.family.domain hH).toImage v) := Subtype.ext hp.symm
      rw [hK]
      refine Eq.trans ?_ (vf_volume_coprod_density_right JF.family.fullVFObject JH.family.fullVFObject _).symm
      change _ = (jacobianTransportedForm (mixedVFBaseMap φ.map H.family.domain hH).toImage _
        (H.jacobianValue hc C Ξ hΞ φ hH) H.family.form).value _
      rw [jacobian_transported_form_value]
      have hd := jacobian_value_density_congr (S.jacobianValue hc C Ξ hΞ φ hS) (H.jacobianValue hc C Ξ hΞ φ hH)
        _ v (hjS.trans hjH.symm)
      rw [hd]
      congr 1
      exact vf_volume_coprod_density_right F.family.fullVFObject H.family.fullVFObject v
  have hJ := JS.gamma.row y
  refine HK.gammaZeroRVClass_iso ⟨e,hForm⟩ ?_
  apply SpecialTransformations.Section5.GammaGraphDefinable.congr (gamma_vf_identity_graph _ hJ.domain)
  intro p q
  constructor
  · rintro ⟨hp,rfl⟩
    exact ⟨⟨p.2,hp⟩,rfl,rfl⟩
  · rintro ⟨u,hu,hv⟩
    refine ⟨?_,?_⟩
    · change p.2 ∈ (JS.family.rowInContext y).underlying.obj.domain.carrier
      rw [← hu]
      exact u.property
    · refine Prod.ext (funext (fun i => Fin.elim0 i)) ?_
      rw [← hu]
      exact hv

end IntegrationInACVF.Section7.GammaFun
