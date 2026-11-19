import Integration7.GammaFunZeroHead
import Integration7.HKZeroJacobianAlmostEverywhere
import Integration7.HKSupportedZeroFunctionJacobians
import Integration7.HKZeroVolumeParameterDescent
import Integration7.HKZeroDefinableDensityRescaling

/-! Gamma Jacobian transforms of weighted degree-zero functions: Gamma certificate, Gamma
change of variables, and invariance under almost-everywhere equivalence. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section9
open SpecialTransformations.Section4 (vfValues)
open SpecialTransformations.Section5 (Point GammaSetDefinable GammaGraphDefinable gammaLogicInput carrier)
open IntegrationInACVF.Section5 IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {C : BaseContext M} {G : Base (M := M)} {n a b : ℕ}

/-- Jacobian pushforward of a zero family along a VF bijection with a prescribed Jacobian value map. -/
def HK.ZeroVFVolumeFamily.jacobianPushforwardWith
    {X Y : SpecialTransformations.DefinableGeometry.DefSet
      (SpecialTransformations.Section4.rawVFSpace (M := M) n) (C.base : Set M)}
    (F : HK.ZeroVFVolumeFamily C n a) (φ : SpecialTransformations.DefinableGeometry.Map X Y)
    (hφ : Function.Bijective φ) (hF : ∀ p : F.domain, p.val.1 ∈ X.carrier)
    (j : SpecialTransformations.DefinableGeometry.Map F.domain
      (SpecialTransformations.DefinableGeometry.DefSet.univ (SpecialTransformations.Section4.rawVFSpace (M := M) 1)
        (C.base : Set M))) : HK.ZeroVFVolumeFamily C n a where
  domain := (mixedVFBaseMap φ F.domain hF).image
  finite_labels := (HK.ZeroVFVolumeFamily.pushforwardBase F φ hφ hF).finite_labels
  form := jacobianTransportedForm (mixedVFBaseMap φ F.domain hF).toImage
    (mixed_vf_base_map_to_image_bijective φ hφ.1 F.domain hF) j F.form

end IntegrationInACVF.Section7

namespace IntegrationInACVF.Section7.GammaFun
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n a b k : ℕ}
variable (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
variable (Ξ : Set (Values.Gamma (M := M))) (hΞ : Cardinal.mk Ξ < C.κ)
variable (hGenerated : VFGammaGeneratedBase (gammaNamedBase C Ξ))

set_option quotPrecheck false
local notation "𝔅" => gammaNamedBase C Ξ
local notation "𝔇" => gammaNamedCodeContext C Ξ hΞ
local notation "𝔖" => ((gammaNamedCodeContext C Ξ hΞ).base : Set M)

/-- A zero presentation is supported in a Gamma VF set when its VF base lies in it. -/
def ZeroPresentation.SupportedIn (F : ZeroPresentation C Ξ hΞ n) (X : GammaVFSet C Ξ hΞ n) : Prop :=
  ∀ p : F.family.domain, p.val.1 ∈ X.set.carrier

include hc in
theorem zero_jacobian_value_exists {X Y : GammaVFSet C Ξ hΞ n} (F : ZeroPresentation C Ξ hΞ n)
    (φ : GammaVFBijection C Ξ hΞ X Y) (hF : F.SupportedIn C Ξ hΞ X) :
    ∃ j : SpecialTransformations.DefinableGeometry.Map F.family.domain
        (SpecialTransformations.DefinableGeometry.DefSet.univ (SpecialTransformations.Section4.rawVFSpace (M := M) 1) 𝔖),
      GammaGraphDefinable 𝔅 (fun (p : Point (M := M) (n+1) F.arity) (z : Point (M := M) 1 0) =>
        ∃ u : F.family.domain, u.val = p ∧ (j u).val = z.1) ∧
      IsJacobianValueMap (mixedVFBaseMap φ.map F.family.domain hF).toImage j :=
  gamma_exists_totalMixedJacobianMap hc (Nat.zero_lt_succ n) _
    (gamma_mixed_vf_base_map_graph φ.map φ.gamma _ F.gamma.domain hF)

def ZeroPresentation.jacobianValue {X Y : GammaVFSet C Ξ hΞ n} (F : ZeroPresentation C Ξ hΞ n)
    (φ : GammaVFBijection C Ξ hΞ X Y) (hF : F.SupportedIn C Ξ hΞ X) :=
  Classical.choose (zero_jacobian_value_exists hc C Ξ hΞ F φ hF)

theorem ZeroPresentation.jacobianValue_gamma {X Y : GammaVFSet C Ξ hΞ n} (F : ZeroPresentation C Ξ hΞ n)
    (φ : GammaVFBijection C Ξ hΞ X Y) (hF : F.SupportedIn C Ξ hΞ X) :
    GammaGraphDefinable 𝔅 (fun (p : Point (M := M) (n+1) F.arity) (z : Point (M := M) 1 0) =>
      ∃ u : F.family.domain, u.val = p ∧ (F.jacobianValue hc C Ξ hΞ φ hF u).val = z.1) :=
  (Classical.choose_spec (zero_jacobian_value_exists hc C Ξ hΞ F φ hF)).1

theorem ZeroPresentation.jacobianValue_spec {X Y : GammaVFSet C Ξ hΞ n} (F : ZeroPresentation C Ξ hΞ n)
    (φ : GammaVFBijection C Ξ hΞ X Y) (hF : F.SupportedIn C Ξ hΞ X) :
    IsJacobianValueMap (mixedVFBaseMap φ.map F.family.domain hF).toImage (F.jacobianValue hc C Ξ hΞ φ hF) :=
  (Classical.choose_spec (zero_jacobian_value_exists hc C Ξ hΞ F φ hF)).2

/-- **The Gamma Jacobian transform of a supported zero presentation.** -/
def ZeroPresentation.jacobian {X Y : GammaVFSet C Ξ hΞ n} (F : ZeroPresentation C Ξ hΞ n)
    (φ : GammaVFBijection C Ξ hΞ X Y) (hF : F.SupportedIn C Ξ hΞ X) : ZeroPresentation C Ξ hΞ n where
  arity := F.arity
  family := F.family.jacobianPushforwardWith φ.map φ.bijective hF (F.jacobianValue hc C Ξ hΞ φ hF)
  gamma := by
    have hfΓ := gamma_mixed_vf_base_map_graph φ.map φ.gamma _ F.gamma.domain hF
    refine ⟨?_,?_⟩
    · convert (gammaLogicInput 𝔅).image_graph hfΓ using 1
      ext q
      constructor
      · rintro ⟨u,hu⟩
        exact ⟨u.val,u,rfl,hu⟩
      · rintro ⟨_,u,rfl,hu⟩
        exact ⟨u,hu⟩
    · exact density_graph_of_volume_form_graph _
        (gamma_jacobian_transported_form_graph hc _ _ hfΓ _ (F.jacobianValue_gamma hc C Ξ hΞ φ hF) F.family.form
          (volume_form_graph_of_density_graph F.family.form F.gamma.densityGraph))

theorem zero_presentation_jacobian_supported {X Y : GammaVFSet C Ξ hΞ n} (F : ZeroPresentation C Ξ hΞ n)
    (φ : GammaVFBijection C Ξ hΞ X Y) (hF : F.SupportedIn C Ξ hΞ X) :
    (F.jacobian hc C Ξ hΞ φ hF).SupportedIn C Ξ hΞ Y := by
  rintro ⟨q,u,hu⟩
  have h := congrArg Prod.fst hu
  change (φ.map ⟨u.val.1,hF u⟩).val = q.1 at h
  rw [← h]
  exact (φ.map ⟨u.val.1,hF u⟩).property

variable (γ : Values.Gamma (M := M)) (hγ : γ ∈ Ξ) (hγ1 : 1 < γ)

include hγ hγ1 in
/-- **Gamma change of variables for weighted degree-zero presentations.** -/
theorem zero_presentation_jacobian_integral {X Y : GammaVFSet C Ξ hΞ n} (F : ZeroPresentation C Ξ hΞ n)
    (φ : GammaVFBijection C Ξ hΞ X Y) (hF : F.SupportedIn C Ξ hΞ X) :
    (F.jacobian hc C Ξ hΞ φ hF).integral hc C Ξ hΞ hGenerated γ hγ hγ1 = F.integral hc C Ξ hΞ hGenerated γ hγ hγ1 := by
  let f := (mixedVFBaseMap φ.map F.family.domain hF).toImage
  have hfΓ := gamma_mixed_vf_base_map_graph φ.map φ.gamma _ F.gamma.domain hF
  let b : VFVolumeBijection F.family.fullVFObject (F.jacobian hc C Ξ hΞ φ hF).family.fullVFObject :=
    ⟨f,mixed_vf_base_map_to_image_bijective φ.map φ.bijective.1 F.family.domain hF,
      preserves_jacobian_transported_form hc 𝔇 (Nat.zero_lt_succ n) f _ _ (F.jacobianValue_spec hc C Ξ hΞ φ hF)
        F.family.form⟩
  have hb : (VFVolumeIso.of_bijection b).GammaDefinable 𝔅 :=
    ⟨F.gamma.domain,(F.jacobian hc C Ξ hΞ φ hF).gamma.domain,hfΓ⟩
  apply (congrArg (gammaNamedIntegrationEquiv hc C Ξ hΞ hGenerated γ hγ hγ1 n) ?_).symm
  exact (gammaVFVolumeClass_eq_iff hc 𝔇 𝔅).mpr ⟨_,hb⟩

/-- The Jacobian discrepancy locus of an arbitrary Gamma domain with a Gamma value map. -/
theorem domain_jacobian_discrepancy_gamma {X Y : GammaVFSet C Ξ hΞ n} (φ : GammaVFBijection C Ξ hΞ X Y) {a : ℕ}
    (U : SpecialTransformations.DefinableGeometry.DefSet (SpecialTransformations.Section4.rawMixedSpace (M := M) (n+1) a) 𝔖)
    (hU : GammaSetDefinable 𝔅 U.carrier) (hUX : ∀ p : U, p.val.1 ∈ X.set.carrier)
    (j : SpecialTransformations.DefinableGeometry.Map U
      (SpecialTransformations.DefinableGeometry.DefSet.univ (SpecialTransformations.Section4.rawVFSpace (M := M) 1) 𝔖))
    (hj : GammaGraphDefinable 𝔅 (fun (p : Point (M := M) (n+1) a) (z : Point (M := M) 1 0) =>
      ∃ u : U, u.val = p ∧ (j u).val = z.1)) :
    GammaSetDefinable 𝔅 {q : Point (M := M) (n+1) 0 | ∃ u : U, u.val.1 = q.1 ∧
      (j u).val 0 ≠ (φ.pureJacobian hc C Ξ hΞ (pureVFEmptyGraphMap X.set ⟨u.val.1,hUX u⟩)).val 0} := by
  let L := gammaLogicInput 𝔅
  have hJX := φ.pureJacobian_gamma hc C Ξ hΞ
  have hJX' := hJX.preimage_maps
    (mixedCoordinatePointMap (id : Fin (n+1) → Fin (n+1)) (Fin.elim0 : Fin 0 → Fin a) (gammaNamedBase C Ξ).real)
    (mixedCoordinatePointMap (id : Fin 1 → Fin 1) (id : Fin 0 → Fin 0) (gammaNamedBase C Ξ).real)
  have hAgree := L.image_graph (L.swap_graph (hj.inter hJX'))
  have hDisc := L.sdiff hU hAgree
  have hBad := L.image_real
    (mixedCoordinatePointMap (id : Fin (n+1) → Fin (n+1)) (Fin.elim0 : Fin 0 → Fin a) (gammaNamedBase C Ξ).real) hDisc
  convert hBad using 1
  ext q
  constructor
  · rintro ⟨u,hu,hne⟩
    refine ⟨⟨u.val,Set.mem_univ _⟩,⟨u.property,?_⟩,?_⟩
    · rintro ⟨z,⟨u',hu',hz⟩,⟨v,hv,hvz⟩⟩
      have hu'' : u' = u := Subtype.ext hu'
      subst hu''
      apply hne
      have hv' : v = pureVFEmptyGraphMap X.set ⟨u'.val.1,hUX u'⟩ := by
        apply Subtype.ext
        rw [hv,pure_vf_empty_graph_map_value,mixedCoordinatePointMap_value]
        exact Prod.ext rfl (funext fun i => i.elim0)
      rw [← hv']
      exact (congrFun hz 0).trans (congrFun hvz 0).symm
    · exact Prod.ext hu (funext fun i => i.elim0)
  · rintro ⟨p,⟨hp,hna⟩,hq⟩
    let u : U := ⟨p.val,hp⟩
    refine ⟨u,congrArg Prod.fst hq,?_⟩
    intro he
    apply hna
    refine ⟨((fun _ => (j u).val 0),Fin.elim0),⟨u,rfl,?_⟩,
      ⟨pureVFEmptyGraphMap X.set ⟨u.val.1,hUX u⟩,?_,?_⟩⟩
    · funext i
      have hi : i = 0 := Subsingleton.elim i 0
      subst hi
      rfl
    · rw [pure_vf_empty_graph_map_value,mixedCoordinatePointMap_value]
      exact Prod.ext rfl (funext fun i => i.elim0)
    · funext i
      have hi : i = 0 := Subsingleton.elim i 0
      subst hi
      exact he.symm

set_option maxHeartbeats 2400000 in
/-- **The exceptional set of a Jacobian comparison of two Gamma domains.** -/
theorem domain_jacobian_ae_exceptional {X Y : GammaVFSet C Ξ hΞ n} (φ : GammaVFBijection C Ξ hΞ X Y) {a b : ℕ}
    (U : SpecialTransformations.DefinableGeometry.DefSet (SpecialTransformations.Section4.rawMixedSpace (M := M) (n+1) a) 𝔖)
    (V : SpecialTransformations.DefinableGeometry.DefSet (SpecialTransformations.Section4.rawMixedSpace (M := M) (n+1) b) 𝔖)
    (hU : GammaSetDefinable 𝔅 U.carrier) (hV : GammaSetDefinable 𝔅 V.carrier)
    (hUX : ∀ p : U, p.val.1 ∈ X.set.carrier) (hVX : ∀ p : V, p.val.1 ∈ X.set.carrier)
    (jU : SpecialTransformations.DefinableGeometry.Map U
      (SpecialTransformations.DefinableGeometry.DefSet.univ (SpecialTransformations.Section4.rawVFSpace (M := M) 1) 𝔖))
    (jV : SpecialTransformations.DefinableGeometry.Map V
      (SpecialTransformations.DefinableGeometry.DefSet.univ (SpecialTransformations.Section4.rawVFSpace (M := M) 1) 𝔖))
    (hjUΓ : GammaGraphDefinable 𝔅 (fun (p : Point (M := M) (n+1) a) (z : Point (M := M) 1 0) =>
      ∃ u : U, u.val = p ∧ (jU u).val = z.1))
    (hjVΓ : GammaGraphDefinable 𝔅 (fun (p : Point (M := M) (n+1) b) (z : Point (M := M) 1 0) =>
      ∃ u : V, u.val = p ∧ (jV u).val = z.1))
    (hjU : IsJacobianValueMap (mixedVFBaseMap φ.map U hUX).toImage jU)
    (hjV : IsJacobianValueMap (mixedVFBaseMap φ.map V hVX).toImage jV)
    (E : GammaVFSet C Ξ hΞ n)
    (hE : SpecialTransformations.Section4.vfDim (SpecialTransformations.Section4.rawRVSpace (M := M) 1) E.set < n+1) :
    ∃ E' : GammaVFSet C Ξ hΞ n,
      SpecialTransformations.Section4.vfDim (SpecialTransformations.Section4.rawRVSpace (M := M) 1) E'.set < n+1 ∧
      ∀ y : Y.set, y.val ∉ E'.set.carrier →
        (φ.map.inverse φ.bijective y).val ∉ E.set.carrier ∧
        (∀ u : U, (jU u).val 0 ≠ (φ.pureJacobian hc C Ξ hΞ (pureVFEmptyGraphMap X.set ⟨u.val.1,hUX u⟩)).val 0 →
            u.val.1 ≠ (φ.map.inverse φ.bijective y).val) ∧
        (∀ u : V, (jV u).val 0 ≠ (φ.pureJacobian hc C Ξ hΞ (pureVFEmptyGraphMap X.set ⟨u.val.1,hVX u⟩)).val 0 →
            u.val.1 ≠ (φ.map.inverse φ.bijective y).val) := by
  let L := gammaLogicInput 𝔅
  let BadPts : Set (Point (M := M) (n+1) 0) := {q | q.1 ∈ X.set.carrier} ∩
    ({q | q.1 ∈ E.set.carrier} ∪
      ({q | ∃ u : U, u.val.1 = q.1 ∧ (jU u).val 0 ≠
          (φ.pureJacobian hc C Ξ hΞ (pureVFEmptyGraphMap X.set ⟨u.val.1,hUX u⟩)).val 0} ∪
       {q | ∃ u : V, u.val.1 = q.1 ∧ (jV u).val 0 ≠
          (φ.pureJacobian hc C Ξ hΞ (pureVFEmptyGraphMap X.set ⟨u.val.1,hVX u⟩)).val 0}))
  have hBad : GammaSetDefinable 𝔅 BadPts := L.inter X.gamma (L.union E.gamma
    (L.union (domain_jacobian_discrepancy_gamma hc C Ξ hΞ φ U hU hUX jU hjUΓ)
      (domain_jacobian_discrepancy_gamma hc C Ξ hΞ φ V hV hVX jV hjVΓ)))
  let R : Set (Fin (n+1) → M) := (fun q => fun j => (q.1 j).val) '' BadPts
  have hR : DefinableOverBase 𝔅 (fun _ : Fin (n+1) => SortTag.vf) R := by
    have h := hBad
    unfold SpecialTransformations.Section5.GammaSetDefinable at h
    rw [gammaPointSort_vf_zero] at h
    convert h using 1
    ext z
    constructor
    · rintro ⟨q,hq,rfl⟩
      exact ⟨q,hq,gammaPointCode_vf_zero q⟩
    · rintro ⟨q,hq,rfl⟩
      exact ⟨q,hq,(gammaPointCode_vf_zero q).symm⟩
  let D := pureVFFormulaLocus R (hR.common_names.mono (gamma_named_code_context_names C Ξ hΞ))
  have hmemD : ∀ x : Fin (n+1) → VFType (M := M), x ∈ D.carrier ↔ (x,Fin.elim0) ∈ BadPts := by
    intro x
    constructor
    · rintro ⟨q,hq,he⟩
      have hx : q.1 = x := SpecialTransformations.Section4.vfValues_injective he
      have hq' : q = (x,Fin.elim0) := Prod.ext hx (funext fun i => i.elim0)
      rw [← hq']
      exact hq
    · intro hx
      exact ⟨(x,Fin.elim0),hx,rfl⟩
  have hDX : D.carrier ⊆ X.set.carrier := fun x hx => ((hmemD x).mp hx).1
  have hDdim : SpecialTransformations.Section4.vfDim (SpecialTransformations.Section4.rawRVSpace (M := M) 1) D < n+1 := by
    apply pure_vf_dimension_lt_of_no_independent hc 𝔇 (Nat.zero_lt_succ n) D
    intro p hp
    obtain ⟨_,hcase⟩ := (hmemD p.val).mp p.property
    rcases hcase with hE' | ⟨u,hu,hne⟩ | ⟨u,hu,hne⟩
    · exact pure_vf_small_has_no_independent hc E.set hE ⟨p.val,hE'⟩ hp
    · apply hne
      apply jacobian_values_agree_at_generic hc 𝔇 (Nat.zero_lt_succ n) φ.map U hUX _ hjU _
        (φ.pureJacobian_spec hc C Ξ hΞ) u
      rw [hu]
      exact hp
    · apply hne
      apply jacobian_values_agree_at_generic hc 𝔇 (Nat.zero_lt_succ n) φ.map V hVX _ hjV _
        (φ.pureJacobian_spec hc C Ξ hΞ) u
      rw [hu]
      exact hp
  let f := φ.map.restrict (A' := D) hDX
  have hf : Function.Bijective f.toImage := by
    constructor
    · intro u v huv
      apply Subtype.ext
      have hval : (φ.map ⟨u.val,hDX u.property⟩).val = (φ.map ⟨v.val,hDX v.property⟩).val :=
        congrArg (fun w : f.image => w.val) huv
      exact congrArg (fun z : X.set => z.val) (φ.bijective.1 (Subtype.ext hval))
    · rintro ⟨v,u,hu⟩
      exact ⟨u,Subtype.ext hu⟩
  have hDpts := HK.gamma_pure_vf_locus hR
  let E' : GammaVFSet C Ξ hΞ n := ⟨f.image,by
    have h := L.image_graph (L.restrict_graph hDpts φ.gamma)
    convert h using 1
    ext q
    constructor
    · rintro ⟨u,hu⟩
      refine ⟨(u.val,Fin.elim0),?_,⟨⟨u.val,hDX u.property⟩,rfl,hu⟩⟩
      exact u.property
    · rintro ⟨p,hp,⟨w,hw,hwq⟩⟩
      have hpD : p.1 ∈ D.carrier := hp
      refine ⟨⟨p.1,hpD⟩,?_⟩
      have hw' : w = ⟨p.1,hDX hpD⟩ := Subtype.ext hw
      rw [← hwq,hw']
      rfl⟩
  refine ⟨E',?_,?_⟩
  · change SpecialTransformations.Section4.vfDim _ f.image < n+1
    rw [pure_vf_dimension_eq_of_bijective f.toImage hf]
    exact hDdim
  · intro y hy
    let x := φ.map.inverse φ.bijective y
    have hxD : x.val ∉ D.carrier := by
      intro hx
      apply hy
      refine ⟨⟨x.val,hx⟩,?_⟩
      change (φ.map ⟨x.val,hDX hx⟩).val = y.val
      rw [show (⟨x.val,hDX hx⟩ : X.set) = x from rfl, SpecialTransformations.DefinableGeometry.Map.apply_inverse]
    have hnot : (x.val,Fin.elim0) ∉ BadPts := fun h => hxD ((hmemD x.val).mpr h)
    refine ⟨fun hE' => hnot ⟨x.property,Or.inl hE'⟩,?_,?_⟩
    · intro u hne hu
      exact hnot ⟨x.property,Or.inr (Or.inl ⟨u,hu,hne⟩)⟩
    · intro u hne hu
      exact hnot ⟨x.property,Or.inr (Or.inr ⟨u,hu,hne⟩)⟩

set_option maxHeartbeats 4000000 in
/-- **Gamma Jacobian transforms of weighted degree-zero functions respect almost-everywhere equivalence.** -/
theorem zero_presentation_jacobian_ae {X Y : GammaVFSet C Ξ hΞ n} (F H : ZeroPresentation C Ξ hΞ n)
    (φ : GammaVFBijection C Ξ hΞ X Y) (hF : F.SupportedIn C Ξ hΞ X) (hH : H.SupportedIn C Ξ hΞ X)
    (h : ZeroAEEquivalent C Ξ hΞ F H) :
    ZeroAEEquivalent C Ξ hΞ (F.jacobian hc C Ξ hΞ φ hF) (H.jacobian hc C Ξ hΞ φ hH) := by
  obtain ⟨E,hE,hRows⟩ := h
  obtain ⟨E',hE',hgood⟩ := domain_jacobian_ae_exceptional hc C Ξ hΞ φ F.family.domain H.family.domain
    F.gamma.domain H.gamma.domain hF hH (F.jacobianValue hc C Ξ hΞ φ hF) (H.jacobianValue hc C Ξ hΞ φ hH)
    (F.jacobianValue_gamma hc C Ξ hΞ φ hF) (H.jacobianValue_gamma hc C Ξ hΞ φ hH)
    (F.jacobianValue_spec hc C Ξ hΞ φ hF) (H.jacobianValue_spec hc C Ξ hΞ φ hH) E hE
  refine ⟨E',hE',?_⟩
  intro y hy
  let Cy := vfParameterVolumeContext 𝔇 y
  let By := rowGammaBase 𝔅 y
  by_cases hyY : y ∈ Y.set.carrier
  swap
  · have hF0 : ((F.jacobian hc C Ξ hΞ φ hF).family.rowInContext y).underlying.obj.domain.carrier = ∅ :=
      HK.zero_jacobian_row_empty_outside 𝔇 F.family φ.map φ.bijective hF y hyY
    have hH0 : ((H.jacobian hc C Ξ hΞ φ hH).family.rowInContext y).underlying.obj.domain.carrier = ∅ :=
      HK.zero_jacobian_row_empty_outside 𝔇 H.family φ.map φ.bijective hH y hyY
    let f : SpecialTransformations.DefinableGeometry.Map
        ((F.jacobian hc C Ξ hΞ φ hF).family.rowInContext y).underlying.obj.domain
        ((H.jacobian hc C Ξ hΞ φ hH).family.rowInContext y).underlying.obj.domain :=
      SpecialTransformations.DefinableGeometry.Map.fromEmpty hF0 _
    refine Quotient.sound ⟨HK.ZeroRVVolumeIso.ofBijection f
      (SpecialTransformations.DefinableGeometry.Map.bijective_of_empty f hF0 hH0) (fun u => (hF0.le u.property).elim),?_⟩
    apply SpecialTransformations.Section5.GammaGraphDefinable.congr (FiniteRV.gamma_empty_graph (B := By) _ _)
    intro p q
    constructor
    · exact False.elim
    · rintro ⟨u,_,_⟩
      exact (hF0.le u.property).elim
  let y' : Y.set := ⟨y,hyY⟩
  obtain ⟨hxE,hgF,hgH⟩ := hgood y' hy
  let x := φ.map.inverse φ.bijective y'
  let Cx := vfParameterVolumeContext 𝔇 x.val
  let Bx := rowGammaBase 𝔅 x.val
  obtain ⟨e,he⟩ := Quotient.exact (hRows x.val hxE)
  let c := (jacobianValueDensityForm (φ.pureJacobian hc C Ξ hΞ)).value (pureVFEmptyGraphMap X.set x)
  have hconstF : ∀ u : F.family.domain, u.val.1 = x.val →
      (jacobianValueDensityForm (F.jacobianValue hc C Ξ hΞ φ hF)).value u = c := by
    intro u hu
    have hux : (⟨u.val.1,hF u⟩ : X.set) = x := Subtype.ext hu
    apply jacobian_value_density_congr
    rw [← hux]
    by_contra hne
    exact hgF u hne hu
  have hconstH : ∀ u : H.family.domain, u.val.1 = x.val →
      (jacobianValueDensityForm (H.jacobianValue hc C Ξ hΞ φ hH)).value u = c := by
    intro u hu
    have hux : (⟨u.val.1,hH u⟩ : X.set) = x := Subtype.ext hu
    apply jacobian_value_density_congr
    rw [← hux]
    by_contra hne
    exact hgH u hne hu
  have hPC : By.real ⊆ (Cy.base : Set M) := by
    rintro z (hz | hz)
    · exact vfParameterVolumeContext_contains 𝔇 y (Or.inl (gamma_named_code_context_base C Ξ hΞ hz))
    · exact vfParameterVolumeContext_contains 𝔇 y (Or.inr hz)
  have hΓ : Cardinal.mk By.gamma < Cy.κ := hΞ
  let D := gammaDefinableNamesVolumeContext hc Cy By hPC hΓ
  have hYD : (Cy.base : Set M) ⊆ (D.base : Set M) :=
    fun z hz => gamma_definable_names_context_contains hc Cy By hPC hΓ (Or.inl hz)
  have hxdef : ∀ i, DefinableClosureAtBase By .vf (x.val i).val :=
    definableClosure_of_gamma_vf_point (φ.inverse_point_gamma C Ξ hΞ y')
  have hxD : ∀ i, (x.val i).val ∈ (D.base : Set M) :=
    fun i => gamma_definable_names_context_singleton hc Cy By hPC hΓ (hxdef i)
  have hXD : (Cx.base : Set M) ⊆ (D.base : Set M) := by
    intro z hz
    refine (Substructure.closure_le.mpr ?_) hz
    rintro w (hw | ⟨i,rfl⟩)
    · exact hYD (vfParameterVolumeContext_contains 𝔇 y (Or.inl hw))
    · exact hxD i
  have hNamesY := row_context_names 𝔇 𝔅 (gamma_named_code_context_names C Ξ hΞ) y
  have hDnames : ∀ t ∈ (D.base : Set M), (Cy.base : Set M).Definable₁ LRV {t} := by
    intro t ht
    have h := (mem_definableClosure_iff_raw hc _ t).mp ht
    rwa [Set.union_eq_left.mpr hNamesY] at h
  let JF := (F.jacobian hc C Ξ hΞ φ hF).family.rowInContext y
  let JH := (H.jacobian hc C Ξ hΞ φ hH).family.rowInContext y
  let FX := F.family.rowInContext x.val
  let HX := H.family.rowInContext x.val
  have hFdom : ∀ r, r ∈ (JF.extend hYD).underlying.obj.domain.carrier ↔ r ∈ (FX.extend hXD).underlying.obj.domain.carrier :=
    fun r => HK.ZeroVFVolumeFamily.pushforwardBase_fibre F.family φ.map φ.bijective hF y' r
  have hHdom : ∀ r, r ∈ (JH.extend hYD).underlying.obj.domain.carrier ↔ r ∈ (HX.extend hXD).underlying.obj.domain.carrier :=
    fun r => HK.ZeroVFVolumeFamily.pushforwardBase_fibre H.family φ.map φ.bijective hH y' r
  let e1 := e.extend hXD
  let fF : SpecialTransformations.DefinableGeometry.Map (JF.extend hYD).underlying.obj.domain
      (FX.extend hXD).underlying.obj.domain :=
    SpecialTransformations.DefinableGeometry.Map.inclusion (fun r hr => (hFdom r).mp hr)
  let fH : SpecialTransformations.DefinableGeometry.Map (HX.extend hXD).underlying.obj.domain
      (JH.extend hYD).underlying.obj.domain :=
    SpecialTransformations.DefinableGeometry.Map.inclusion (fun r hr => (hHdom r).mpr hr)
  let g := fH.comp ((finiteIsoMap e1.iso).comp fF)
  have hg : Function.Bijective g := by
    have hfF : Function.Bijective fF := ⟨fun u v huv => Subtype.ext (congrArg (fun w : (FX.extend hXD).underlying.obj.domain => w.val) huv),
      fun v => ⟨⟨v.val,(hFdom v.val).mpr v.property⟩,rfl⟩⟩
    have hfH : Function.Bijective fH := ⟨fun u v huv => Subtype.ext (congrArg (fun w : (JH.extend hYD).underlying.obj.domain => w.val) huv),
      fun v => ⟨⟨v.val,(hHdom v.val).mp v.property⟩,rfl⟩⟩
    exact hfH.comp ((finiteIsoMap_bijective e1.iso).comp hfF)
  have hjF : ∀ r : (JF.extend hYD).underlying.obj.domain,
      (JF.extend hYD).form.value r = F.family.form.value ⟨(x.val,r.val),(hFdom r.val).mp r.property⟩ * c⁻¹ := by
    intro r
    let p : F.family.domain := ⟨(x.val,r.val),(hFdom r.val).mp r.property⟩
    have hq : (mixedVFBaseMap φ.map F.family.domain hF).toImage p =
        (⟨(y,r.val),r.property⟩ : (F.jacobian hc C Ξ hΞ φ hF).family.domain) := by
      apply Subtype.ext
      exact Prod.ext (congrArg Subtype.val
        (SpecialTransformations.DefinableGeometry.Map.apply_inverse φ.map φ.bijective y')) rfl
    have h := jacobian_transported_form_value (mixedVFBaseMap φ.map F.family.domain hF).toImage
      (mixed_vf_base_map_to_image_bijective φ.map φ.bijective.1 F.family.domain hF)
      (F.jacobianValue hc C Ξ hΞ φ hF) F.family.form p
    rw [hq,hconstF p rfl,div_eq_mul_inv] at h
    exact h
  have hjH : ∀ r : (JH.extend hYD).underlying.obj.domain,
      (JH.extend hYD).form.value r = H.family.form.value ⟨(x.val,r.val),(hHdom r.val).mp r.property⟩ * c⁻¹ := by
    intro r
    let p : H.family.domain := ⟨(x.val,r.val),(hHdom r.val).mp r.property⟩
    have hq : (mixedVFBaseMap φ.map H.family.domain hH).toImage p =
        (⟨(y,r.val),r.property⟩ : (H.jacobian hc C Ξ hΞ φ hH).family.domain) := by
      apply Subtype.ext
      exact Prod.ext (congrArg Subtype.val
        (SpecialTransformations.DefinableGeometry.Map.apply_inverse φ.map φ.bijective y')) rfl
    have h := jacobian_transported_form_value (mixedVFBaseMap φ.map H.family.domain hH).toImage
      (mixed_vf_base_map_to_image_bijective φ.map φ.bijective.1 H.family.domain hH)
      (H.jacobianValue hc C Ξ hΞ φ hH) H.family.form p
    rw [hq,hconstH p rfl,div_eq_mul_inv] at h
    exact h
  have hdens : ∀ r, (JF.extend hYD).form.value r = (JH.extend hYD).form.value (g r) := by
    intro r
    rw [hjF,hjH]
    congr 1
    exact e.density ⟨r.val,(hFdom r.val).mp r.property⟩
  let e2 := HK.ZeroRVVolumeIso.ofBijection g hg hdens
  let e3 := e2.descendDefinableNames hYD hDnames
  have hdom : GammaBaseDominated Bx By := by
    refine ⟨?_,Set.Subset.refl _⟩
    rintro z (hz | ⟨i,rfl⟩)
    · exact (subset_closureBase By).1 (Or.inl hz)
    · exact ⟨.vf,hxdef i⟩
  refine Quotient.sound ⟨e3,?_⟩
  have he' := hdom.graph he
  apply SpecialTransformations.Section5.GammaGraphDefinable.congr he'
  intro p q
  constructor
  · rintro ⟨u,hu,hq⟩
    refine ⟨⟨u.val,(hFdom u.val).mpr u.property⟩,hu,?_⟩
    rw [← hq]
    rfl
  · rintro ⟨u,hu,hq⟩
    refine ⟨⟨u.val,(hFdom u.val).mp u.property⟩,hu,?_⟩
    rw [← hq]
    rfl

end IntegrationInACVF.Section7.GammaFun
