import Integration7.GammaFunJacobians
import Integration7.GammaPointDefinability
import Integration7.GammaVolumeBaseChange
import Integration7.SelectedJacobianRowIsomorphisms
import Integration7.SelectedJacobianAlmostEverywhere
import Integration7.GammaDefinableNameContexts

/-! Gamma Jacobian transforms respect almost-everywhere equivalence. Outside the image of
a Gamma VF-small locus, rows of a Gamma Jacobian transform are constant rescalings of the
original rows; the comparison is carried out over an enlarged Gamma base and returned to the
row base by change of Gamma base along definable points. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section9
open SpecialTransformations.Section5 (Point GammaSetDefinable GammaGraphDefinable gammaLogicInput carrier)
open SpecialTransformations.Section4 (vfValues)
open IntegrationInACVF.Section5 IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7.GammaFun
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n a b k : ℕ}
variable (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
variable (Ξ : Set (Values.Gamma (M := M))) (hΞ : Cardinal.mk Ξ < C.κ)
variable (hGenerated : VFGammaGeneratedBase (gammaNamedBase C Ξ))

set_option quotPrecheck false
local notation "𝔅" => gammaNamedBase C Ξ
local notation "𝔇" => gammaNamedCodeContext C Ξ hΞ
local notation "𝔖" => ((gammaNamedCodeContext C Ξ hΞ).base : Set M)

/-- The pure mixed graph of a Gamma VF bijection is Gamma. -/
theorem GammaVFBijection.pure_mixed_graph {X Y : GammaVFSet C Ξ hΞ n} (φ : GammaVFBijection C Ξ hΞ X Y) :
    GammaGraphDefinable 𝔅 (vfMixedMapGraph (pureVFMixedMap φ.map)) := by
  apply SpecialTransformations.Section5.GammaGraphDefinable.congr φ.gamma
  intro p q
  constructor
  · rintro ⟨u,hu,hq⟩
    refine ⟨⟨(u.val,Fin.elim0),u.property,Set.mem_univ _⟩,Prod.ext hu (funext fun i => i.elim0),?_⟩
    exact Prod.ext hq (funext fun i => i.elim0)
  · rintro ⟨v,rfl,rfl⟩
    exact ⟨⟨v.val.1,v.property.1⟩,rfl,rfl⟩

include hc in
theorem pure_jacobian_value_exists {X Y : GammaVFSet C Ξ hΞ n} (φ : GammaVFBijection C Ξ hΞ X Y) :
    ∃ j : SpecialTransformations.DefinableGeometry.Map
        (X.set.prod (SpecialTransformations.DefinableGeometry.DefSet.univ
          (SpecialTransformations.Section4.rawRVSpace (M := M) 0) 𝔖))
        (SpecialTransformations.DefinableGeometry.DefSet.univ (SpecialTransformations.Section4.rawVFSpace (M := M) 1) 𝔖),
      GammaGraphDefinable 𝔅 (fun (p : Point (M := M) (n+1) 0) (z : Point (M := M) 1 0) =>
        ∃ u : X.set.prod (SpecialTransformations.DefinableGeometry.DefSet.univ
          (SpecialTransformations.Section4.rawRVSpace (M := M) 0) 𝔖), u.val = p ∧ (j u).val = z.1) ∧
      IsJacobianValueMap (pureVFMixedMap φ.map) j :=
  gamma_exists_totalMixedJacobianMap hc (Nat.zero_lt_succ n) _ (φ.pure_mixed_graph C Ξ hΞ)

/-- The chosen Gamma Jacobian value map of the pure base map. -/
def GammaVFBijection.pureJacobian {X Y : GammaVFSet C Ξ hΞ n} (φ : GammaVFBijection C Ξ hΞ X Y) :=
  Classical.choose (pure_jacobian_value_exists hc C Ξ hΞ φ)

theorem GammaVFBijection.pureJacobian_gamma {X Y : GammaVFSet C Ξ hΞ n} (φ : GammaVFBijection C Ξ hΞ X Y) :
    GammaGraphDefinable 𝔅 (fun (p : Point (M := M) (n+1) 0) (z : Point (M := M) 1 0) =>
      ∃ u : X.set.prod (SpecialTransformations.DefinableGeometry.DefSet.univ
        (SpecialTransformations.Section4.rawRVSpace (M := M) 0) 𝔖), u.val = p ∧ (φ.pureJacobian hc C Ξ hΞ u).val = z.1) :=
  (Classical.choose_spec (pure_jacobian_value_exists hc C Ξ hΞ φ)).1

theorem GammaVFBijection.pureJacobian_spec {X Y : GammaVFSet C Ξ hΞ n} (φ : GammaVFBijection C Ξ hΞ X Y) :
    IsJacobianValueMap (pureVFMixedMap φ.map) (φ.pureJacobian hc C Ξ hΞ) :=
  (Classical.choose_spec (pure_jacobian_value_exists hc C Ξ hΞ φ)).2

theorem Presentation.jacobianValue_gamma {X Y : GammaVFSet C Ξ hΞ n} (F : Presentation C Ξ hΞ n k)
    (φ : GammaVFBijection C Ξ hΞ X Y) (hF : F.SupportedIn C Ξ hΞ X) :
    GammaGraphDefinable 𝔅 (fun (p : Point (M := M) (n+1) F.arity) (z : Point (M := M) 1 0) =>
      ∃ u : F.family.domain, u.val = p ∧ (F.jacobianValue hc C Ξ hΞ φ hF u).val = z.1) :=
  (Classical.choose_spec (presentation_jacobian_value_exists hc C Ξ hΞ F φ hF)).1

/-- **The Jacobian discrepancy locus** of a supported presentation is Gamma. -/
theorem jacobian_discrepancy_gamma {X Y : GammaVFSet C Ξ hΞ n} (F : Presentation C Ξ hΞ n k)
    (φ : GammaVFBijection C Ξ hΞ X Y) (hF : F.SupportedIn C Ξ hΞ X) :
    GammaSetDefinable 𝔅 {q : Point (M := M) (n+1) 0 | ∃ u : F.family.domain, u.val.1 = q.1 ∧
      (F.jacobianValue hc C Ξ hΞ φ hF u).val 0 ≠
        (φ.pureJacobian hc C Ξ hΞ (pureVFEmptyGraphMap X.set ⟨u.val.1,hF u⟩)).val 0} := by
  let L := gammaLogicInput 𝔅
  have hJF := F.jacobianValue_gamma hc C Ξ hΞ φ hF
  have hJX := φ.pureJacobian_gamma hc C Ξ hΞ
  have hJX' := hJX.preimage_maps
    (mixedCoordinatePointMap (id : Fin (n+1) → Fin (n+1)) (Fin.elim0 : Fin 0 → Fin F.arity) (gammaNamedBase C Ξ).real)
    (mixedCoordinatePointMap (id : Fin 1 → Fin 1) (id : Fin 0 → Fin 0) (gammaNamedBase C Ξ).real)
  have hAgree := L.image_graph (L.swap_graph (hJF.inter hJX'))
  have hDisc := L.sdiff F.gamma.domain hAgree
  have hBad := L.image_real
    (mixedCoordinatePointMap (id : Fin (n+1) → Fin (n+1)) (Fin.elim0 : Fin 0 → Fin F.arity) (gammaNamedBase C Ξ).real) hDisc
  convert hBad using 1
  ext q
  constructor
  · rintro ⟨u,hu,hne⟩
    refine ⟨⟨u.val,Set.mem_univ _⟩,⟨u.property,?_⟩,?_⟩
    · rintro ⟨z,⟨u',hu',hz⟩,⟨v,hv,hvz⟩⟩
      have hu'' : u' = u := Subtype.ext hu'
      subst hu''
      apply hne
      have hv' : v = pureVFEmptyGraphMap X.set ⟨u'.val.1,hF u'⟩ := by
        apply Subtype.ext
        rw [hv,pure_vf_empty_graph_map_value,mixedCoordinatePointMap_value]
        exact Prod.ext rfl (funext fun i => i.elim0)
      rw [← hv']
      exact (congrFun hz 0).trans (congrFun hvz 0).symm
    · exact Prod.ext hu (funext fun i => i.elim0)
  · rintro ⟨p,⟨hp,hna⟩,hq⟩
    let u : F.family.domain := ⟨p.val,hp⟩
    refine ⟨u,congrArg Prod.fst hq,?_⟩
    intro he
    apply hna
    refine ⟨((fun _ => (F.jacobianValue hc C Ξ hΞ φ hF u).val 0),Fin.elim0),⟨u,rfl,?_⟩,
      ⟨pureVFEmptyGraphMap X.set ⟨u.val.1,hF u⟩,?_,?_⟩⟩
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

/-- Membership in a pure VF formula locus. -/
theorem mem_pureVFFormulaLocus_points {R : Set (Fin (n+1) → M)} {hR : DefinableOver 𝔖 (fun _ => SortTag.vf) R}
    (x : Fin (n+1) → VFType (M := M)) :
    x ∈ (pureVFFormulaLocus R hR).carrier ↔ vfValues x ∈ R := Iff.rfl

set_option maxHeartbeats 2400000 in
/-- **The exceptional set of a Jacobian comparison.** -/
theorem jacobian_ae_exceptional {X Y : GammaVFSet C Ξ hΞ n} (F H : Presentation C Ξ hΞ n k)
    (φ : GammaVFBijection C Ξ hΞ X Y) (hF : F.SupportedIn C Ξ hΞ X) (hH : H.SupportedIn C Ξ hΞ X)
    (E : GammaVFSet C Ξ hΞ n)
    (hE : SpecialTransformations.Section4.vfDim (SpecialTransformations.Section4.rawRVSpace (M := M) 1) E.set < n+1) :
    ∃ E' : GammaVFSet C Ξ hΞ n,
      SpecialTransformations.Section4.vfDim (SpecialTransformations.Section4.rawRVSpace (M := M) 1) E'.set < n+1 ∧
      ∀ y : Y.set, y.val ∉ E'.set.carrier →
        (φ.map.inverse φ.bijective y).val ∉ E.set.carrier ∧
        (∀ u : F.family.domain, (F.jacobianValue hc C Ξ hΞ φ hF u).val 0 ≠
          (φ.pureJacobian hc C Ξ hΞ (pureVFEmptyGraphMap X.set ⟨u.val.1,hF u⟩)).val 0 →
            u.val.1 ≠ (φ.map.inverse φ.bijective y).val) ∧
        (∀ u : H.family.domain, (H.jacobianValue hc C Ξ hΞ φ hH u).val 0 ≠
          (φ.pureJacobian hc C Ξ hΞ (pureVFEmptyGraphMap X.set ⟨u.val.1,hH u⟩)).val 0 →
            u.val.1 ≠ (φ.map.inverse φ.bijective y).val) := by
  let L := gammaLogicInput 𝔅
  let BadPts : Set (Point (M := M) (n+1) 0) := {q | q.1 ∈ X.set.carrier} ∩
    ({q | q.1 ∈ E.set.carrier} ∪
      ({q | ∃ u : F.family.domain, u.val.1 = q.1 ∧ (F.jacobianValue hc C Ξ hΞ φ hF u).val 0 ≠
          (φ.pureJacobian hc C Ξ hΞ (pureVFEmptyGraphMap X.set ⟨u.val.1,hF u⟩)).val 0} ∪
       {q | ∃ u : H.family.domain, u.val.1 = q.1 ∧ (H.jacobianValue hc C Ξ hΞ φ hH u).val 0 ≠
          (φ.pureJacobian hc C Ξ hΞ (pureVFEmptyGraphMap X.set ⟨u.val.1,hH u⟩)).val 0}))
  have hBad : GammaSetDefinable 𝔅 BadPts := L.inter X.gamma (L.union E.gamma
    (L.union (jacobian_discrepancy_gamma hc C Ξ hΞ F φ hF) (jacobian_discrepancy_gamma hc C Ξ hΞ H φ hH)))
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
      apply jacobian_values_agree_at_generic hc 𝔇 (Nat.zero_lt_succ n) φ.map F.family.domain hF _
        (F.jacobianValue_spec hc C Ξ hΞ φ hF) _ (φ.pureJacobian_spec hc C Ξ hΞ) u
      rw [hu]
      exact hp
    · apply hne
      apply jacobian_values_agree_at_generic hc 𝔇 (Nat.zero_lt_succ n) φ.map H.family.domain hH _
        (H.jacobianValue_spec hc C Ξ hΞ φ hH) _ (φ.pureJacobian_spec hc C Ξ hΞ) u
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

end IntegrationInACVF.Section7.GammaFun
