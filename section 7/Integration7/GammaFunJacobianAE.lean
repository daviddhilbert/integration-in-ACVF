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

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {G : Base (M := M)} {n m a b : ℕ}

/-- Jacobian value densities depend only on the Jacobian value. -/
theorem jacobian_value_density_congr {S : Set M}
    {A : SpecialTransformations.DefinableGeometry.DefSet (SpecialTransformations.Section4.rawMixedSpace (M := M) n a) S}
    {B : SpecialTransformations.DefinableGeometry.DefSet (SpecialTransformations.Section4.rawMixedSpace (M := M) m b) S}
    (j₁ : SpecialTransformations.DefinableGeometry.Map A
      (SpecialTransformations.DefinableGeometry.DefSet.univ (SpecialTransformations.Section4.rawVFSpace (M := M) 1) S))
    (j₂ : SpecialTransformations.DefinableGeometry.Map B
      (SpecialTransformations.DefinableGeometry.DefSet.univ (SpecialTransformations.Section4.rawVFSpace (M := M) 1) S))
    (p : A) (q : B) (h : (j₁ p).val 0 = (j₂ q).val 0) :
    (jacobianValueDensityForm j₁).value p = (jacobianValueDensityForm j₂).value q := by
  have he : j₁ p = j₂ q := Subtype.ext (funext fun i => by
    have hi : i = 0 := Subsingleton.elim i 0
    subst hi
    exact h)
  change (nonzeroRVScalarMap S ((scalarEncodedRVMap S) (j₁ p))).val 0 =
    (nonzeroRVScalarMap S ((scalarEncodedRVMap S) (j₂ q))).val 0
  rw [he]

theorem gamma_univ_rv_one_set :
    GammaSetDefinable G {p : Point (M := M) 0 1 |
      p.2 ∈ (SpecialTransformations.DefinableGeometry.DefSet.univ
        (SpecialTransformations.Section4.rawRVSpace (M := M) 1) G.real).carrier} := by
  have h := (gammaLogicInput G).image_graph
    ((gammaLogicInput G).swap_graph (gamma_global_map_graph (B := G)
      (mixedCoordinatePointMap (id : Fin 0 → Fin 0) (id : Fin 1 → Fin 1) G.real)))
  convert h using 1
  ext p
  constructor
  · intro _
    exact ⟨p,Prod.ext rfl rfl⟩
  · intro _
    exact Set.mem_univ _

/-- The Gamma graph of the density of a Gamma Jacobian value map. -/
theorem gamma_jacobian_value_density_graph (hc : CanonicalStructure.IsCanonical (M := M)) {S : Set M}
    {A : SpecialTransformations.DefinableGeometry.DefSet (SpecialTransformations.Section4.rawMixedSpace (M := M) n a) S}
    (j : SpecialTransformations.DefinableGeometry.Map A
      (SpecialTransformations.DefinableGeometry.DefSet.univ (SpecialTransformations.Section4.rawVFSpace (M := M) 1) S))
    (hjΓ : GammaGraphDefinable G (fun (p : Point (M := M) n a) (z : Point (M := M) 1 0) =>
      ∃ u : A, u.val = p ∧ (j u).val = z.1)) :
    GammaGraphDefinable G (volumeFormGraph (jacobianValueDensityForm j)) := by
  have L := gammaLogicInput G
  have hnz := gamma_real_rv_map_graph hc G (nonzeroRVScalarMap G.real) (nonzeroRVScalarMap G.real)
    gamma_univ_rv_one_set (fun _ => rfl)
  have h := L.comp_graph (L.comp_graph hjΓ (gamma_scalar_rv_graph (G := G))) hnz
  apply SpecialTransformations.Section5.GammaGraphDefinable.congr h
  intro p y
  constructor
  · rintro ⟨w,⟨z,⟨u,rfl,hz⟩,rfl⟩,⟨t,ht,hty⟩⟩
    refine ⟨u,rfl,?_⟩
    rw [← hty]
    funext i
    have hi : i = 0 := Subsingleton.elim i 0
    subst hi
    classical
    change (if (CanonicalRV.encodedRv ((j u).val 0)).val = iRVZero then 1 else CanonicalRV.encodedRv ((j u).val 0)) =
      (if (t.val 0).val = iRVZero then 1 else t.val 0)
    rw [show t.val 0 = SpecialTransformations.Section5.rv ((j u).val 0) from (congrFun ht 0).trans (by rw [← hz])]
    rfl
  · rintro ⟨u,rfl,hy⟩
    refine ⟨(Fin.elim0,fun _ => SpecialTransformations.Section5.rv ((j u).val 0)),
      ⟨((j u).val,Fin.elim0),⟨u,rfl,rfl⟩,rfl⟩,
      ⟨⟨fun _ => SpecialTransformations.Section5.rv ((j u).val 0),Set.mem_univ _⟩,rfl,?_⟩⟩
    rw [← hy]
    funext i
    have hi : i = 0 := Subsingleton.elim i 0
    subst hi
    rfl

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

/-- The row of a Gamma Jacobian transform is a constant rescaling of the original row. -/
def jacobianRowIso {X Y : GammaVFSet C Ξ hΞ n} (F : Presentation C Ξ hΞ n k) (φ : GammaVFBijection C Ξ hΞ X Y)
    (hF : F.SupportedIn C Ξ hΞ X) (y : Y.set) (D : BaseContext M)
    (hXD : ((vfParameterVolumeContext 𝔇 (φ.map.inverse φ.bijective y).val).base : Set M) ⊆ (D.base : Set M))
    (hYD : ((vfParameterVolumeContext 𝔇 y.val).base : Set M) ⊆ (D.base : Set M))
    (c : CanonicalRV.RVSort M) (hcD : c⁻¹.val ∈ (D.base : Set M)) (hc0 : c⁻¹ ≠ 0)
    (hconst : ∀ u : F.family.domain, u.val.1 = (φ.map.inverse φ.bijective y).val →
      (jacobianValueDensityForm (F.jacobianValue hc C Ξ hΞ φ hF)).value u = c) :
    RVVolumeIso (((F.family.rowInContext (φ.map.inverse φ.bijective y).val).extend hXD).rescale c⁻¹ hcD hc0)
      (((F.jacobian hc C Ξ hΞ φ hF).family.rowInContext y.val).extend hYD) := by
  let x := φ.map.inverse φ.bijective y
  let U := ((F.family.rowInContext x.val).extend hXD).rescale c⁻¹ hcD hc0
  let V := ((F.jacobian hc C Ξ hΞ φ hF).family.rowInContext y.val).extend hYD
  have hUV : U.underlying.obj.domain.carrier = V.underlying.obj.domain.carrier := by
    ext r
    exact (F.family.pushforwardBase_fibre φ.map φ.bijective hF y r).symm
  let e : U.underlying ≅ V.underlying := SpecialTransformations.Section4.rvFiniteIsoOfAmbient
    (U := U.underlying) (V := V.underlying) (SpecialTransformations.Section4.rvIsoOfCarrierEq U.underlying.obj.domain V.underlying.obj.domain
    U.underlying.obj.volume V.underlying.obj.volume hUV (fun _ => rfl))
  apply RVVolumeIso.of_preserving_coordinates_full hc D e (fun _ => rfl)
  intro r
  let p : F.family.domain := ⟨(x.val,r.val),r.property⟩
  have hq : (mixedVFBaseMap φ.map F.family.domain hF).toImage p =
      (⟨(y.val,r.val),hUV.le r.property⟩ : (F.jacobian hc C Ξ hΞ φ hF).family.domain) := by
    apply Subtype.ext
    exact Prod.ext (congrArg Subtype.val (SpecialTransformations.DefinableGeometry.Map.apply_inverse φ.map φ.bijective y)) rfl
  have h := jacobian_transported_form_value (mixedVFBaseMap φ.map F.family.domain hF).toImage
    (mixed_vf_base_map_to_image_bijective φ.map φ.bijective.1 F.family.domain hF)
    (F.jacobianValue hc C Ξ hΞ φ hF) F.family.form p
  rw [hq,hconst p rfl,div_eq_mul_inv,mul_comm] at h
  exact h

/-- The preimage point of a Gamma VF bijection is a Gamma singleton over the row base of the image. -/
theorem GammaVFBijection.inverse_point_gamma {X Y : GammaVFSet C Ξ hΞ n} (φ : GammaVFBijection C Ξ hΞ X Y)
    (y : Y.set) :
    GammaSetDefinable (rowGammaBase 𝔅 y.val) {q : Point (M := M) (n+1) 0 | q.1 = (φ.map.inverse φ.bijective y).val} := by
  have h := gamma_graph_vf_fibre ((gammaLogicInput 𝔅).swap_graph φ.gamma) y.val
  convert h using 1
  ext q
  constructor
  · intro hq
    refine ⟨φ.map.inverse φ.bijective y,hq.symm,?_⟩
    exact congrArg Subtype.val (SpecialTransformations.DefinableGeometry.Map.apply_inverse φ.map φ.bijective y)
  · rintro ⟨u,hu,hφu⟩
    have he : u = φ.map.inverse φ.bijective y := by
      apply φ.bijective.1
      rw [SpecialTransformations.DefinableGeometry.Map.apply_inverse]
      exact Subtype.ext hφu
    change q.1 = (φ.map.inverse φ.bijective y).val
    rw [← hu,he]

/-- The pure Jacobian density at the preimage point is a Gamma singleton over the row base. -/
theorem GammaVFBijection.inverse_density_gamma {X Y : GammaVFSet C Ξ hΞ n} (φ : GammaVFBijection C Ξ hΞ X Y)
    (y : Y.set) :
    GammaSetDefinable (rowGammaBase 𝔅 y.val) {q : Point (M := M) 0 1 | q.2 0 =
      (jacobianValueDensityForm (φ.pureJacobian hc C Ξ hΞ)).value
        (pureVFEmptyGraphMap X.set (φ.map.inverse φ.bijective y))} := by
  let L := gammaLogicInput 𝔅
  have hd := gamma_jacobian_value_density_graph hc _ (φ.pureJacobian_gamma hc C Ξ hΞ)
  have h := gamma_graph_vf_fibre (L.comp_graph (L.swap_graph φ.gamma) hd) y.val
  convert h using 1
  ext q
  let x := φ.map.inverse φ.bijective y
  constructor
  · intro hq
    refine ⟨(x.val,Fin.elim0),⟨x,rfl,?_⟩,⟨pureVFEmptyGraphMap X.set x,?_,?_⟩⟩
    · exact congrArg Subtype.val (SpecialTransformations.DefinableGeometry.Map.apply_inverse φ.map φ.bijective y)
    · rw [pure_vf_empty_graph_map_value]
    · funext i
      have hi : i = 0 := Subsingleton.elim i 0
      subst hi
      exact hq.symm
  · rintro ⟨xp,⟨u,hu,hφu⟩,⟨v,hv,hvq⟩⟩
    have he : u = x := by
      apply φ.bijective.1
      rw [SpecialTransformations.DefinableGeometry.Map.apply_inverse]
      exact Subtype.ext hφu
    have hv' : v = pureVFEmptyGraphMap X.set x := by
      apply Subtype.ext
      rw [hv,pure_vf_empty_graph_map_value]
      exact Prod.ext (by rw [← hu,he]) (funext fun i => i.elim0)
    rw [← hv'] 
    exact (congrFun hvq 0).symm

set_option maxHeartbeats 4000000 in
/-- **Gamma Jacobian transforms respect almost-everywhere equivalence.** -/
theorem presentation_jacobian_ae {X Y : GammaVFSet C Ξ hΞ n} (F H : Presentation C Ξ hΞ n k)
    (φ : GammaVFBijection C Ξ hΞ X Y) (hF : F.SupportedIn C Ξ hΞ X) (hH : H.SupportedIn C Ξ hΞ X)
    (h : AEEquivalent hc C Ξ hΞ F H) :
    AEEquivalent hc C Ξ hΞ (F.jacobian hc C Ξ hΞ φ hF) (H.jacobian hc C Ξ hΞ φ hH) := by
  obtain ⟨E,hE,hRows⟩ := h
  obtain ⟨E',hE',hgood⟩ := jacobian_ae_exceptional hc C Ξ hΞ F H φ hF hH E hE
  refine ⟨E',hE',?_⟩
  intro y hy
  let Cy := vfParameterVolumeContext 𝔇 y
  let By := rowGammaBase 𝔅 y
  by_cases hyY : y ∈ Y.set.carrier
  swap
  · have hF0 := selected_jacobian_row_empty_outside 𝔇 F.family φ.map φ.bijective hF y hyY
    have hH0 := selected_jacobian_row_empty_outside 𝔇 H.family φ.map φ.bijective hH y hyY
    apply (gammaVolumeBlowupClass_eq_iff hc Cy By).mpr
    refine GammaVolumeBlowupEquivalent.of_iso Cy By (RVVolumeIso.of_empty hc Cy _ _ hF0 hH0) ?_
    apply SpecialTransformations.Section5.GammaGraphDefinable.congr (FiniteRV.gamma_empty_graph (B := By) _ _)
    intro p q
    constructor
    · exact False.elim
    · rintro ⟨u,_,_⟩
      exact (hF0.le (rvEssentialLabels_subset _ u.property)).elim
  let y' : Y.set := ⟨y,hyY⟩
  obtain ⟨hxE,hgF,hgH⟩ := hgood y' hy
  let x := φ.map.inverse φ.bijective y'
  let Cx := vfParameterVolumeContext 𝔇 x.val
  let Bx := rowGammaBase 𝔅 x.val
  have hx := (gammaVolumeBlowupClass_eq_iff hc Cx Bx).mp (hRows x.val hxE)
  let c := (jacobianValueDensityForm (φ.pureJacobian hc C Ξ hΞ)).value (pureVFEmptyGraphMap X.set x)
  have hconst : ∀ {P : Presentation C Ξ hΞ n k} (hP : P.SupportedIn C Ξ hΞ X),
      (∀ u : P.family.domain, (P.jacobianValue hc C Ξ hΞ φ hP u).val 0 ≠
        (φ.pureJacobian hc C Ξ hΞ (pureVFEmptyGraphMap X.set ⟨u.val.1,hP u⟩)).val 0 → u.val.1 ≠ x.val) →
      ∀ u : P.family.domain, u.val.1 = x.val →
        (jacobianValueDensityForm (P.jacobianValue hc C Ξ hΞ φ hP)).value u = c := by
    intro P hP hg u hu
    have hux : (⟨u.val.1,hP u⟩ : X.set) = x := Subtype.ext hu
    apply jacobian_value_density_congr
    rw [← hux]
    by_contra hne
    exact hg u hne hu
  -- the comparison context and base
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
  have hcdef : DefinableClosureAtBase By .rv c.val :=
    definableClosure_of_gamma_rv_point (φ.inverse_density_gamma hc C Ξ hΞ y')
  have hxD : ∀ i, (x.val i).val ∈ (D.base : Set M) :=
    fun i => gamma_definable_names_context_singleton hc Cy By hPC hΓ (hxdef i)
  have hcD : c.val ∈ (D.base : Set M) := gamma_definable_names_context_singleton hc Cy By hPC hΓ hcdef
  have hXD : (Cx.base : Set M) ⊆ (D.base : Set M) := by
    intro z hz
    refine (Substructure.closure_le.mpr ?_) hz
    rintro w (hw | ⟨i,rfl⟩)
    · exact hYD (vfParameterVolumeContext_contains 𝔇 y (Or.inl hw))
    · exact hxD i
  have hc0 : c ≠ 0 := (jacobianValueDensityForm (φ.pureJacobian hc C Ξ hΞ)).nonzero _
  have hi0 : c⁻¹ ≠ 0 := inv_ne_zero hc0
  have hiD : c⁻¹.val ∈ (D.base : Set M) := SpecialTransformations.Section4.ResiduePurity.rv_inv_mem_base D.base hcD
  let B' : Base (M := M) := ⟨By.real ∪ Set.range (fun i => (x.val i).val) ∪ {c.val},Ξ⟩
  have hiB : c⁻¹.val ∈ Substructure.closure LRV B'.real :=
    SpecialTransformations.Section4.ResiduePurity.rv_inv_mem_base _ (Substructure.subset_closure (Or.inr rfl))
  have hdom1 : GammaBaseDominated Bx B' := by
    refine GammaBaseDominated.of_subset ?_ (Set.Subset.refl _)
    rintro z (hz | hz)
    · exact Or.inl (Or.inl (Or.inl hz))
    · exact Or.inl (Or.inr hz)
  have hdomY : GammaBaseDominated By B' :=
    GammaBaseDominated.of_subset (fun z hz => Or.inl (Or.inl hz)) (Set.Subset.refl _)
  have hdom2 : GammaBaseDominated B' By := by
    refine ⟨?_,Set.Subset.refl _⟩
    rintro z ((hz | ⟨i,rfl⟩) | hz)
    · exact (subset_closureBase By).1 hz
    · exact ⟨.vf,hxdef i⟩
    · rw [Set.mem_singleton_iff.mp hz]
      exact ⟨.rv,hcdef⟩
  let Fx : GammaVolumeObjects Bx (Cx.base : Set M) k := ⟨F.family.rowInContext x.val,F.gamma.row hc x.val⟩
  let Hx : GammaVolumeObjects Bx (Cx.base : Set M) k := ⟨H.family.rowInContext x.val,H.gamma.row hc x.val⟩
  let FX := ((Fx.extend hXD).changeBase hdom1).rescale hc c⁻¹ hiD hiB hi0
  let HX := ((Hx.extend hXD).changeBase hdom1).rescale hc c⁻¹ hiD hiB hi0
  have h2 : GammaVolumeBlowupEquivalent B' (D.base : Set M) k FX HX :=
    ((hx.extend hXD).changeBase hdom1).rescale hc D c⁻¹ hiD hiB hi0
  let JF : GammaVolumeObjects By (Cy.base : Set M) k :=
    ⟨(F.jacobian hc C Ξ hΞ φ hF).family.rowInContext y,(F.jacobian hc C Ξ hΞ φ hF).gamma.row hc y⟩
  let JH : GammaVolumeObjects By (Cy.base : Set M) k :=
    ⟨(H.jacobian hc C Ξ hΞ φ hH).family.rowInContext y,(H.jacobian hc C Ξ hΞ φ hH).gamma.row hc y⟩
  let JF' := (JF.extend hYD).changeBase hdomY
  let JH' := (JH.extend hYD).changeBase hdomY
  have heF := gamma_volume_iso_of_label_identity hc
    (jacobianRowIso hc C Ξ hΞ F φ hF y' D hXD hYD c hiD hi0 (hconst hF hgF)) FX.property rfl (fun _ => rfl)
  have heH := gamma_volume_iso_of_label_identity hc
    (jacobianRowIso hc C Ξ hΞ H φ hH y' D hXD hYD c hiD hi0 (hconst hH hgH)) HX.property rfl (fun _ => rfl)
  have h3 : GammaVolumeBlowupEquivalent B' (D.base : Set M) k JF' JH' :=
    ((GammaVolumeBlowupEquivalent.of_iso D B' (U := FX) (V := JF') _ heF).symm hc D B').trans hc D B'
      (h2.trans hc D B' (GammaVolumeBlowupEquivalent.of_iso D B' (U := HX) (V := JH') _ heH))
  have h4 : GammaVolumeBlowupEquivalent By (D.base : Set M) k (JF.extend hYD) (JH.extend hYD) :=
    h3.changeBase hdom2
  have hCommon : CommonContextVolumeEquivalent By Cy JF JH := ⟨D,hYD,h4⟩
  exact (gammaVolumeBlowupClass_eq_iff hc Cy By).mpr
    (hCommon.descend hc Cy (row_context_names 𝔇 𝔅 (gamma_named_code_context_names C Ξ hΞ) y))

end IntegrationInACVF.Section7.GammaFun
