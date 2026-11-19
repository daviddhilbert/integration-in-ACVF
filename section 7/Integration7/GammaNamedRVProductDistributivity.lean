import Integration7.GammaNamedRVProductLaws
import Integration7.HKVolumeRightDistributivity
import Integration7.HKVolumeLeftDistributivity
import Integration7.GammaTaggedRVMapGraphs
import Integration7.GammaRVTagMaps

/-! Distributivity of actual products over actual coproducts on Gamma-named
RV classes. The fold maps are glued from coordinate maps and tag maps on the
two summands, so their graphs are Gamma. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section5 (Point GammaSetDefinable GammaGraphDefinable gammaLogicInput)
open IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {B : Base (M := M)} {S : Set M} {k l c : ℕ}

theorem gamma_coprod_glued_map (U V : RVObject (M := M) S k)
    {D D₁ D₂ : DefSet (rawRVSpace (M := M) c) S}
    (F : Map (rvCoprodObject U V).domain D) (f : Map U.domain D₁) (g : Map V.domain D₂)
    (hf : RVMapGamma f B) (hg : RVMapGamma g B)
    (hl : ∀ u, (F (rvCoprodLeftMap U V u)).val = (f u).val)
    (hr : ∀ v, (F (rvCoprodRightMap U V v)).val = (g v).val) : RVMapGamma F B :=
  gamma_tagged_rv_map_graph U V F
    ((Map.inclusion (show D₁.carrier ⊆ (DefSet.univ (rawRVSpace (M := M) c) S).carrier from
      fun _ _ => Set.mem_univ _)).comp f)
    ((Map.inclusion (show D₂.carrier ⊆ (DefSet.univ (rawRVSpace (M := M) c) S).carrier from
      fun _ _ => Set.mem_univ _)).comp g)
    (hf.congr (fun _ => rfl)) (hg.congr (fun _ => rfl)) hl hr

theorem gamma_rv_identity_map (hc : CanonicalStructure.IsCanonical (M := M)) {a : ℕ}
    (A : DefSet (rawRVSpace (M := M) a) S)
    (hA : GammaSetDefinable B {p : Point (M := M) 0 a | p.2 ∈ A.carrier}) :
    RVMapGamma (Map.id A) B :=
  gamma_rv_coordinate_map hc (Map.id A) id hA (fun _ => rfl)

theorem gamma_rv_coprod_left_map (hc : CanonicalStructure.IsCanonical (M := M)) (U V : RVObject (M := M) S k)
    (hU : GammaSetDefinable B {p : Point (M := M) 0 U.arity | p.2 ∈ U.domain.carrier}) :
    RVMapGamma (rvCoprodLeftMap U V) B :=
  (gamma_rv_left_tag_map hc U.domain V.arity hU).congr (fun _ => rfl)

theorem gamma_rv_coprod_right_map (hc : CanonicalStructure.IsCanonical (M := M)) (U V : RVObject (M := M) S k)
    (hV : GammaSetDefinable B {p : Point (M := M) 0 V.arity | p.2 ∈ V.domain.carrier}) :
    RVMapGamma (rvCoprodRightMap U V) B :=
  (gamma_rv_right_tag_map hc V.domain U.arity hV).congr (fun _ => rfl)

theorem gamma_rv_product_map_pair {k' l' : ℕ}
    {U U' : RVObject (M := M) S k} {V V' : RVObject (M := M) S l}
    {f : Map U.domain U'.domain} {g : Map V.domain V'.domain}
    (hf : RVMapGamma f B) (hg : RVMapGamma g B) : RVMapGamma (rvProductMap f g) B := by
  apply gamma_rv_product_map hf hg
  intro w
  obtain ⟨u,v,rfl⟩ := exists_rvPackPair U.domain V.domain w
  rw [rvProductMap_pair,rvUnpack_pair]
  rfl

theorem gamma_rv_product_coprod_fold (hc : CanonicalStructure.IsCanonical (M := M))
    (A : RVObject (M := M) S k) (V W : RVObject (M := M) S l)
    (hA : GammaSetDefinable B {p : Point (M := M) 0 A.arity | p.2 ∈ A.domain.carrier})
    (hV : GammaSetDefinable B {p : Point (M := M) 0 V.arity | p.2 ∈ V.domain.carrier})
    (hW : GammaSetDefinable B {p : Point (M := M) 0 W.arity | p.2 ∈ W.domain.carrier}) :
    RVMapGamma (rvProductCoprodFold A V W).map B :=
  gamma_coprod_glued_map _ _ _ _ _
    (gamma_rv_product_map_pair (k' := 0) (l' := 0) (gamma_rv_identity_map hc _ hA)
      (gamma_rv_coprod_left_map hc V W hV))
    (gamma_rv_product_map_pair (k' := 0) (l' := 0) (gamma_rv_identity_map hc _ hA)
      (gamma_rv_coprod_right_map hc V W hW))
    (fun x => congrArg Subtype.val (rvProductCoprodFold_left A V W x))
    (fun x => congrArg Subtype.val (rvProductCoprodFold_right A V W x))

theorem gamma_rv_left_product_coprod_fold (hc : CanonicalStructure.IsCanonical (M := M))
    (U V : RVObject (M := M) S k) (W : RVObject (M := M) S l)
    (hU : GammaSetDefinable B {p : Point (M := M) 0 U.arity | p.2 ∈ U.domain.carrier})
    (hV : GammaSetDefinable B {p : Point (M := M) 0 V.arity | p.2 ∈ V.domain.carrier})
    (hW : GammaSetDefinable B {p : Point (M := M) 0 W.arity | p.2 ∈ W.domain.carrier}) :
    RVMapGamma (rvLeftProductCoprodFold U V W).map B :=
  gamma_coprod_glued_map _ _ _ _ _
    (gamma_rv_product_map_pair (k' := 0) (l' := 0) (gamma_rv_coprod_left_map hc U V hU)
      (gamma_rv_identity_map hc _ hW))
    (gamma_rv_product_map_pair (k' := 0) (l' := 0) (gamma_rv_coprod_right_map hc U V hV)
      (gamma_rv_identity_map hc _ hW))
    (fun x => congrArg Subtype.val (rvLeftProductCoprodFold_left U V W x))
    (fun x => congrArg Subtype.val (rvLeftProductCoprodFold_right U V W x))

end IntegrationInACVF.Section7

namespace IntegrationInACVF.Section7.HK
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {B : Base (M := M)} {S : Set M}

theorem RVVolumeObject.Gamma.coprod {n : ℕ} {U V : RVVolumeObject (M := M) S n}
    (hU : RVVolumeObject.Gamma n U B) (hV : RVVolumeObject.Gamma n V B) :
    RVVolumeObject.Gamma n (HK.coprod S n U V) B := by
  cases n with
  | zero =>
    exact (RVVolumeObject.Gamma.zero_iff _).mpr
      (((RVVolumeObject.Gamma.zero_iff U).mp hU).coprod ((RVVolumeObject.Gamma.zero_iff V).mp hV))
  | succ k =>
    exact (RVVolumeObject.Gamma.positive_iff _).mpr
      (((RVVolumeObject.Gamma.positive_iff U).mp hU).coprod ((RVVolumeObject.Gamma.positive_iff V).mp hV))

def GammaRVObjects.coprod {n : ℕ} (U V : GammaRVObjects B S n) : GammaRVObjects B S n :=
  ⟨HK.coprod S n U.val V.val,U.property.coprod V.property⟩

variable (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
variable (Ξ : Set (Values.Gamma (M := M))) (hΞ : Cardinal.mk Ξ < C.κ)

set_option quotPrecheck false
local notation "𝔅" => gammaNamedBase C Ξ
local notation "𝔇" => gammaNamedCodeContext C Ξ hΞ
local notation "𝔖" => ((gammaNamedCodeContext C Ξ hΞ).base : Set M)

theorem gammaNamedRVClass_coprod {n : ℕ} (U V : GammaRVObjects 𝔅 𝔖 n) :
    gammaNamedRVClass hc C Ξ hΞ (U.coprod V) =
      gammaNamedRVClass hc C Ξ hΞ U + gammaNamedRVClass hc C Ξ hΞ V := by
  cases n with
  | zero => rfl
  | succ k => rfl

set_option allowUnsafeReducibility true in
attribute [local reducible] RVVolumeData.coprod productData rvFiniteProductObject
  rvFiniteCoprodObject rvCoprodObject rvProductObject in
theorem gamma_product_right_distrib {n m : ℕ} (U : GammaRVObjects 𝔅 𝔖 n) (V W : GammaRVObjects 𝔅 𝔖 m) :
    gammaNamedRVClass hc C Ξ hΞ (U.product hc (V.coprod W)) =
      gammaNamedRVClass hc C Ξ hΞ ((U.product hc V).coprod (U.product hc W)) := by
  obtain ⟨U,hU⟩ := U
  obtain ⟨V,hV⟩ := V
  obtain ⟨W,hW⟩ := W
  let D := productData n m U V
  let E := productData n m U W
  let G := productData n m U (HK.coprod 𝔖 m V W)
  have hF : RVVolumeObject.Gamma (n+m) (ofData (D.coprod E)) 𝔅 := by
    rw [data_coprod_ofData]
    exact (RVVolumeObject.Gamma.product hc hU hV).coprod (RVVolumeObject.Gamma.product hc hU hW)
  have hG : RVVolumeObject.Gamma (n+m) (ofData G) 𝔅 := RVVolumeObject.Gamma.product hc hU (hV.coprod hW)
  have hAd := hU.domain
  have hBd := hV.domain
  have hLd := hW.domain
  have key : gammaNamedRVClass hc C Ξ hΞ ⟨ofData (D.coprod E),hF⟩ = gammaNamedRVClass hc C Ξ hΞ ⟨ofData G,hG⟩ := by
    revert hF hG hAd hBd hLd
    cases n <;> cases m
    all_goals
      intro hF hG hAd hBd hLd
      let A := underlying 𝔖 _ U
      let Bv := underlying 𝔖 _ V
      let L := underlying 𝔖 _ W
      let ωU := form 𝔖 _ U
      exact eq_of_heq (gammaNamedRVClass_heq_of_reindex hc C Ξ hΞ rfl (D.coprod E) G
        (rvProductCoprodFold A.obj Bv.obj L.obj).map (rvProductCoprodFold_bijective A.obj Bv.obj L.obj)
        (by
          intro x
          change (rvProductObject A.obj (rvCoprodObject Bv.obj L.obj)).value _ =
            (rvCoprodObject (rvProductObject A.obj Bv.obj) (rvProductObject A.obj L.obj)).value x
          rcases rvObjectCoprod_cases (rvProductObject A.obj Bv.obj) (rvProductObject A.obj L.obj) x
            with ⟨a,rfl⟩ | ⟨a,rfl⟩
          · obtain ⟨u,v,rfl⟩ := exists_rvPackPair A.obj.domain Bv.obj.domain a
            rw [rvProductCoprodFold_left,rvProductMap_pair,rvProductObject_value_pair,
              rvCoprod_value_left,rvCoprod_value_left,rvProductObject_value_pair]
            rfl
          · obtain ⟨u,w,rfl⟩ := exists_rvPackPair A.obj.domain L.obj.domain a
            rw [rvProductCoprodFold_right,rvProductMap_pair,rvProductObject_value_pair,
              rvCoprod_value_right,rvCoprod_value_right,rvProductObject_value_pair]
            rfl)
        (by
          intro x
          rcases rvObjectCoprod_cases (rvProductObject A.obj Bv.obj) (rvProductObject A.obj L.obj) x
            with ⟨a,rfl⟩ | ⟨a,rfl⟩
          · obtain ⟨u,v,rfl⟩ := exists_rvPackPair A.obj.domain Bv.obj.domain a
            have he := (rvProductCoprodFold_left A.obj Bv.obj L.obj (rvPackPair _ _ u v)).trans
              (rvProductMap_pair (Map.id A.obj.domain) (rvCoprodLeftMap Bv.obj L.obj) u v)
            exact (congrArg G.form.value he).trans
              ((productData_density_pair _ _ U (HK.coprod 𝔖 _ V W) u (rvCoprodLeftMap Bv.obj L.obj v)).trans
                ((congrArg (fun t => ωU.value u * t) (coprod_density_left _ V W v)).trans
                  ((productData_density_pair _ _ U V u v).symm.trans
                    (RVVolumeData.coprod_density_left D E (rvPackPair _ _ u v)).symm)))
          · obtain ⟨u,w,rfl⟩ := exists_rvPackPair A.obj.domain L.obj.domain a
            have he := (rvProductCoprodFold_right A.obj Bv.obj L.obj (rvPackPair _ _ u w)).trans
              (rvProductMap_pair (Map.id A.obj.domain) (rvCoprodRightMap Bv.obj L.obj) u w)
            exact (congrArg G.form.value he).trans
              ((productData_density_pair _ _ U (HK.coprod 𝔖 _ V W) u (rvCoprodRightMap Bv.obj L.obj w)).trans
                ((congrArg (fun t => ωU.value u * t) (coprod_density_right _ V W w)).trans
                  ((productData_density_pair _ _ U W u w).symm.trans
                    (RVVolumeData.coprod_density_right D E (rvPackPair _ _ u w)).symm))))
        hF hG (gamma_rv_product_coprod_fold hc A.obj Bv.obj L.obj hAd hBd hLd))
  exact key.symm.trans (gammaNamedRVClass_congr hc C Ξ hΞ (data_coprod_ofData D E))

set_option allowUnsafeReducibility true in
attribute [local reducible] RVVolumeData.coprod productData rvFiniteProductObject
  rvFiniteCoprodObject rvCoprodObject rvProductObject in
theorem gamma_product_left_distrib {n m : ℕ} (U V : GammaRVObjects 𝔅 𝔖 n) (W : GammaRVObjects 𝔅 𝔖 m) :
    gammaNamedRVClass hc C Ξ hΞ ((U.coprod V).product hc W) =
      gammaNamedRVClass hc C Ξ hΞ ((U.product hc W).coprod (V.product hc W)) := by
  obtain ⟨U,hU⟩ := U
  obtain ⟨V,hV⟩ := V
  obtain ⟨W,hW⟩ := W
  let D := productData n m U W
  let E := productData n m V W
  let G := productData n m (HK.coprod 𝔖 n U V) W
  have hF : RVVolumeObject.Gamma (n+m) (ofData (D.coprod E)) 𝔅 := by
    rw [data_coprod_ofData]
    exact (RVVolumeObject.Gamma.product hc hU hW).coprod (RVVolumeObject.Gamma.product hc hV hW)
  have hG : RVVolumeObject.Gamma (n+m) (ofData G) 𝔅 := RVVolumeObject.Gamma.product hc (hU.coprod hV) hW
  have hAd := hU.domain
  have hBd := hV.domain
  have hLd := hW.domain
  have key : gammaNamedRVClass hc C Ξ hΞ ⟨ofData (D.coprod E),hF⟩ = gammaNamedRVClass hc C Ξ hΞ ⟨ofData G,hG⟩ := by
    revert hF hG hAd hBd hLd
    cases n <;> cases m
    all_goals
      intro hF hG hAd hBd hLd
      let A := underlying 𝔖 _ U
      let Bv := underlying 𝔖 _ V
      let L := underlying 𝔖 _ W
      let ωW := form 𝔖 _ W
      exact eq_of_heq (gammaNamedRVClass_heq_of_reindex hc C Ξ hΞ rfl (D.coprod E) G
        (rvLeftProductCoprodFold A.obj Bv.obj L.obj).map (rvLeftProductCoprodFold_bijective A.obj Bv.obj L.obj)
        (by
          intro x
          change (rvProductObject (rvCoprodObject A.obj Bv.obj) L.obj).value _ =
            (rvCoprodObject (rvProductObject A.obj L.obj) (rvProductObject Bv.obj L.obj)).value x
          rcases rvObjectCoprod_cases (rvProductObject A.obj L.obj) (rvProductObject Bv.obj L.obj) x
            with ⟨a,rfl⟩ | ⟨a,rfl⟩
          · obtain ⟨u,w,rfl⟩ := exists_rvPackPair A.obj.domain L.obj.domain a
            rw [rvLeftProductCoprodFold_left,rvProductMap_pair,rvProductObject_value_pair,
              rvCoprod_value_left,rvCoprod_value_left,rvProductObject_value_pair]
            rfl
          · obtain ⟨v,w,rfl⟩ := exists_rvPackPair Bv.obj.domain L.obj.domain a
            rw [rvLeftProductCoprodFold_right,rvProductMap_pair,rvProductObject_value_pair,
              rvCoprod_value_right,rvCoprod_value_right,rvProductObject_value_pair]
            rfl)
        (by
          intro x
          rcases rvObjectCoprod_cases (rvProductObject A.obj L.obj) (rvProductObject Bv.obj L.obj) x
            with ⟨a,rfl⟩ | ⟨a,rfl⟩
          · obtain ⟨u,w,rfl⟩ := exists_rvPackPair A.obj.domain L.obj.domain a
            have he := (rvLeftProductCoprodFold_left A.obj Bv.obj L.obj (rvPackPair _ _ u w)).trans
              (rvProductMap_pair (rvCoprodLeftMap A.obj Bv.obj) (Map.id L.obj.domain) u w)
            exact (congrArg G.form.value he).trans
              ((productData_density_pair _ _ (HK.coprod 𝔖 _ U V) W (rvCoprodLeftMap A.obj Bv.obj u) w).trans
                ((congrArg (fun t => t * ωW.value w) (coprod_density_left _ U V u)).trans
                  ((productData_density_pair _ _ U W u w).symm.trans
                    (RVVolumeData.coprod_density_left D E (rvPackPair _ _ u w)).symm)))
          · obtain ⟨v,w,rfl⟩ := exists_rvPackPair Bv.obj.domain L.obj.domain a
            have he := (rvLeftProductCoprodFold_right A.obj Bv.obj L.obj (rvPackPair _ _ v w)).trans
              (rvProductMap_pair (rvCoprodRightMap A.obj Bv.obj) (Map.id L.obj.domain) v w)
            exact (congrArg G.form.value he).trans
              ((productData_density_pair _ _ (HK.coprod 𝔖 _ U V) W (rvCoprodRightMap A.obj Bv.obj v) w).trans
                ((congrArg (fun t => t * ωW.value w) (coprod_density_right _ U V v)).trans
                  ((productData_density_pair _ _ V W v w).symm.trans
                    (RVVolumeData.coprod_density_right D E (rvPackPair _ _ v w)).symm))))
        hF hG (gamma_rv_left_product_coprod_fold hc A.obj Bv.obj L.obj hAd hBd hLd))
  exact key.symm.trans (gammaNamedRVClass_congr hc C Ξ hΞ (data_coprod_ofData D E))

end IntegrationInACVF.Section7.HK
