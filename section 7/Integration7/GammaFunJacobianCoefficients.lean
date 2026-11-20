import Integration7.GammaFunJacobianLinearity

/-! **Jacobian transforms of coefficient products.** For each coefficient action, the Jacobian
transform of the product, computed with the value map transported from the underlying
presentation, has the same rows as the coefficient product of the Jacobian transform. Combined
with the comparison of value maps, the Jacobian transform of a coefficient product is almost
everywhere the coefficient product of the Jacobian transform. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section5 (Point GammaSetDefinable GammaGraphDefinable gammaLogicInput carrier)
open SpecialTransformations.DefinableGeometry (Map DefSet)
open SpecialTransformations.Section4 (rawMixedSpace rawRVSpace rawVFSpace)
open IntegrationInACVF.Section5 IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {G : Base (M := M)} {S : Set M} {n a b : ℕ}

/-- The map selecting RV labels between mixed domains. -/
def mixedRVSelectMap (D : DefSet (rawMixedSpace (M := M) n a) S) (D' : DefSet (rawMixedSpace (M := M) n b) S)
    (τ : Fin b → Fin a) (h : ∀ q ∈ D.carrier, (q.1,q.2 ∘ τ) ∈ D'.carrier) : Map D D' :=
  ((Map.prodUnivMap (Map.id (DefSet.univ (rawVFSpace (M := M) n) S))
    (rvCoordinateSelectMap S τ)).comp (Map.id D).toUniv).corestrict
    (fun q => h q.val q.property)

theorem mixed_rv_select_map_value (D : DefSet (rawMixedSpace (M := M) n a) S)
    (D' : DefSet (rawMixedSpace (M := M) n b) S) (τ : Fin b → Fin a)
    (h : ∀ q ∈ D.carrier, (q.1,q.2 ∘ τ) ∈ D'.carrier) (q : D) :
    (mixedRVSelectMap D D' τ h q).val = (q.val.1,q.val.2 ∘ τ) := rfl

/-- The Gamma graph of a value map composed with a label selection. -/
theorem gamma_value_map_comp_select {D : DefSet (rawMixedSpace (M := M) n a) S}
    {D' : DefSet (rawMixedSpace (M := M) n b) S} (τ : Fin b → Fin a)
    (h : ∀ q ∈ D.carrier, (q.1,q.2 ∘ τ) ∈ D'.carrier) (hD : GammaSetDefinable G D.carrier)
    (j : Map D' (DefSet.univ (rawVFSpace (M := M) 1) S))
    (hjΓ : GammaGraphDefinable G (fun (p : Point (M := M) n b) (z : Point (M := M) 1 0) =>
      ∃ u : D', u.val = p ∧ (j u).val = z.1)) :
    GammaGraphDefinable G (fun (p : Point (M := M) n a) (z : Point (M := M) 1 0) =>
      ∃ u : D, u.val = p ∧ ((j.comp (mixedRVSelectMap D D' τ h)) u).val = z.1) := by
  have L := gammaLogicInput G
  have hR := L.restrict_graph hD (hjΓ.preimage_maps
    (mixedCoordinatePointMap (id : Fin n → Fin n) τ G.real)
    (mixedCoordinatePointMap (id : Fin 1 → Fin 1) (id : Fin 0 → Fin 0) G.real))
  apply SpecialTransformations.Section5.GammaGraphDefinable.congr hR
  intro p z
  simp only [mixedCoordinatePointMap_value]
  constructor
  · rintro ⟨hp,u',hu',hz⟩
    refine ⟨⟨p,hp⟩,rfl,?_⟩
    have he : mixedRVSelectMap D D' τ h ⟨p,hp⟩ = u' := Subtype.ext hu'.symm
    change (j (mixedRVSelectMap D D' τ h ⟨p,hp⟩)).val = z.1
    rw [he]
    exact hz
  · rintro ⟨u,rfl,hz⟩
    exact ⟨u.property,mixedRVSelectMap D D' τ h u,rfl,hz⟩

theorem mem_vf_base_image {X Y : DefSet (rawVFSpace (M := M) n) S} (φ : Map X Y) (D : DefSet (rawMixedSpace (M := M) n a) S)
    (hD : ∀ p : D, p.val.1 ∈ X.carrier) (y : Fin n → VFType (M := M)) (r : Fin a → CanonicalRV.RVSort M) :
    (y,r) ∈ (mixedVFBaseMap φ D hD).image.carrier ↔ ∃ p : D, (φ ⟨p.val.1,hD p⟩).val = y ∧ p.val.2 = r := by
  constructor
  · rintro ⟨p,hp⟩
    exact ⟨p,congrArg Prod.fst hp,congrArg Prod.snd hp⟩
  · rintro ⟨p,h1,h2⟩
    exact ⟨p,Prod.ext h1 h2⟩

end IntegrationInACVF.Section7

namespace IntegrationInACVF.Section7.GammaFun
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n k p : ℕ}
variable (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
variable (Ξ : Set (Values.Gamma (M := M))) (hΞ : Cardinal.mk Ξ < C.κ)

set_option quotPrecheck false
local notation "𝔅" => gammaNamedBase C Ξ
local notation "𝔇" => gammaNamedCodeContext C Ξ hΞ
local notation "𝔖" => ((gammaNamedCodeContext C Ξ hΞ).base : Set M)

theorem presentation_left_product_supported {X : GammaVFSet C Ξ hΞ n} (U : GammaVolumeObjects 𝔅 𝔖 p)
    (F : Presentation C Ξ hΞ n k) (hF : F.SupportedIn C Ξ hΞ X) :
    (F.leftProduct hc C Ξ hΞ U).SupportedIn C Ξ hΞ X := by
  intro q
  exact hF ⟨_,((mem_left_product_coords U.val F.family q.val).mp q.property).1⟩

set_option maxHeartbeats 6400000 in
/-- **Jacobian transforms commute with positive coefficients on positive presentations.** -/
theorem presentation_left_product_jacobian {X Y : GammaVFSet C Ξ hΞ n} (U : GammaVolumeObjects 𝔅 𝔖 p)
    (F : Presentation C Ξ hΞ n k) (φ : GammaVFBijection C Ξ hΞ X Y) (hF : F.SupportedIn C Ξ hΞ X) :
    AEEquivalent hc C Ξ hΞ
      ((F.leftProduct hc C Ξ hΞ U).jacobian hc C Ξ hΞ φ (presentation_left_product_supported hc C Ξ hΞ U F hF))
      ((F.jacobian hc C Ξ hΞ φ hF).leftProduct hc C Ξ hΞ U) := by
  let S := F.leftProduct hc C Ξ hΞ U
  have hS := presentation_left_product_supported hc C Ξ hΞ U F hF
  let τ := leftProductBaseIndex F.arity U.val.underlying.obj.arity (((p+1)+k)+1)
  have hτ : ∀ q ∈ S.family.domain.carrier, (q.1,q.2 ∘ τ) ∈ F.family.domain.carrier :=
    fun q hq => ((mem_left_product_coords U.val F.family q).mp hq).1
  let π := mixedRVSelectMap S.family.domain F.family.domain τ hτ
  let jF := F.jacobianValue hc C Ξ hΞ φ hF
  have hjFΓ := (Classical.choose_spec (presentation_jacobian_value_exists hc C Ξ hΞ F φ hF)).1
  have hjF := F.jacobianValue_spec hc C Ξ hΞ φ hF
  let jT := jF.comp π
  have hjTΓ := gamma_value_map_comp_select τ hτ S.gamma.domain jF hjFΓ
  have hjT : IsJacobianValueMap (mixedVFBaseMap φ.map S.family.domain hS).toImage jT :=
    is_jacobian_value_map_comp φ.map hS hF π (fun _ => rfl) (fun q x hx => hτ (x,q.val.2) hx) jF hjF
  have step1 := presentation_jacobian_with_ae hc C Ξ hΞ S φ hS _ jT
    (Classical.choose_spec (presentation_jacobian_value_exists hc C Ξ hΞ S φ hS)).1 hjTΓ
    (S.jacobianValue_spec hc C Ξ hΞ φ hS) hjT
  refine (aeSetoid hc C Ξ hΞ n _).iseqv.trans step1 (ae_equivalent_of_rows hc C Ξ hΞ _ _ (fun y => ?_))
  let JT := S.jacobianWith hc C Ξ hΞ φ hS jT hjTΓ
  let JF := F.jacobian hc C Ξ hΞ φ hF
  let K := JF.leftProduct hc C Ξ hΞ U
  refine gamma_class_eq_of_select hc _ _ ⟨JT.family.rowInContext y,JT.gamma.row hc y⟩
    ⟨K.family.rowInContext y,K.gamma.row hc y⟩ id ?hmap ?hsurj (fun _ _ _ _ h => h) (fun _ => rfl) ?hden
  case hmap =>
    intro t ht
    obtain ⟨q,hq⟩ := ht
    have hq1 : (φ.map ⟨q.val.1,hS q⟩).val = y := congrArg Prod.fst hq
    have hq2 : q.val.2 = t := congrArg Prod.snd hq
    subst hq2
    obtain ⟨h1,hU,hv,hs⟩ := (mem_left_product_coords U.val F.family q.val).mp q.property
    change (y,q.val.2) ∈ K.family.domain.carrier
    refine (mem_left_product_coords U.val JF.family (y,q.val.2)).mpr ⟨?_,hU,hv,hs⟩
    exact (mem_vf_base_image φ.map F.family.domain hF y _).mpr ⟨⟨_,h1⟩,hq1,rfl⟩
  case hsurj =>
    intro t ht
    obtain ⟨h1,hU,hv,hs⟩ := (mem_left_product_coords U.val JF.family (y,t)).mp ht
    obtain ⟨f,hf1,hf2⟩ := (mem_vf_base_image φ.map F.family.domain hF y _).mp h1
    have hmem : (f.val.1,t) ∈ S.family.domain.carrier := by
      refine (mem_left_product_coords U.val F.family (f.val.1,t)).mpr ⟨?_,hU,hv,hs⟩
      have : (f.val.1,t ∘ τ) = f.val := Prod.ext rfl hf2.symm
      rw [this]
      exact f.property
    refine ⟨t,?_,rfl⟩
    exact (mem_vf_base_image φ.map S.family.domain hS y t).mpr ⟨⟨_,hmem⟩,hf1,rfl⟩
  case hden =>
    rintro ⟨tv,q,hq⟩
    have hq1 : (φ.map ⟨q.val.1,hS q⟩).val = y := congrArg Prod.fst hq
    have hq2 : q.val.2 = tv := congrArg Prod.snd hq
    subst hq2
    obtain ⟨h1,hU,hv,hs⟩ := (mem_left_product_coords U.val F.family q.val).mp q.property
    have hKmem : (y,q.val.2) ∈ K.family.domain.carrier :=
      (mem_left_product_coords U.val JF.family (y,q.val.2)).mpr
        ⟨(mem_vf_base_image φ.map F.family.domain hF y _).mpr ⟨⟨_,h1⟩,hq1,rfl⟩,hU,hv,hs⟩
    have hJFmem : (y,q.val.2 ∘ τ) ∈ JF.family.domain.carrier :=
      ((mem_left_product_coords U.val JF.family (y,q.val.2)).mp hKmem).1
    have eK := left_product_density_coords U.val JF.family ⟨(y,q.val.2),hKmem⟩
    have eS := left_product_density_coords U.val F.family q
    have eJF : JF.family.form.value ⟨(y,q.val.2 ∘ τ),hJFmem⟩ =
        F.family.form.value (π q) / (jacobianValueDensityForm jF).value (π q) := by
      have hpt : (⟨(y,q.val.2 ∘ τ),hJFmem⟩ : JF.family.domain) =
          (mixedVFBaseMap φ.map F.family.domain hF).toImage (π q) := Subtype.ext (Prod.ext hq1.symm rfl)
      rw [hpt]
      exact jacobian_transported_form_value _ _ jF F.family.form (π q)
    have eJT : JT.family.form.value ⟨(y,q.val.2),⟨q,hq⟩⟩ =
        S.family.form.value q / (jacobianValueDensityForm jT).value q := by
      have hpt : (⟨(y,q.val.2),⟨q,hq⟩⟩ : JT.family.domain) = (mixedVFBaseMap φ.map S.family.domain hS).toImage q :=
        Subtype.ext hq.symm
      rw [hpt]
      exact jacobian_transported_form_value _ _ jT S.family.form q
    change K.family.form.value ⟨(y,q.val.2),hKmem⟩ = JT.family.form.value ⟨(y,q.val.2),⟨q,hq⟩⟩
    refine eK.trans ?_
    rw [eJT,show S.family.form.value q = _ from eS]
    change _ * JF.family.form.value ⟨(y,q.val.2 ∘ τ),hJFmem⟩ = _
    rw [eJF,mul_div_assoc]
    rfl

end IntegrationInACVF.Section7.GammaFun
