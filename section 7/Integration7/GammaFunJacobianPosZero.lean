import Integration7.GammaFunJacobianZeroCoef

/-! **Jacobian transforms commute with positive coefficients on degree-zero presentations**
(almost everywhere). -/
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
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {C : BaseContext M} {n a p : ℕ}

/-- Label coordinates of the degree-zero family inside a positive-coefficient product. -/
def zeroPosBaseIndex (a b p : ℕ) : Fin a → Fin ((a+b)+(p+1)) := fun i => Fin.castAdd (p+1) (Fin.castAdd b i)
/-- Label coordinates of the coefficient inside a positive-coefficient product. -/
def zeroPosCoefIndex (a b p : ℕ) : Fin b → Fin ((a+b)+(p+1)) := fun i => Fin.castAdd (p+1) (Fin.natAdd a i)

theorem mem_zero_family_positive_product (U : PositiveRVVolumeObject (M := M) (C.base : Set M) p)
    (F : HK.ZeroVFVolumeFamily C n a) (q : Point (M := M) n ((a+U.underlying.obj.arity)+(p+1))) :
    q ∈ (HK.selectedZeroFamilyPositiveProduct U F).domain.carrier ↔
      (q.1,q.2 ∘ zeroPosBaseIndex a U.underlying.obj.arity p) ∈ F.domain.carrier ∧
      ∃ h : q.2 ∘ zeroPosCoefIndex a U.underlying.obj.arity p ∈ U.underlying.obj.domain.carrier,
        U.underlying.obj.value ⟨_,h⟩ = q.2 ∘ Fin.natAdd (a+U.underlying.obj.arity) := by
  constructor
  · rintro ⟨w,hw⟩
    have hv := ordinary_family_positive_coefficient_projection_value F.toOrdinary U w
    have hm := (mem_mixed_rv_factor_domain F.domain U.underlying.obj.domain w.val.1 w.val.2).mp w.property
    have hq : (appendMixedRVMap (F.mulConstant U).volume w).val = q := hw
    rw [append_mixed_rv_map_value] at hq
    subst hq
    refine ⟨?_,?_⟩
    · change (w.val.1,Fin.append w.val.2 _ ∘ zeroPosBaseIndex a U.underlying.obj.arity p) ∈ F.domain.carrier
      have : Fin.append w.val.2 ((F.mulConstant U).volume w).val ∘ zeroPosBaseIndex a U.underlying.obj.arity p =
          w.val.2 ∘ Fin.castAdd U.underlying.obj.arity := funext fun i => by simp [zeroPosBaseIndex]
      rw [this]
      exact hm.1
    · have h2 : Fin.append w.val.2 ((F.mulConstant U).volume w).val ∘ zeroPosCoefIndex a U.underlying.obj.arity p = w.val.2 ∘ Fin.natAdd a :=
        funext fun i => by simp [zeroPosCoefIndex]
      refine ⟨by
        change Fin.append w.val.2 ((F.mulConstant U).volume w).val ∘ zeroPosCoefIndex a U.underlying.obj.arity p ∈ _
        rw [h2]
        exact hm.2,?_⟩
      change _ = Fin.append w.val.2 ((F.mulConstant U).volume w).val ∘ Fin.natAdd (a+U.underlying.obj.arity)
      have h3 : Fin.append w.val.2 ((F.mulConstant U).volume w).val ∘ Fin.natAdd (a+U.underlying.obj.arity) =
          ((F.mulConstant U).volume w).val := funext fun i => by simp
      rw [h3]
      change _ = U.underlying.obj.value (ordinaryFamilyPositiveCoefficientProjection F.toOrdinary U w)
      congr 1
      apply Subtype.ext
      exact (show _ = w.val.2 ∘ Fin.natAdd a from h2).trans hv.symm
  · rintro ⟨h1,h2,hv⟩
    let w0 : (Fin n → VFType (M := M)) × (Fin (a+U.underlying.obj.arity) → CanonicalRV.RVSort M) := (q.1,q.2 ∘ Fin.castAdd (p+1))
    have hw0 : w0 ∈ (mixedRVFactorDomain F.domain U.underlying.obj.domain).carrier :=
      (mem_mixed_rv_factor_domain F.domain U.underlying.obj.domain w0.1 w0.2).mpr ⟨h1,h2⟩
    refine ⟨⟨w0,hw0⟩,?_⟩
    show (appendMixedRVMap (F.mulConstant U).volume ⟨w0,hw0⟩).val = q
    rw [append_mixed_rv_map_value]
    refine Prod.ext rfl ?_
    have hvol : ((F.mulConstant U).volume ⟨w0,hw0⟩).val = q.2 ∘ Fin.natAdd (a+U.underlying.obj.arity) := by
      refine Eq.trans ?_ hv
      change U.underlying.obj.value (ordinaryFamilyPositiveCoefficientProjection F.toOrdinary U ⟨w0,hw0⟩) = _
      congr 1
      apply Subtype.ext
      exact ordinary_family_positive_coefficient_projection_value F.toOrdinary U ⟨w0,hw0⟩
    rw [hvol]
    exact Fin.append_castAdd_natAdd

theorem zero_family_positive_product_density (U : PositiveRVVolumeObject (M := M) (C.base : Set M) p)
    (F : HK.ZeroVFVolumeFamily C n a) (q : (HK.selectedZeroFamilyPositiveProduct U F).domain) :
    (HK.selectedZeroFamilyPositiveProduct U F).form.value q =
      F.form.value ⟨_,((mem_zero_family_positive_product U F q.val).mp q.property).1⟩ *
        U.form.value ⟨_,((mem_zero_family_positive_product U F q.val).mp q.property).2.1⟩ := by
  let w := mixedRVMapGraphProjection (F.mulConstant U).volume q
  have hw := mixed_rv_map_graph_projection_value (F.mulConstant U).volume q
  have hu := mixed_rv_factor_unpack_value F.domain U.underlying.obj.domain w
  change (F.form.prod U.form).value (mixedRVFactorUnpack F.domain U.underlying.obj.domain w) = _
  have he : mixedRVFactorUnpack F.domain U.underlying.obj.domain w =
      ⟨((q.val.1,q.val.2 ∘ zeroPosBaseIndex a U.underlying.obj.arity p),q.val.2 ∘ zeroPosCoefIndex a U.underlying.obj.arity p),
        ((mem_zero_family_positive_product U F q.val).mp q.property).1,
        ((mem_zero_family_positive_product U F q.val).mp q.property).2.1⟩ := by
    apply Subtype.ext
    rw [hu]
    change ((w.val.1,w.val.2 ∘ Fin.castAdd U.underlying.obj.arity),w.val.2 ∘ Fin.natAdd a) = _
    rw [hw]
    rfl
  rw [he]
  rfl

end IntegrationInACVF.Section7

namespace IntegrationInACVF.Section7.GammaFun
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n p : ℕ}
variable (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
variable (Ξ : Set (Values.Gamma (M := M))) (hΞ : Cardinal.mk Ξ < C.κ)

set_option quotPrecheck false
local notation "𝔅" => gammaNamedBase C Ξ
local notation "𝔇" => gammaNamedCodeContext C Ξ hΞ
local notation "𝔖" => ((gammaNamedCodeContext C Ξ hΞ).base : Set M)

theorem zero_presentation_pos_coef_supported {X : GammaVFSet C Ξ hΞ n} (U : GammaVolumeObjects 𝔅 𝔖 p)
    (F : ZeroPresentation C Ξ hΞ n) (hF : F.SupportedIn C Ξ hΞ X) :
    (F.posCoef hc C Ξ hΞ U).SupportedIn C Ξ hΞ X := fun q =>
  hF ⟨_,((mem_zero_family_positive_product U.val F.family q.val).mp q.property).1⟩

set_option maxHeartbeats 6400000 in
/-- **Jacobian transforms commute with positive coefficients on degree-zero presentations.** -/
theorem zero_presentation_pos_coef_jacobian {X Y : GammaVFSet C Ξ hΞ n} (U : GammaVolumeObjects 𝔅 𝔖 p)
    (F : ZeroPresentation C Ξ hΞ n) (φ : GammaVFBijection C Ξ hΞ X Y) (hF : F.SupportedIn C Ξ hΞ X) :
    AEEquivalent hc C Ξ hΞ
      ((F.posCoef hc C Ξ hΞ U).jacobian hc C Ξ hΞ φ (zero_presentation_pos_coef_supported hc C Ξ hΞ U F hF))
      ((F.jacobian hc C Ξ hΞ φ hF).posCoef hc C Ξ hΞ U) := by
  let S := F.posCoef hc C Ξ hΞ U
  have hS := zero_presentation_pos_coef_supported hc C Ξ hΞ U F hF
  let τ := zeroPosBaseIndex F.arity U.val.underlying.obj.arity p
  have hτ : ∀ q ∈ S.family.domain.carrier, (q.1,q.2 ∘ τ) ∈ F.family.domain.carrier :=
    fun q hq => ((mem_zero_family_positive_product U.val F.family q).mp hq).1
  let π := mixedRVSelectMap S.family.domain F.family.domain τ hτ
  let jF := F.jacobianValue hc C Ξ hΞ φ hF
  have hjFΓ := F.jacobianValue_gamma hc C Ξ hΞ φ hF
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
  let K := JF.posCoef hc C Ξ hΞ U
  refine gamma_class_eq_of_select hc _ _ ⟨JT.family.rowInContext y,JT.gamma.row hc y⟩
    ⟨K.family.rowInContext y,K.gamma.row hc y⟩ id ?hmap ?hsurj (fun _ _ _ _ h => h) (fun _ => rfl) ?hden
  case hmap =>
    intro t ht
    obtain ⟨q,hq⟩ := ht
    have hq1 : (φ.map ⟨q.val.1,hS q⟩).val = y := congrArg Prod.fst hq
    have hq2 : q.val.2 = t := congrArg Prod.snd hq
    subst hq2
    obtain ⟨h1,h2⟩ := (mem_zero_family_positive_product U.val F.family q.val).mp q.property
    change (y,q.val.2) ∈ K.family.domain.carrier
    exact (mem_zero_family_positive_product U.val JF.family (y,q.val.2)).mpr
      ⟨(mem_vf_base_image φ.map F.family.domain hF y _).mpr ⟨⟨_,h1⟩,hq1,rfl⟩,h2⟩
  case hsurj =>
    intro t ht
    obtain ⟨h1,h2⟩ := (mem_zero_family_positive_product U.val JF.family (y,t)).mp ht
    obtain ⟨f,hf1,hf2⟩ := (mem_vf_base_image φ.map F.family.domain hF y _).mp h1
    have hmem : (f.val.1,t) ∈ S.family.domain.carrier := by
      refine (mem_zero_family_positive_product U.val F.family (f.val.1,t)).mpr ⟨?_,h2⟩
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
    obtain ⟨h1,h2⟩ := (mem_zero_family_positive_product U.val F.family q.val).mp q.property
    have hKmem : (y,q.val.2) ∈ K.family.domain.carrier :=
      (mem_zero_family_positive_product U.val JF.family (y,q.val.2)).mpr
        ⟨(mem_vf_base_image φ.map F.family.domain hF y _).mpr ⟨⟨_,h1⟩,hq1,rfl⟩,h2⟩
    have hJFmem : (y,q.val.2 ∘ τ) ∈ JF.family.domain.carrier :=
      ((mem_zero_family_positive_product U.val JF.family (y,q.val.2)).mp hKmem).1
    have eK := zero_family_positive_product_density U.val JF.family ⟨(y,q.val.2),hKmem⟩
    have eS := zero_family_positive_product_density U.val F.family q
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
    change JF.family.form.value ⟨(y,q.val.2 ∘ τ),hJFmem⟩ * _ = _
    rw [eJF,div_mul_eq_mul_div]
    rfl

end IntegrationInACVF.Section7.GammaFun
