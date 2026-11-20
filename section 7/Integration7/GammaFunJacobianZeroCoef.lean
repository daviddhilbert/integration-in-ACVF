import Integration7.GammaFunJacobianCoefficients

/-! **Jacobian transforms commute with weighted degree-zero coefficients on positive
presentations** (almost everywhere). -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section5 (Point GammaSetDefinable GammaGraphDefinable gammaLogicInput carrier)
open SpecialTransformations.DefinableGeometry (Map DefSet)
open SpecialTransformations.Section4 (rawMixedSpace rawRVSpace rawVFSpace)
open IntegrationInACVF.Section5 IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7.GammaFun
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n k : ℕ}
variable (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
variable (Ξ : Set (Values.Gamma (M := M))) (hΞ : Cardinal.mk Ξ < C.κ)

set_option quotPrecheck false
local notation "𝔅" => gammaNamedBase C Ξ
local notation "𝔇" => gammaNamedCodeContext C Ξ hΞ
local notation "𝔖" => ((gammaNamedCodeContext C Ξ hΞ).base : Set M)

theorem presentation_zero_coef_supported {X : GammaVFSet C Ξ hΞ n} (Z : HK.GammaZeroRVObjects 𝔅 𝔖)
    (F : Presentation C Ξ hΞ n k) (hF : F.SupportedIn C Ξ hΞ X) :
    (F.zeroCoef hc C Ξ hΞ Z).SupportedIn C Ξ hΞ X := fun q =>
  hF ⟨_,((mem_mixed_rv_factor_domain F.family.domain Z.val.underlying.obj.domain q.val.1 q.val.2).mp q.property).1⟩

set_option maxHeartbeats 6400000 in
/-- **Jacobian transforms commute with weighted degree-zero coefficients on positive presentations.** -/
theorem presentation_zero_coef_jacobian {X Y : GammaVFSet C Ξ hΞ n} (Z : HK.GammaZeroRVObjects 𝔅 𝔖)
    (F : Presentation C Ξ hΞ n k) (φ : GammaVFBijection C Ξ hΞ X Y) (hF : F.SupportedIn C Ξ hΞ X) :
    AEEquivalent hc C Ξ hΞ
      ((F.zeroCoef hc C Ξ hΞ Z).jacobian hc C Ξ hΞ φ (presentation_zero_coef_supported hc C Ξ hΞ Z F hF))
      ((F.jacobian hc C Ξ hΞ φ hF).zeroCoef hc C Ξ hΞ Z) := by
  let S := F.zeroCoef hc C Ξ hΞ Z
  have hS := presentation_zero_coef_supported hc C Ξ hΞ Z F hF
  let b := Z.val.underlying.obj.arity
  let τ : Fin F.arity → Fin (F.arity+b) := Fin.castAdd b
  have hτ : ∀ q ∈ S.family.domain.carrier, (q.1,q.2 ∘ τ) ∈ F.family.domain.carrier :=
    fun q hq => ((mem_mixed_rv_factor_domain F.family.domain Z.val.underlying.obj.domain q.1 q.2).mp hq).1
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
  let K := JF.zeroCoef hc C Ξ hΞ Z
  refine gamma_class_eq_of_select hc _ _ ⟨JT.family.rowInContext y,JT.gamma.row hc y⟩
    ⟨K.family.rowInContext y,K.gamma.row hc y⟩ id ?hmap ?hsurj (fun _ _ _ _ h => h) (fun _ => rfl) ?hden
  case hmap =>
    intro t ht
    obtain ⟨q,hq⟩ := ht
    have hq1 : (φ.map ⟨q.val.1,hS q⟩).val = y := congrArg Prod.fst hq
    have hq2 : q.val.2 = t := congrArg Prod.snd hq
    subst hq2
    obtain ⟨h1,h2⟩ := (mem_mixed_rv_factor_domain F.family.domain Z.val.underlying.obj.domain q.val.1 q.val.2).mp
      q.property
    change (y,q.val.2) ∈ K.family.domain.carrier
    exact (mem_mixed_rv_factor_domain JF.family.domain Z.val.underlying.obj.domain y q.val.2).mpr
      ⟨(mem_vf_base_image φ.map F.family.domain hF y _).mpr ⟨⟨_,h1⟩,hq1,rfl⟩,h2⟩
  case hsurj =>
    intro t ht
    obtain ⟨h1,h2⟩ := (mem_mixed_rv_factor_domain JF.family.domain Z.val.underlying.obj.domain y t).mp ht
    obtain ⟨f,hf1,hf2⟩ := (mem_vf_base_image φ.map F.family.domain hF y _).mp h1
    have hmem : (f.val.1,t) ∈ S.family.domain.carrier := by
      refine (mem_mixed_rv_factor_domain F.family.domain Z.val.underlying.obj.domain f.val.1 t).mpr ⟨?_,h2⟩
      have : (f.val.1,t ∘ Fin.castAdd b) = f.val := Prod.ext rfl hf2.symm
      rw [this]
      exact f.property
    refine ⟨t,?_,rfl⟩
    exact (mem_vf_base_image φ.map S.family.domain hS y t).mpr ⟨⟨_,hmem⟩,hf1,rfl⟩
  case hden =>
    rintro ⟨tv,q,hq⟩
    have hq1 : (φ.map ⟨q.val.1,hS q⟩).val = y := congrArg Prod.fst hq
    have hq2 : q.val.2 = tv := congrArg Prod.snd hq
    subst hq2
    obtain ⟨h1,h2⟩ := (mem_mixed_rv_factor_domain F.family.domain Z.val.underlying.obj.domain q.val.1 q.val.2).mp
      q.property
    have hKmem : (y,q.val.2) ∈ K.family.domain.carrier :=
      (mem_mixed_rv_factor_domain JF.family.domain Z.val.underlying.obj.domain y q.val.2).mpr
        ⟨(mem_vf_base_image φ.map F.family.domain hF y _).mpr ⟨⟨_,h1⟩,hq1,rfl⟩,h2⟩
    have hJFmem : (y,q.val.2 ∘ τ) ∈ JF.family.domain.carrier :=
      ((mem_mixed_rv_factor_domain JF.family.domain Z.val.underlying.obj.domain y q.val.2).mp hKmem).1
    have eK := weighted_zero_product_density JF.family Z.val ⟨(y,q.val.2),hKmem⟩
    have eS := weighted_zero_product_density F.family Z.val q
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
