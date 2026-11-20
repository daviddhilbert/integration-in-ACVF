import Integration7.GammaFunSupportedModule
import Integration7.GammaFunZeroJacobianCompare

/-! **Jacobian transforms commute with weighted degree-zero coefficients on degree-zero
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

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {B : Base (M := M)} {S : Set M} {C : BaseContext M} {n a : ℕ}

/-- Class equality of Gamma degree-zero objects from a bijective coordinate selection. -/
theorem zero_class_eq_of_select (hc : CanonicalStructure.IsCanonical (M := M)) (X Y : HK.GammaZeroRVObjects B S)
    (σ : Fin Y.val.underlying.obj.arity → Fin X.val.underlying.obj.arity)
    (hmap : ∀ t ∈ X.val.underlying.obj.domain.carrier, t ∘ σ ∈ Y.val.underlying.obj.domain.carrier)
    (hsurj : ∀ s ∈ Y.val.underlying.obj.domain.carrier, ∃ t ∈ X.val.underlying.obj.domain.carrier, t ∘ σ = s)
    (hinj : ∀ t ∈ X.val.underlying.obj.domain.carrier, ∀ t' ∈ X.val.underlying.obj.domain.carrier,
      t ∘ σ = t' ∘ σ → t = t')
    (hden : ∀ t : X.val.underlying.obj.domain, X.val.form.value t = Y.val.form.value ⟨t.val ∘ σ,hmap _ t.property⟩) :
    (Quotient.mk _ X : HK.GammaZeroRVClasses B S) = Quotient.mk _ Y := by
  let f : Map X.val.underlying.obj.domain Y.val.underlying.obj.domain :=
    ((rvCoordinateSelectMap S σ).comp (Map.inclusion (fun _ _ => Set.mem_univ _))).corestrict
      (fun s => hmap s.val s.property)
  have hfv : ∀ s, (f s).val = s.val ∘ σ := fun _ => rfl
  have hf : Function.Bijective f := by
    constructor
    · intro s s' h
      apply Subtype.ext
      exact hinj s.val s.property s'.val s'.property
        ((hfv s).symm.trans ((congrArg (fun w : Y.val.underlying.obj.domain => w.val) h).trans (hfv s')))
    · intro t
      obtain ⟨s,hs,hst⟩ := hsurj t.val t.property
      exact ⟨⟨s,hs⟩,Subtype.ext hst⟩
  exact Quotient.sound ⟨HK.ZeroRVVolumeIso.ofBijection f hf hden,
    gamma_rv_coordinate_map hc _ σ X.property.domain (fun _ => rfl)⟩

theorem zero_prod_zero_density (F : HK.ZeroVFVolumeFamily C n a)
    (Z : HK.ZeroRVVolumeObject (M := M) (C.base : Set M)) (q : (F.prodZero Z).domain) :
    (F.prodZero Z).form.value q =
      F.form.value ⟨_,((mem_mixed_rv_factor_domain F.domain Z.underlying.obj.domain q.val.1 q.val.2).mp q.property).1⟩ *
        Z.form.value ⟨_,((mem_mixed_rv_factor_domain F.domain Z.underlying.obj.domain q.val.1 q.val.2).mp
          q.property).2⟩ := by
  have hv := mixed_rv_factor_unpack_value F.domain Z.underlying.obj.domain q
  change (F.form.prod Z.form).value (mixedRVFactorUnpack F.domain Z.underlying.obj.domain q) = _
  have hu : mixedRVFactorUnpack F.domain Z.underlying.obj.domain q =
      ⟨((q.val.1,q.val.2 ∘ Fin.castAdd Z.underlying.obj.arity),q.val.2 ∘ Fin.natAdd a),
        ((mem_mixed_rv_factor_domain F.domain Z.underlying.obj.domain q.val.1 q.val.2).mp q.property).1,
        ((mem_mixed_rv_factor_domain F.domain Z.underlying.obj.domain q.val.1 q.val.2).mp q.property).2⟩ :=
    Subtype.ext hv
  rw [hu]
  rfl

end IntegrationInACVF.Section7

namespace IntegrationInACVF.Section7.GammaFun
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n : ℕ}
variable (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
variable (Ξ : Set (Values.Gamma (M := M))) (hΞ : Cardinal.mk Ξ < C.κ)

set_option quotPrecheck false
local notation "𝔅" => gammaNamedBase C Ξ
local notation "𝔇" => gammaNamedCodeContext C Ξ hΞ
local notation "𝔖" => ((gammaNamedCodeContext C Ξ hΞ).base : Set M)

set_option maxHeartbeats 6400000 in
/-- **Jacobian transforms commute with weighted degree-zero coefficients on degree-zero presentations.** -/
theorem zero_presentation_zero_coef_jacobian {X Y : GammaVFSet C Ξ hΞ n} (Z : HK.GammaZeroRVObjects 𝔅 𝔖)
    (F : ZeroPresentation C Ξ hΞ n) (φ : GammaVFBijection C Ξ hΞ X Y) (hF : F.SupportedIn C Ξ hΞ X) :
    ZeroAEEquivalent C Ξ hΞ
      ((F.zeroCoef hc C Ξ hΞ Z).jacobian hc C Ξ hΞ φ (zero_presentation_zero_coef_supported hc C Ξ hΞ Z F hF))
      ((F.jacobian hc C Ξ hΞ φ hF).zeroCoef hc C Ξ hΞ Z) := by
  let S := F.zeroCoef hc C Ξ hΞ Z
  have hS := zero_presentation_zero_coef_supported hc C Ξ hΞ Z F hF
  let b := Z.val.underlying.obj.arity
  let τ : Fin F.arity → Fin (F.arity+b) := Fin.castAdd b
  have hτ : ∀ q ∈ S.family.domain.carrier, (q.1,q.2 ∘ τ) ∈ F.family.domain.carrier :=
    fun q hq => ((mem_mixed_rv_factor_domain F.family.domain Z.val.underlying.obj.domain q.1 q.2).mp hq).1
  let π := mixedRVSelectMap S.family.domain F.family.domain τ hτ
  let jF := F.jacobianValue hc C Ξ hΞ φ hF
  have hjFΓ := F.jacobianValue_gamma hc C Ξ hΞ φ hF
  have hjF := F.jacobianValue_spec hc C Ξ hΞ φ hF
  let jT := jF.comp π
  have hjTΓ := gamma_value_map_comp_select τ hτ S.gamma.domain jF hjFΓ
  have hjT : IsJacobianValueMap (mixedVFBaseMap φ.map S.family.domain hS).toImage jT :=
    is_jacobian_value_map_comp φ.map hS hF π (fun _ => rfl) (fun q x hx => hτ (x,q.val.2) hx) jF hjF
  have step1 := zero_presentation_jacobian_with_ae hc C Ξ hΞ S φ hS _ jT
    (S.jacobianValue_gamma hc C Ξ hΞ φ hS) hjTΓ (S.jacobianValue_spec hc C Ξ hΞ φ hS) hjT
  refine (zeroAESetoid hc C Ξ hΞ n).iseqv.trans step1 (zero_ae_equivalent_of_rows C Ξ hΞ _ _ (fun y => ?_))
  let JT := S.jacobianWith hc C Ξ hΞ φ hS jT hjTΓ
  let JF := F.jacobian hc C Ξ hΞ φ hF
  let K := JF.zeroCoef hc C Ξ hΞ Z
  refine zero_class_eq_of_select hc ⟨JT.family.rowInContext y,JT.gamma.row y⟩
    ⟨K.family.rowInContext y,K.gamma.row y⟩ id ?hmap ?hsurj (fun _ _ _ _ h => h) ?hden
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
    have eK := zero_prod_zero_density JF.family Z.val ⟨(y,q.val.2),hKmem⟩
    have eS := zero_prod_zero_density F.family Z.val q
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
    change JT.family.form.value ⟨(y,q.val.2),⟨q,hq⟩⟩ = K.family.form.value ⟨(y,q.val.2),hKmem⟩
    refine Eq.trans ?_ eK.symm
    rw [eJT,show S.family.form.value q = _ from eS]
    change _ = JF.family.form.value ⟨(y,q.val.2 ∘ τ),hJFmem⟩ * _
    rw [eJF,div_mul_eq_mul_div]
    rfl

end IntegrationInACVF.Section7.GammaFun
