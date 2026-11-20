import Integration7.GammaFunJacobianLinearity

/-! Comparison of two Gamma Jacobian value maps for degree-zero presentations. -/
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
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {B : Base (M := M)} {S : Set M}

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

end IntegrationInACVF.Section7

namespace IntegrationInACVF.Section7.GammaFun
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n k : ℕ}
variable (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
variable (Ξ : Set (Values.Gamma (M := M))) (hΞ : Cardinal.mk Ξ < C.κ)

set_option quotPrecheck false
local notation "𝔅" => gammaNamedBase C Ξ
local notation "𝔇" => gammaNamedCodeContext C Ξ hΞ
local notation "𝔖" => ((gammaNamedCodeContext C Ξ hΞ).base : Set M)

set_option maxHeartbeats 6400000 in
/-- **Two Gamma Jacobian value maps give almost-everywhere equal Jacobian transforms** (degree zero). -/
theorem zero_presentation_jacobian_with_ae {X Y : GammaVFSet C Ξ hΞ n} (F : ZeroPresentation C Ξ hΞ n)
    (φ : GammaVFBijection C Ξ hΞ X Y) (hF : F.SupportedIn C Ξ hΞ X)
    (j₁ j₂ : Map F.family.domain (DefSet.univ (rawVFSpace (M := M) 1) 𝔖))
    (h₁Γ : GammaGraphDefinable 𝔅 (fun (p : Point (M := M) (n+1) F.arity) (z : Point (M := M) 1 0) =>
      ∃ u : F.family.domain, u.val = p ∧ (j₁ u).val = z.1))
    (h₂Γ : GammaGraphDefinable 𝔅 (fun (p : Point (M := M) (n+1) F.arity) (z : Point (M := M) 1 0) =>
      ∃ u : F.family.domain, u.val = p ∧ (j₂ u).val = z.1))
    (h₁ : IsJacobianValueMap (mixedVFBaseMap φ.map F.family.domain hF).toImage j₁)
    (h₂ : IsJacobianValueMap (mixedVFBaseMap φ.map F.family.domain hF).toImage j₂) :
    ZeroAEEquivalent C Ξ hΞ (F.jacobianWith hc C Ξ hΞ φ hF j₁ h₁Γ) (F.jacobianWith hc C Ξ hΞ φ hF j₂ h₂Γ) := by
  obtain ⟨E,hE,hg⟩ := domain_jacobian_ae_exceptional hc C Ξ hΞ φ F.family.domain F.family.domain
    F.gamma.domain F.gamma.domain hF hF j₁ j₂ h₁Γ h₂Γ h₁ h₂ (GammaVFSet.empty C Ξ hΞ n)
    (gamma_vf_set_empty_small C Ξ hΞ n)
  refine ⟨E,hE,fun y hy => ?_⟩
  refine zero_class_eq_of_select hc ⟨_,(F.jacobianWith hc C Ξ hΞ φ hF j₁ h₁Γ).gamma.row y⟩
    ⟨_,(F.jacobianWith hc C Ξ hΞ φ hF j₂ h₂Γ).gamma.row y⟩ id (fun _ ht => ht) (fun s hs => ⟨s,hs,rfl⟩)
    (fun _ _ _ _ h => h) (fun s => ?_)
  obtain ⟨p,hp⟩ := s.property
  have hJ : (⟨(y,s.val),s.property⟩ : (F.jacobianWith hc C Ξ hΞ φ hF j₁ h₁Γ).family.domain) =
      (mixedVFBaseMap φ.map F.family.domain hF).toImage p := Subtype.ext hp.symm
  change (jacobianTransportedForm (mixedVFBaseMap φ.map F.family.domain hF).toImage _ j₁ F.family.form).value
      ⟨(y,s.val),s.property⟩ =
    (jacobianTransportedForm (mixedVFBaseMap φ.map F.family.domain hF).toImage _ j₂ F.family.form).value
      ⟨(y,s.val),s.property⟩
  rw [hJ]
  exact (jacobian_with_density_eq hc C Ξ hΞ φ F.family.domain hF F.family.form j₁ j₂ E
    (fun y' hy' => ⟨(hg y' hy').2.1,(hg y' hy').2.2⟩) y hy p (congrArg Prod.fst hp)).symm

end IntegrationInACVF.Section7.GammaFun
