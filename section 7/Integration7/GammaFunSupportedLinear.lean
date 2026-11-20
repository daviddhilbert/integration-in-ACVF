import Integration7.GammaFunJacobianZeroZero

/-! **Gamma-named linear Proposition 7.12.** Gamma Jacobian transforms of supported graded
Gamma-named functions are `HK.GammaNamedRVSemiring`-linear, the supported graded integral is
linear, and the integral over the target of the Jacobian transform equals the integral over the
source as linear maps. No hypothesis puts common names into `C.base`. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open IntegrationInACVF.Section5 IntegrationInACVF.Section6
open scoped DirectSum

namespace IntegrationInACVF.Section7.GammaFun
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n : ℕ}
variable (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
variable (Ξ : Set (Values.Gamma (M := M))) (hΞ : Cardinal.mk Ξ < C.κ)

set_option quotPrecheck false
local notation "𝔅" => gammaNamedBase C Ξ
local notation "𝔇" => gammaNamedCodeContext C Ξ hΞ
local notation "𝔖" => ((gammaNamedCodeContext C Ξ hΞ).base : Set M)

/-- The Gamma Jacobian transform of a supported component presentation. -/
def presJac {X Y : GammaVFSet C Ξ hΞ n} (φ : GammaVFBijection C Ξ hΞ X Y) :
    {j : ℕ} → (F : Pres C Ξ hΞ n j) → PresSupported C Ξ hΞ F X → Pres C Ξ hΞ n j
  | 0, F, h => (F : ZeroPresentation C Ξ hΞ n).jacobian hc C Ξ hΞ φ h
  | _+1, F, h => (F : Presentation C Ξ hΞ n _).jacobian hc C Ξ hΞ φ h

theorem pres_jac_supported {X Y : GammaVFSet C Ξ hΞ n} (φ : GammaVFBijection C Ξ hΞ X Y) {j : ℕ}
    (F : Pres C Ξ hΞ n j) (h : PresSupported C Ξ hΞ F X) : PresSupported C Ξ hΞ (presJac hc C Ξ hΞ φ F h) Y := by
  cases j with
  | zero => exact zero_presentation_jacobian_supported hc C Ξ hΞ _ φ h
  | succ k => exact presentation_jacobian_supported hc C Ξ hΞ _ φ h

/-- The supported Gamma Jacobian transform on a graded component. -/
def suppJac {X Y : GammaVFSet C Ξ hΞ n} (φ : GammaVFBijection C Ξ hΞ X Y) :
    (j : ℕ) → SuppComp hc C Ξ hΞ X j →+ SuppComp hc C Ξ hΞ Y j
  | 0 => supportedZeroJacobianAddHom hc C Ξ hΞ φ
  | k+1 => supportedJacobianAddHom hc C Ξ hΞ φ k

theorem supp_jac_mk {X Y : GammaVFSet C Ξ hΞ n} (φ : GammaVFBijection C Ξ hΞ X Y) {j : ℕ} (F : Pres C Ξ hΞ n j)
    (h : PresSupported C Ξ hΞ F X) :
    suppJac hc C Ξ hΞ φ j (suppMk hc C Ξ hΞ X F h) =
      suppMk hc C Ξ hΞ Y (presJac hc C Ξ hΞ φ F h) (pres_jac_supported hc C Ξ hΞ φ F h) := by
  cases j <;> rfl

theorem presentation_reindex_jacobian {X Y : GammaVFSet C Ξ hΞ n} {k k' : ℕ} (h : k = k')
    (F : Presentation C Ξ hΞ n k) (φ : GammaVFBijection C Ξ hΞ X Y) (hF : F.SupportedIn C Ξ hΞ X)
    (hF' : (F.reindex C Ξ hΞ h).SupportedIn C Ξ hΞ X) :
    (F.reindex C Ξ hΞ h).jacobian hc C Ξ hΞ φ hF' = (F.jacobian hc C Ξ hΞ φ hF).reindex C Ξ hΞ h := by
  subst h
  rfl

theorem ae_mk_reindex_eq {k k' : ℕ} (h : k = k') {P Q : Presentation C Ξ hΞ n k} (hPQ : AEEquivalent hc C Ξ hΞ P Q) :
    aeMk hc C Ξ hΞ (j := k'+1) (P.reindex C Ξ hΞ h) = aeMk hc C Ξ hΞ (j := k'+1) (Q.reindex C Ξ hΞ h) := by
  subst h
  exact Quotient.sound hPQ

/-- **Jacobian transforms commute with coefficient actions** (almost everywhere, all degrees). -/
theorem pres_jac_act {X Y : GammaVFSet C Ξ hΞ n} (φ : GammaVFBijection C Ξ hΞ X Y) {i j : ℕ}
    (u : HK.GammaRVObjects 𝔅 𝔖 i) (F : Pres C Ξ hΞ n j) (hF : PresSupported C Ξ hΞ F X) :
    aeMk hc C Ξ hΞ (presJac hc C Ξ hΞ φ (presAct hc C Ξ hΞ u F) (pres_act_supported hc C Ξ hΞ u F hF)) =
      aeMk hc C Ξ hΞ (presAct hc C Ξ hΞ u (presJac hc C Ξ hΞ φ F hF)) := by
  cases i with
  | zero =>
    cases j with
    | zero => exact Quotient.sound (zero_presentation_zero_coef_jacobian hc C Ξ hΞ _ _ φ hF)
    | succ k =>
      let F' : Presentation C Ξ hΞ n k := F
      let Z : HK.GammaZeroRVObjects 𝔅 𝔖 := ⟨u.val,(HK.RVVolumeObject.Gamma.zero_iff _).mp u.property⟩
      change aeMk hc C Ξ hΞ (j := (0+k)+1) (((F'.zeroCoef hc C Ξ hΞ Z).reindex C Ξ hΞ (Nat.zero_add k).symm).jacobian
          hc C Ξ hΞ φ _) =
        aeMk hc C Ξ hΞ (j := (0+k)+1) (((F'.jacobian hc C Ξ hΞ φ hF).zeroCoef hc C Ξ hΞ Z).reindex C Ξ hΞ
          (Nat.zero_add k).symm)
      rw [presentation_reindex_jacobian hc C Ξ hΞ (Nat.zero_add k).symm _ φ
        (presentation_zero_coef_supported hc C Ξ hΞ Z F' hF)]
      exact ae_mk_reindex_eq hc C Ξ hΞ _ (presentation_zero_coef_jacobian hc C Ξ hΞ Z F' φ hF)
  | succ p =>
    cases j with
    | zero => exact Quotient.sound (zero_presentation_pos_coef_jacobian hc C Ξ hΞ _ _ φ hF)
    | succ k => exact Quotient.sound (presentation_left_product_jacobian hc C Ξ hΞ _ _ φ hF)

/-- **The supported Jacobian transform is linear on homogeneous elements.** -/
theorem supp_jac_act {X Y : GammaVFSet C Ξ hΞ n} (φ : GammaVFBijection C Ξ hΞ X Y) {i j : ℕ}
    (a : HK.GammaNamedRVClasses hc C Ξ hΞ i) (f : SuppComp hc C Ξ hΞ X j) :
    suppJac hc C Ξ hΞ φ (i+j) (suppAct hc C Ξ hΞ X a f) = suppAct hc C Ξ hΞ Y a (suppJac hc C Ξ hΞ φ j f) := by
  apply supp_forget_injective hc C Ξ hΞ Y
  rw [supp_forget_act]
  unfold suppAct
  rw [supp_jac_mk,supp_forget_mk]
  conv_rhs => rw [← supp_mk_rep hc C Ξ hΞ X f,supp_jac_mk,supp_forget_mk,← HK.gammaNamedRVRep_class hc C Ξ hΞ a,aeAct_mk]
  exact pres_jac_act hc C Ξ hΞ φ _ _ _

/-! ### Graded linear maps -/

/-- **Forgetting supports, as a linear map.** -/
def suppForgetLinearMap (X : GammaVFSet C Ξ hΞ n) :
    SupportedGradedFunction hc C Ξ hΞ X →ₗ[HK.GammaNamedRVSemiring hc C Ξ hΞ] GradedAEFunction hc C Ξ hΞ n where
  toAddHom := (DirectSum.toAddMonoid fun j => (DirectSum.of (AEComp hc C Ξ hΞ n) j).comp
    (suppForget hc C Ξ hΞ X j)).toAddHom
  map_smul' r x := by
    let F := DirectSum.toAddMonoid fun j => (DirectSum.of (AEComp hc C Ξ hΞ n) j).comp (suppForget hc C Ξ hΞ X j)
    change F (r • x) = r • F x
    induction r using DirectSum.induction_on with
    | zero => simp only [zero_smul,map_zero]
    | of i a =>
      induction x using DirectSum.induction_on with
      | zero => simp only [smul_zero,map_zero]
      | of j f =>
        rw [supported_graded_action_of]
        simp only [F,DirectSum.toAddMonoid_of,AddMonoidHom.comp_apply]
        rw [supp_forget_act,graded_ae_action_of]
      | add f g hf hg => rw [smul_add,map_add,map_add,smul_add,hf,hg]
    | add r s hr hs => rw [add_smul,map_add,hr,hs,add_smul]

/-- **The supported graded Gamma Jacobian transform, as a linear map.** -/
def suppJacLinearMap {X Y : GammaVFSet C Ξ hΞ n} (φ : GammaVFBijection C Ξ hΞ X Y) :
    SupportedGradedFunction hc C Ξ hΞ X →ₗ[HK.GammaNamedRVSemiring hc C Ξ hΞ] SupportedGradedFunction hc C Ξ hΞ Y where
  toAddHom := (DirectSum.map (suppJac hc C Ξ hΞ φ)).toAddHom
  map_smul' r x := by
    let F := DirectSum.map (suppJac hc C Ξ hΞ φ)
    change F (r • x) = r • F x
    induction r using DirectSum.induction_on with
    | zero => simp only [zero_smul,map_zero]
    | of i a =>
      induction x using DirectSum.induction_on with
      | zero => simp only [smul_zero,map_zero]
      | of j f =>
        rw [supported_graded_action_of]
        simp only [F,DirectSum.map_of]
        rw [supp_jac_act,supported_graded_action_of]
      | add f g hf hg => rw [smul_add,map_add,map_add,smul_add,hf,hg]
    | add r s hr hs => rw [add_smul,map_add,hr,hs,add_smul]

variable (hGenerated : VFGammaGeneratedBase (gammaNamedBase C Ξ))
variable (γ : Values.Gamma (M := M)) (hγ : γ ∈ Ξ) (hγ1 : 1 < γ)

/-- **The supported graded Gamma-named integral, as a linear map.** -/
def suppIntegralLinearMap (X : GammaVFSet C Ξ hΞ n) :
    SupportedGradedFunction hc C Ξ hΞ X →ₗ[HK.GammaNamedRVSemiring hc C Ξ hΞ] HK.GammaNamedRVSemiring hc C Ξ hΞ :=
  (gradedIntegralLinearMap hc C Ξ hΞ hGenerated γ hγ hγ1 n).comp (suppForgetLinearMap hc C Ξ hΞ X)

include hγ hγ1 in
/-- **Gamma-named Proposition 7.12 (linear form).** For a Gamma VF bijection `φ : X → Y`, the
supported graded integral over `Y` composed with the linear Jacobian transform equals the supported
graded integral over `X`, as `HK.GammaNamedRVSemiring`-linear maps. -/
theorem gamma_named_linear_proposition_7_12 {X Y : GammaVFSet C Ξ hΞ n} (φ : GammaVFBijection C Ξ hΞ X Y) :
    (suppIntegralLinearMap hc C Ξ hΞ hGenerated γ hγ hγ1 Y).comp (suppJacLinearMap hc C Ξ hΞ φ) =
      suppIntegralLinearMap hc C Ξ hΞ hGenerated γ hγ hγ1 X := by
  apply LinearMap.ext
  intro x
  induction x using DirectSum.induction_on with
  | zero => simp only [map_zero]
  | of j f =>
    change gradedIntegralAddHom hc C Ξ hΞ hGenerated γ hγ hγ1 n
        ((DirectSum.toAddMonoid fun j => (DirectSum.of (AEComp hc C Ξ hΞ n) j).comp (suppForget hc C Ξ hΞ Y j))
          (DirectSum.map (suppJac hc C Ξ hΞ φ) (DirectSum.of (SuppComp hc C Ξ hΞ X) j f))) =
      gradedIntegralAddHom hc C Ξ hΞ hGenerated γ hγ hγ1 n
        ((DirectSum.toAddMonoid fun j => (DirectSum.of (AEComp hc C Ξ hΞ n) j).comp (suppForget hc C Ξ hΞ X j))
          (DirectSum.of (SuppComp hc C Ξ hΞ X) j f))
    rw [DirectSum.map_of]
    simp only [DirectSum.toAddMonoid_of,AddMonoidHom.comp_apply]
    rw [graded_integral_of,graded_integral_of]
    cases j with
    | zero => exact gamma_named_proposition_7_12_zero hc C Ξ hΞ hGenerated γ hγ hγ1 φ f
    | succ k => exact gamma_named_proposition_7_12 hc C Ξ hΞ hGenerated γ hγ hγ1 φ f
  | add x y hx hy => rw [map_add,map_add,hx,hy]

end IntegrationInACVF.Section7.GammaFun
