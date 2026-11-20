import Integration7.GammaFunJacobianPosZero

/-! **Supported Gamma-named function modules.** Coefficient actions preserve supports, so the
supported graded Gamma-named functions on a Gamma VF set form a module over
`HK.GammaNamedRVSemiring`, and forgetting the support is linear. -/
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

theorem zero_presentation_zero_coef_supported {X : GammaVFSet C Ξ hΞ n} (Z : HK.GammaZeroRVObjects 𝔅 𝔖)
    (F : ZeroPresentation C Ξ hΞ n) (hF : F.SupportedIn C Ξ hΞ X) :
    (F.zeroCoef hc C Ξ hΞ Z).SupportedIn C Ξ hΞ X := fun q =>
  hF ⟨_,((mem_mixed_rv_factor_domain F.family.domain Z.val.underlying.obj.domain q.val.1 q.val.2).mp q.property).1⟩


/-- Support of a component presentation. -/
def PresSupported : {j : ℕ} → Pres C Ξ hΞ n j → GammaVFSet C Ξ hΞ n → Prop
  | 0, F, X => (F : ZeroPresentation C Ξ hΞ n).SupportedIn C Ξ hΞ X
  | _+1, F, X => (F : Presentation C Ξ hΞ n _).SupportedIn C Ξ hΞ X

theorem presentation_reindex_supported {X : GammaVFSet C Ξ hΞ n} {k k' : ℕ} (h : k = k')
    (F : Presentation C Ξ hΞ n k) (hF : F.SupportedIn C Ξ hΞ X) : (F.reindex C Ξ hΞ h).SupportedIn C Ξ hΞ X := by
  subst h
  exact hF

/-- **Coefficient actions preserve supports.** -/
theorem pres_act_supported {X : GammaVFSet C Ξ hΞ n} {i j : ℕ} (u : HK.GammaRVObjects 𝔅 𝔖 i)
    (F : Pres C Ξ hΞ n j) (hF : PresSupported C Ξ hΞ F X) : PresSupported C Ξ hΞ (presAct hc C Ξ hΞ u F) X := by
  cases i with
  | zero =>
    cases j with
    | zero => exact zero_presentation_zero_coef_supported hc C Ξ hΞ _ (F : ZeroPresentation C Ξ hΞ n) hF
    | succ k =>
      have h := presentation_zero_coef_supported hc C Ξ hΞ ⟨u.val,(HK.RVVolumeObject.Gamma.zero_iff _).mp u.property⟩
        (F : Presentation C Ξ hΞ n k) hF
      exact presentation_reindex_supported C Ξ hΞ _ _ h
  | succ p =>
    cases j with
    | zero => exact zero_presentation_pos_coef_supported hc C Ξ hΞ _ (F : ZeroPresentation C Ξ hΞ n) hF
    | succ k => exact presentation_left_product_supported hc C Ξ hΞ _ (F : Presentation C Ξ hΞ n k) hF

/-- Supported graded components. -/
abbrev SuppComp (X : GammaVFSet C Ξ hΞ n) : ℕ → Type
  | 0 => SupportedAEZeroFunction hc C Ξ hΞ X
  | k+1 => SupportedAEFunction hc C Ξ hΞ X k

instance suppCompAddCommMonoid (X : GammaVFSet C Ξ hΞ n) : (j : ℕ) → AddCommMonoid (SuppComp hc C Ξ hΞ X j)
  | 0 => inferInstanceAs (AddCommMonoid (SupportedAEZeroFunction hc C Ξ hΞ X))
  | k+1 => inferInstanceAs (AddCommMonoid (SupportedAEFunction hc C Ξ hΞ X k))

/-- Forgetting the support, componentwise. -/
def suppForget (X : GammaVFSet C Ξ hΞ n) : (j : ℕ) → SuppComp hc C Ξ hΞ X j →+ AEComp hc C Ξ hΞ n j
  | 0 => supportedZeroForgetAddHom hc C Ξ hΞ X
  | k+1 => supportedForgetAddHom hc C Ξ hΞ X k

theorem supp_forget_injective (X : GammaVFSet C Ξ hΞ n) (j : ℕ) : Function.Injective (suppForget hc C Ξ hΞ X j) := by
  cases j with
  | zero => exact supported_zero_forget_injective hc C Ξ hΞ X
  | succ k => exact supported_forget_injective hc C Ξ hΞ X

theorem supp_forget_heq_injective (X : GammaVFSet C Ξ hΞ n) {j j' : ℕ} (h : j = j') {x : SuppComp hc C Ξ hΞ X j}
    {x' : SuppComp hc C Ξ hΞ X j'} (hx : HEq (suppForget hc C Ξ hΞ X j x) (suppForget hc C Ξ hΞ X j' x')) : HEq x x' := by
  subst h
  exact heq_of_eq (supp_forget_injective hc C Ξ hΞ X j (eq_of_heq hx))

/-- A supported representative. -/
def suppRep (X : GammaVFSet C Ξ hΞ n) : {j : ℕ} → SuppComp hc C Ξ hΞ X j →
    {F : Pres C Ξ hΞ n j // PresSupported C Ξ hΞ F X}
  | 0, f => ⟨(Quotient.out f).val,(Quotient.out f).property⟩
  | _+1, f => ⟨(Quotient.out f).val,(Quotient.out f).property⟩

/-- The supported class of a supported presentation. -/
def suppMk (X : GammaVFSet C Ξ hΞ n) : {j : ℕ} → (F : Pres C Ξ hΞ n j) → PresSupported C Ξ hΞ F X →
    SuppComp hc C Ξ hΞ X j
  | 0, F, h => Quotient.mk _ ⟨F,h⟩
  | _+1, F, h => Quotient.mk _ ⟨F,h⟩

theorem supp_forget_mk (X : GammaVFSet C Ξ hΞ n) {j : ℕ} (F : Pres C Ξ hΞ n j) (h : PresSupported C Ξ hΞ F X) :
    suppForget hc C Ξ hΞ X j (suppMk hc C Ξ hΞ X F h) = aeMk hc C Ξ hΞ F := by
  cases j <;> rfl

theorem supp_mk_rep (X : GammaVFSet C Ξ hΞ n) {j : ℕ} (f : SuppComp hc C Ξ hΞ X j) :
    suppMk hc C Ξ hΞ X (suppRep hc C Ξ hΞ X f).val (suppRep hc C Ξ hΞ X f).property = f := by
  cases j with
  | zero => exact Quotient.out_eq f
  | succ k => exact Quotient.out_eq f

theorem supp_forget_rep (X : GammaVFSet C Ξ hΞ n) {j : ℕ} (f : SuppComp hc C Ξ hΞ X j) :
    suppForget hc C Ξ hΞ X j f = aeMk hc C Ξ hΞ (suppRep hc C Ξ hΞ X f).val := by
  conv_lhs => rw [← supp_mk_rep hc C Ξ hΞ X f]
  exact supp_forget_mk hc C Ξ hΞ X _ _

/-- **The coefficient action on supported functions.** -/
def suppAct (X : GammaVFSet C Ξ hΞ n) {i j : ℕ} (a : HK.GammaNamedRVClasses hc C Ξ hΞ i)
    (f : SuppComp hc C Ξ hΞ X j) : SuppComp hc C Ξ hΞ X (i+j) :=
  suppMk hc C Ξ hΞ X (presAct hc C Ξ hΞ (HK.gammaNamedRVRep hc C Ξ hΞ a) (suppRep hc C Ξ hΞ X f).val)
    (pres_act_supported hc C Ξ hΞ _ _ (suppRep hc C Ξ hΞ X f).property)

theorem supp_forget_act (X : GammaVFSet C Ξ hΞ n) {i j : ℕ} (a : HK.GammaNamedRVClasses hc C Ξ hΞ i)
    (f : SuppComp hc C Ξ hΞ X j) :
    suppForget hc C Ξ hΞ X (i+j) (suppAct hc C Ξ hΞ X a f) = aeAct hc C Ξ hΞ a (suppForget hc C Ξ hΞ X j f) := by
  rw [supp_forget_rep hc C Ξ hΞ X f]
  unfold suppAct
  rw [supp_forget_mk]
  conv_rhs => rw [← HK.gammaNamedRVRep_class hc C Ξ hΞ a]
  rw [aeAct_mk]

/-- **The biadditive supported coefficient action.** -/
def suppActBiadditive (X : GammaVFSet C Ξ hΞ n) (i j : ℕ) :
    HK.GammaNamedRVClasses hc C Ξ hΞ i →+ (SuppComp hc C Ξ hΞ X j →+ SuppComp hc C Ξ hΞ X (i+j)) where
  toFun a :=
    { toFun := suppAct hc C Ξ hΞ X a
      map_zero' := supp_forget_injective hc C Ξ hΞ X _ (by
        rw [supp_forget_act,map_zero,map_zero,aeAct_zero_right])
      map_add' := fun f g => supp_forget_injective hc C Ξ hΞ X _ (by
        rw [supp_forget_act,map_add,map_add,supp_forget_act,supp_forget_act,aeAct_add_right]) }
  map_zero' := by
    ext f
    exact supp_forget_injective hc C Ξ hΞ X _ (by
      change suppForget hc C Ξ hΞ X (i+j) (suppAct hc C Ξ hΞ X 0 f) = suppForget hc C Ξ hΞ X (i+j) 0
      rw [supp_forget_act,map_zero,aeAct_zero_left])
  map_add' a b := by
    ext f
    exact supp_forget_injective hc C Ξ hΞ X _ (by
      change suppForget hc C Ξ hΞ X (i+j) (suppAct hc C Ξ hΞ X (a+b) f) =
        suppForget hc C Ξ hΞ X (i+j) (suppAct hc C Ξ hΞ X a f + suppAct hc C Ξ hΞ X b f)
      rw [supp_forget_act,map_add,supp_forget_act,supp_forget_act,aeAct_add_left])

/-- **The graded action on supported functions.** -/
def suppGradedAction (X : GammaVFSet C Ξ hΞ n) :
    GradedSemiringAction (HK.GammaNamedRVClasses hc C Ξ hΞ) (SuppComp hc C Ξ hΞ X) where
  act := suppActBiadditive hc C Ξ hΞ X
  one_act j f := supp_forget_heq_injective hc C Ξ hΞ X (Nat.zero_add j) (by
    change HEq (suppForget hc C Ξ hΞ X (0+j) (suppAct hc C Ξ hΞ X GradedMonoid.GOne.one f)) (suppForget hc C Ξ hΞ X j f)
    rw [supp_forget_act]
    exact aeAct_one hc C Ξ hΞ _)
  mul_act i j k a b f := supp_forget_heq_injective hc C Ξ hΞ X (Nat.add_assoc i j k) (by
    change HEq (suppForget hc C Ξ hΞ X ((i+j)+k) (suppAct hc C Ξ hΞ X (GradedMonoid.GMul.mul a b) f))
      (suppForget hc C Ξ hΞ X (i+(j+k)) (suppAct hc C Ξ hΞ X a (suppAct hc C Ξ hΞ X b f)))
    rw [supp_forget_act,supp_forget_act,supp_forget_act]
    exact aeAct_assoc hc C Ξ hΞ a b _)

/-- **Supported graded Gamma-named functions.** -/
abbrev SupportedGradedFunction (X : GammaVFSet C Ξ hΞ n) := DirectSum ℕ (SuppComp hc C Ξ hΞ X)

/-- **The `HK.GammaNamedRVSemiring`-module of supported graded Gamma-named functions.** -/
instance supportedGradedFunctionModule (X : GammaVFSet C Ξ hΞ n) :
    Module (HK.GammaNamedRVSemiring hc C Ξ hΞ) (SupportedGradedFunction hc C Ξ hΞ X) :=
  gradedSemiringActionModule (suppGradedAction hc C Ξ hΞ X)

theorem supported_graded_action_of (X : GammaVFSet C Ξ hΞ n) {i j : ℕ} (a : HK.GammaNamedRVClasses hc C Ξ hΞ i)
    (f : SuppComp hc C Ξ hΞ X j) :
    DirectSum.of (HK.GammaNamedRVClasses hc C Ξ hΞ) i a • DirectSum.of (SuppComp hc C Ξ hΞ X) j f =
      DirectSum.of (SuppComp hc C Ξ hΞ X) (i+j) (suppAct hc C Ξ hΞ X a f) :=
  graded_semiring_action_of_of (suppGradedAction hc C Ξ hΞ X) i j a f

end IntegrationInACVF.Section7.GammaFun
