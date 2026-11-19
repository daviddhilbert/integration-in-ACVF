import Integration7.GammaFunZeroJacobians

/-! Gamma-named supported weighted degree-zero functions, their Gamma Jacobian transforms and
coordinate permutations, and zero-degree prefix and coordinate integrals with Fubini. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open IntegrationInACVF.Section5 IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7.GammaFun
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n p a b k : ℕ}
variable (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
variable (Ξ : Set (Values.Gamma (M := M))) (hΞ : Cardinal.mk Ξ < C.κ)
variable (hGenerated : VFGammaGeneratedBase (gammaNamedBase C Ξ))

/-- Zero presentations supported in a Gamma VF set. -/
def SupportedZeroPresentation (X : GammaVFSet C Ξ hΞ n) :=
  {F : ZeroPresentation C Ξ hΞ n // F.SupportedIn C Ξ hΞ X}

def supportedZeroSetoid (X : GammaVFSet C Ξ hΞ n) : Setoid (SupportedZeroPresentation C Ξ hΞ X) where
  r F H := ZeroAEEquivalent C Ξ hΞ F.val H.val
  iseqv := ⟨fun F => (zeroAESetoid hc C Ξ hΞ n).iseqv.refl F.val,
    fun h => (zeroAESetoid hc C Ξ hΞ n).iseqv.symm h,
    fun h g => (zeroAESetoid hc C Ξ hΞ n).iseqv.trans h g⟩

/-- **Gamma-named supported weighted degree-zero functions.** -/
abbrev SupportedAEZeroFunction (X : GammaVFSet C Ξ hΞ n) := Quotient (supportedZeroSetoid hc C Ξ hΞ X)

def supportedZeroForget (X : GammaVFSet C Ξ hΞ n) : SupportedAEZeroFunction hc C Ξ hΞ X → AEZeroFunction hc C Ξ hΞ n :=
  Quotient.map (fun F => F.val) (fun _ _ h => h)

theorem supported_zero_forget_injective (X : GammaVFSet C Ξ hΞ n) :
    Function.Injective (supportedZeroForget hc C Ξ hΞ X) := by
  intro u v
  induction u using Quotient.inductionOn with
  | h F =>
    induction v using Quotient.inductionOn with
    | h H =>
      intro h
      have h' : (Quotient.mk _ F.val : AEZeroFunction hc C Ξ hΞ n) = Quotient.mk _ H.val := h
      exact Quotient.sound (show ZeroAEEquivalent C Ξ hΞ F.val H.val from Quotient.exact h')

/-- **The Gamma Jacobian transform of supported weighted degree-zero functions.** -/
def supportedZeroJacobian {X Y : GammaVFSet C Ξ hΞ n} (φ : GammaVFBijection C Ξ hΞ X Y) :
    SupportedAEZeroFunction hc C Ξ hΞ X → SupportedAEZeroFunction hc C Ξ hΞ Y :=
  Quotient.map (fun F => ⟨F.val.jacobian hc C Ξ hΞ φ F.property,
      zero_presentation_jacobian_supported hc C Ξ hΞ F.val φ F.property⟩)
    (fun F H h => zero_presentation_jacobian_ae hc C Ξ hΞ F.val H.val φ F.property H.property h)

variable (γ : Values.Gamma (M := M)) (hγ : γ ∈ Ξ) (hγ1 : 1 < γ)

include hγ hγ1 in
/-- **Gamma change of variables on supported weighted degree-zero functions.** -/
theorem supported_zero_jacobian_integral {X Y : GammaVFSet C Ξ hΞ n} (φ : GammaVFBijection C Ξ hΞ X Y)
    (f : SupportedAEZeroFunction hc C Ξ hΞ X) :
    aeZeroIntegral hc C Ξ hΞ hGenerated γ hγ hγ1
        (supportedZeroForget hc C Ξ hΞ Y (supportedZeroJacobian hc C Ξ hΞ φ f)) =
      aeZeroIntegral hc C Ξ hΞ hGenerated γ hγ hγ1 (supportedZeroForget hc C Ξ hΞ X f) := by
  induction f using Quotient.inductionOn with
  | h F => exact zero_presentation_jacobian_integral hc C Ξ hΞ hGenerated γ hγ hγ1 F.val φ F.property

theorem zero_presentation_supported_univ (F : ZeroPresentation C Ξ hΞ n) :
    F.SupportedIn C Ξ hΞ (GammaVFSet.univ C Ξ hΞ n) := fun _ => Set.mem_univ _

def supportedZeroUnivEquiv (n : ℕ) :
    SupportedAEZeroFunction hc C Ξ hΞ (GammaVFSet.univ C Ξ hΞ n) ≃ AEZeroFunction hc C Ξ hΞ n :=
  Equiv.ofBijective (supportedZeroForget hc C Ξ hΞ _) ⟨supported_zero_forget_injective hc C Ξ hΞ _,by
    intro f
    induction f using Quotient.inductionOn with
    | h F => exact ⟨Quotient.mk _ ⟨F,zero_presentation_supported_univ C Ξ hΞ F⟩,rfl⟩⟩

/-- **Gamma coordinate permutation of weighted degree-zero functions** (with its Jacobian sign). -/
def aeZeroPermute (σ : Equiv.Perm (Fin (n+1))) : AEZeroFunction hc C Ξ hΞ n → AEZeroFunction hc C Ξ hΞ n :=
  fun f => supportedZeroForget hc C Ξ hΞ _ (supportedZeroJacobian hc C Ξ hΞ (coordinatePermutation C Ξ hΞ σ)
    ((supportedZeroUnivEquiv hc C Ξ hΞ n).symm f))

include hγ hγ1 in
theorem ae_zero_permute_integral (σ : Equiv.Perm (Fin (n+1))) (f : AEZeroFunction hc C Ξ hΞ n) :
    aeZeroIntegral hc C Ξ hΞ hGenerated γ hγ hγ1 (aeZeroPermute hc C Ξ hΞ σ f) =
      aeZeroIntegral hc C Ξ hΞ hGenerated γ hγ hγ1 f := by
  have h := supported_zero_jacobian_integral hc C Ξ hΞ hGenerated γ hγ hγ1 (coordinatePermutation C Ξ hΞ σ)
    ((supportedZeroUnivEquiv hc C Ξ hΞ n).symm f)
  refine h.trans ?_
  exact congrArg _ ((supportedZeroUnivEquiv hc C Ξ hΞ n).apply_symm_apply f)

/-- **Gamma prefix integrals of weighted degree-zero functions**: integrate out the first `r+1`
VF coordinates. -/
def aeZeroPrefixIntegral (r p : ℕ) (f : AEZeroFunction hc C Ξ hΞ ((p+r)+1)) :
    AEFunction hc C Ξ hΞ p (appendVolumeDegree r 0) :=
  aePrefixIntegral hc C Ξ hΞ hGenerated γ hγ hγ1 r p 0 (aeZeroHeadIntegral (n := p+r) hc C Ξ hΞ hGenerated γ hγ hγ1 f)

/-- **Gamma prefix Fubini for weighted degree-zero functions.** -/
theorem ae_zero_prefix_fubini (r p : ℕ) (f : AEZeroFunction hc C Ξ hΞ ((p+r)+1)) :
    HEq (aeAppendedIntegral hc C Ξ hΞ hGenerated γ hγ hγ1 (aeZeroPrefixIntegral hc C Ξ hΞ hGenerated γ hγ hγ1 r p f))
      (aeZeroIntegral hc C Ξ hΞ hGenerated γ hγ hγ1 f) :=
  (ae_prefix_fubini hc C Ξ hΞ hGenerated γ hγ hγ1 r p 0 _).trans
    (ae_zero_head_fubini (n := p+r) hc C Ξ hΞ hGenerated γ hγ hγ1 f)

/-- Reindex the VF arity of weighted degree-zero functions along an equality. -/
def aeZeroReindexBase {a b : ℕ} (h : a = b) : AEZeroFunction hc C Ξ hΞ b → AEZeroFunction hc C Ξ hΞ a :=
  fun f => h ▸ f

theorem ae_zero_reindex_base_integral {a b : ℕ} (h : a = b) (f : AEZeroFunction hc C Ξ hΞ b) :
    HEq (aeZeroIntegral hc C Ξ hΞ hGenerated γ hγ hγ1 (aeZeroReindexBase hc C Ξ hΞ h f))
      (aeZeroIntegral hc C Ξ hΞ hGenerated γ hγ hγ1 f) := by
  subst h
  rfl

theorem zero_projection_index_eq (E : VFCoordinateProjection (n+1) (p+1)) {r : ℕ} (hr : E.discarded = r+1) :
    (p+r)+1 = n := by
  have h := volume_projection_index_eq E
  omega

/-- **Gamma coordinate integral of a weighted degree-zero function** along a projection discarding
`r+1` coordinates. -/
def aeZeroCoordinateIntegral (E : VFCoordinateProjection (n+1) (p+1)) {r : ℕ} (hr : E.discarded = r+1)
    (f : AEZeroFunction hc C Ξ hΞ n) : AEFunction hc C Ξ hΞ p (appendVolumeDegree r 0) :=
  aeZeroPrefixIntegral hc C Ξ hΞ hGenerated γ hγ hγ1 r p
    (aeZeroReindexBase hc C Ξ hΞ (show (p+r)+1 = p+E.discarded by rw [hr]; rfl)
      (aeZeroPermute hc C Ξ hΞ (volumeProjectionFibreOrder E)
        (aeZeroReindexBase hc C Ξ hΞ (volume_projection_index_eq E) f)))

/-- **Gamma Fubini for weighted degree-zero functions.** -/
theorem ae_zero_coordinate_fubini (E : VFCoordinateProjection (n+1) (p+1)) {r : ℕ} (hr : E.discarded = r+1)
    (f : AEZeroFunction hc C Ξ hΞ n) :
    HEq (aeAppendedIntegral hc C Ξ hΞ hGenerated γ hγ hγ1
        (aeZeroCoordinateIntegral hc C Ξ hΞ hGenerated γ hγ hγ1 E hr f))
      (aeZeroIntegral hc C Ξ hΞ hGenerated γ hγ hγ1 f) :=
  (ae_zero_prefix_fubini hc C Ξ hΞ hGenerated γ hγ hγ1 r p _).trans
    ((ae_zero_reindex_base_integral hc C Ξ hΞ hGenerated γ hγ hγ1 _ _).trans
      ((heq_of_eq (ae_zero_permute_integral hc C Ξ hΞ hGenerated γ hγ hγ1 _ _)).trans
        (ae_zero_reindex_base_integral hc C Ξ hΞ hGenerated γ hγ hγ1 _ f)))

end IntegrationInACVF.Section7.GammaFun
