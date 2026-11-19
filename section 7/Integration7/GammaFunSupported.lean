import Integration7.GammaFunJacobianAE
import Integration7.PureVFPermutationDimensions

/-! Gamma-named supported almost-everywhere functions, their Gamma Jacobian transforms,
and Gamma coordinate permutations. Jacobian transforms preserve the canonical and the
appended Gamma-named integral. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section9
open SpecialTransformations.Section5 (Point GammaSetDefinable GammaGraphDefinable gammaLogicInput carrier)
open IntegrationInACVF.Section5 IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7.GammaFun
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n a b k : ℕ}
variable (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
variable (Ξ : Set (Values.Gamma (M := M))) (hΞ : Cardinal.mk Ξ < C.κ)
variable (hGenerated : VFGammaGeneratedBase (gammaNamedBase C Ξ))

set_option quotPrecheck false
local notation "𝔅" => gammaNamedBase C Ξ
local notation "𝔇" => gammaNamedCodeContext C Ξ hΞ
local notation "𝔖" => ((gammaNamedCodeContext C Ξ hΞ).base : Set M)

/-- Presentations supported in a Gamma VF set. -/
def SupportedPresentation (X : GammaVFSet C Ξ hΞ n) (k : ℕ) :=
  {F : Presentation C Ξ hΞ n k // F.SupportedIn C Ξ hΞ X}

def supportedSetoid (X : GammaVFSet C Ξ hΞ n) (k : ℕ) : Setoid (SupportedPresentation C Ξ hΞ X k) where
  r F H := AEEquivalent hc C Ξ hΞ F.val H.val
  iseqv := ⟨fun F => (aeSetoid hc C Ξ hΞ n k).iseqv.refl F.val,
    fun h => (aeSetoid hc C Ξ hΞ n k).iseqv.symm h,
    fun h g => (aeSetoid hc C Ξ hΞ n k).iseqv.trans h g⟩

/-- **Gamma-named supported almost-everywhere functions.** -/
abbrev SupportedAEFunction (X : GammaVFSet C Ξ hΞ n) (k : ℕ) := Quotient (supportedSetoid hc C Ξ hΞ X k)

/-- Forget the support. -/
def supportedForget (X : GammaVFSet C Ξ hΞ n) : SupportedAEFunction hc C Ξ hΞ X k → AEFunction hc C Ξ hΞ n k :=
  Quotient.map (fun F => F.val) (fun _ _ h => h)

theorem supported_forget_injective (X : GammaVFSet C Ξ hΞ n) :
    Function.Injective (supportedForget hc C Ξ hΞ X (k := k)) := by
  intro u v
  induction u using Quotient.inductionOn with
  | h F =>
    induction v using Quotient.inductionOn with
    | h H =>
      intro h
      have h' : (Quotient.mk _ F.val : AEFunction hc C Ξ hΞ n k) = Quotient.mk _ H.val := h
      exact Quotient.sound (show AEEquivalent hc C Ξ hΞ F.val H.val from Quotient.exact h')

/-- A Gamma Jacobian transform is supported in the target. -/
theorem presentation_jacobian_supported {X Y : GammaVFSet C Ξ hΞ n} (F : Presentation C Ξ hΞ n k)
    (φ : GammaVFBijection C Ξ hΞ X Y) (hF : F.SupportedIn C Ξ hΞ X) :
    (F.jacobian hc C Ξ hΞ φ hF).SupportedIn C Ξ hΞ Y := by
  rintro ⟨q,u,hu⟩
  have h := congrArg Prod.fst hu
  change (φ.map ⟨u.val.1,hF u⟩).val = q.1 at h
  rw [← h]
  exact (φ.map ⟨u.val.1,hF u⟩).property

/-- **The Gamma Jacobian transform of supported almost-everywhere functions.** -/
def supportedJacobian {X Y : GammaVFSet C Ξ hΞ n} (φ : GammaVFBijection C Ξ hΞ X Y) :
    SupportedAEFunction hc C Ξ hΞ X k → SupportedAEFunction hc C Ξ hΞ Y k :=
  Quotient.map (fun F => ⟨F.val.jacobian hc C Ξ hΞ φ F.property,
      presentation_jacobian_supported hc C Ξ hΞ F.val φ F.property⟩)
    (fun F H h => presentation_jacobian_ae hc C Ξ hΞ F.val H.val φ F.property H.property h)

variable (γ : Values.Gamma (M := M)) (hγ : γ ∈ Ξ) (hγ1 : 1 < γ)

include hγ hγ1 in
/-- **Gamma change of variables on supported functions.** -/
theorem supported_jacobian_integral {X Y : GammaVFSet C Ξ hΞ n} (φ : GammaVFBijection C Ξ hΞ X Y)
    (f : SupportedAEFunction hc C Ξ hΞ X k) :
    aeIntegral hc C Ξ hΞ hGenerated γ hγ hγ1 (supportedForget hc C Ξ hΞ Y (supportedJacobian hc C Ξ hΞ φ f)) =
      aeIntegral hc C Ξ hΞ hGenerated γ hγ hγ1 (supportedForget hc C Ξ hΞ X f) := by
  induction f using Quotient.inductionOn with
  | h F => exact presentation_jacobian_integral hc C Ξ hΞ hGenerated γ hγ hγ1 F.val φ F.property

include hγ hγ1 in
theorem supported_jacobian_appended_integral {X Y : GammaVFSet C Ξ hΞ n} (φ : GammaVFBijection C Ξ hΞ X Y)
    (f : SupportedAEFunction hc C Ξ hΞ X k) :
    aeAppendedIntegral hc C Ξ hΞ hGenerated γ hγ hγ1
        (supportedForget hc C Ξ hΞ Y (supportedJacobian hc C Ξ hΞ φ f)) =
      aeAppendedIntegral hc C Ξ hΞ hGenerated γ hγ hγ1 (supportedForget hc C Ξ hΞ X f) := by
  induction f using Quotient.inductionOn with
  | h F =>
    exact presentation_appended_eq_of_integral hc C Ξ hΞ hGenerated γ hγ hγ1 _ _
      (presentation_jacobian_integral hc C Ξ hΞ hGenerated γ hγ hγ1 F.val φ F.property)

/-! ### Coordinate permutations -/

/-- The whole space `VF^(n+1)` as a Gamma VF set. -/
def GammaVFSet.univ (n : ℕ) : GammaVFSet C Ξ hΞ n :=
  ⟨SpecialTransformations.DefinableGeometry.DefSet.univ _ _,by
    have h := (gammaLogicInput 𝔅).real_set _
      (SpecialTransformations.Section5.setDefinable
        (SpecialTransformations.Section5.PresentedSet.univ
          (SpecialTransformations.Section5.pointSpace (M := M) (n+1) 0) (gammaNamedBase C Ξ).real))
    convert h using 1
    ext p
    exact ⟨fun _ => Set.mem_univ _,fun _ => Set.mem_univ _⟩⟩

/-- Every presentation is supported in the whole space. -/
theorem presentation_supported_univ (F : Presentation C Ξ hΞ n k) :
    F.SupportedIn C Ξ hΞ (GammaVFSet.univ C Ξ hΞ n) := fun _ => Set.mem_univ _

/-- A coordinate permutation as a Gamma VF bijection of the whole space. -/
def coordinatePermutation (σ : Equiv.Perm (Fin (n+1))) :
    GammaVFBijection C Ξ hΞ (GammaVFSet.univ C Ξ hΞ n) (GammaVFSet.univ C Ξ hΞ n) where
  map := pureVFPermutationMap _ σ
  bijective := by
    constructor
    · intro x y h
      apply Subtype.ext
      have he := congrArg Subtype.val h
      change x.val ∘ σ = y.val ∘ σ at he
      funext i
      simpa only [Function.comp_apply,σ.apply_symm_apply] using congrFun he (σ.symm i)
    · intro y
      refine ⟨⟨y.val ∘ σ.symm,Set.mem_univ _⟩,Subtype.ext ?_⟩
      funext i
      exact congrArg y.val (σ.symm_apply_apply i)
  gamma := by
    apply SpecialTransformations.Section5.GammaGraphDefinable.congr (gamma_global_map_graph (B := 𝔅)
      (mixedCoordinatePointMap σ (id : Fin 0 → Fin 0) (gammaNamedBase C Ξ).real))
    intro p q
    constructor
    · intro h
      refine ⟨⟨p.1,Set.mem_univ _⟩,rfl,?_⟩
      exact congrArg Prod.fst h
    · rintro ⟨u,hu,hq⟩
      rw [mixedCoordinatePointMap_value]
      refine Prod.ext ?_ (funext fun i => i.elim0)
      change p.1 ∘ σ = q.1
      rw [← hu,← hq]
      rfl

/-- Supported functions in the whole space are all functions. -/
def supportedUnivEquiv (n k : ℕ) :
    SupportedAEFunction hc C Ξ hΞ (GammaVFSet.univ C Ξ hΞ n) k ≃ AEFunction hc C Ξ hΞ n k :=
  Equiv.ofBijective (supportedForget hc C Ξ hΞ _) ⟨supported_forget_injective hc C Ξ hΞ _,by
    intro f
    induction f using Quotient.inductionOn with
    | h F => exact ⟨Quotient.mk _ ⟨F,presentation_supported_univ C Ξ hΞ F⟩,rfl⟩⟩

/-- **Gamma coordinate permutation of almost-everywhere functions** (with its Jacobian sign). -/
def aePermute (σ : Equiv.Perm (Fin (n+1))) : AEFunction hc C Ξ hΞ n k → AEFunction hc C Ξ hΞ n k :=
  fun f => supportedForget hc C Ξ hΞ _ (supportedJacobian hc C Ξ hΞ (coordinatePermutation C Ξ hΞ σ)
    ((supportedUnivEquiv hc C Ξ hΞ n k).symm f))

include hγ hγ1 in
theorem ae_permute_appended_integral (σ : Equiv.Perm (Fin (n+1))) (f : AEFunction hc C Ξ hΞ n k) :
    aeAppendedIntegral hc C Ξ hΞ hGenerated γ hγ hγ1 (aePermute hc C Ξ hΞ σ f) =
      aeAppendedIntegral hc C Ξ hΞ hGenerated γ hγ hγ1 f := by
  have h := supported_jacobian_appended_integral hc C Ξ hΞ hGenerated γ hγ hγ1 (coordinatePermutation C Ξ hΞ σ)
    ((supportedUnivEquiv hc C Ξ hΞ n k).symm f)
  refine h.trans ?_
  exact congrArg _ ((supportedUnivEquiv hc C Ξ hΞ n k).apply_symm_apply f)

end IntegrationInACVF.Section7.GammaFun
