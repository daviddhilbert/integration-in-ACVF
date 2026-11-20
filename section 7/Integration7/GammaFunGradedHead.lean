import Integration7.GammaFunHeadPositiveLinearity
import Integration7.GammaFunHeadZeroCoefLinearity
import Integration7.GammaFunHeadZeroFunctions
import Integration7.GammaFunHeadPosZero
import Integration7.GammaFunSupportedLinear
import Integration7.GammaFunAEAdditiveMaps

/-! **The graded Gamma-named head integral.** Head integrals of all-degree presentations commute with
all coefficient actions (the four head-linearity cases), so the head integral is a
`HK.GammaNamedRVSemiring`-linear map of graded Gamma-named functions raising the component index
by one, and the graded integral is invariant under it (graded head Fubini). -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open IntegrationInACVF.Section5 IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7.GammaFun
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n : ℕ}
variable (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
variable (Ξ : Set (Values.Gamma (M := M))) (hΞ : Cardinal.mk Ξ < C.κ)
variable (hGenerated : VFGammaGeneratedBase (gammaNamedBase C Ξ))

set_option quotPrecheck false
local notation "𝔅" => gammaNamedBase C Ξ
local notation "𝔇" => gammaNamedCodeContext C Ξ hΞ
local notation "𝔖" => ((gammaNamedCodeContext C Ξ hΞ).base : Set M)

/-- Head integrals of all-degree presentations. -/
def presHead : {j : ℕ} → Pres C Ξ hΞ (n+1) j → Pres C Ξ hΞ n (j+1)
  | 0, F => (F : ZeroPresentation C Ξ hΞ (n+1)).headIntegral hc C Ξ hΞ hGenerated
  | _+1, F => (F : Presentation C Ξ hΞ (n+1) _).headIntegral hc C Ξ hΞ hGenerated

theorem presentation_reindex_head {k k' : ℕ} (h : k = k') (F : Presentation C Ξ hΞ (n+1) k) :
    (F.reindex C Ξ hΞ h).headIntegral hc C Ξ hΞ hGenerated =
      (F.headIntegral hc C Ξ hΞ hGenerated).reindex C Ξ hΞ (congrArg (· + 1) h) := by
  subst h
  rfl

variable (γ : Values.Gamma (M := M)) (hγ : γ ∈ Ξ) (hγ1 : 1 < γ)

include hγ hγ1 in
/-- **Head integrals commute with coefficient actions** (almost everywhere, all degrees). -/
theorem pres_head_act {i j : ℕ} (u : HK.GammaRVObjects 𝔅 𝔖 i) (F : Pres C Ξ hΞ (n+1) j) :
    aeMk hc C Ξ hΞ (presHead hc C Ξ hΞ hGenerated (presAct hc C Ξ hΞ u F)) =
      aeMk hc C Ξ hΞ (presAct hc C Ξ hΞ u (presHead hc C Ξ hΞ hGenerated F)) := by
  cases i with
  | zero =>
    let Z : HK.GammaZeroRVObjects 𝔅 𝔖 := ⟨u.val,(HK.RVVolumeObject.Gamma.zero_iff _).mp u.property⟩
    cases j with
    | zero =>
      let F' : ZeroPresentation C Ξ hΞ (n+1) := F
      change aeMk hc C Ξ hΞ (j := (0+0)+1) ((F'.zeroCoef hc C Ξ hΞ Z).headIntegral hc C Ξ hΞ hGenerated) =
        aeMk hc C Ξ hΞ (j := (0+0)+1) (((F'.headIntegral hc C Ξ hΞ hGenerated).zeroCoef hc C Ξ hΞ Z).reindex C Ξ hΞ
          (Nat.zero_add 0).symm)
      exact ae_mk_reindex_eq hc C Ξ hΞ (Nat.zero_add 0).symm
        (presentation_head_zero_zero_ae hc C Ξ hΞ hGenerated γ hγ1 hγ Z F')
    | succ k =>
      let F' : Presentation C Ξ hΞ (n+1) k := F
      change aeMk hc C Ξ hΞ (j := (0+k)+1+1)
          (((F'.zeroCoef hc C Ξ hΞ Z).reindex C Ξ hΞ (Nat.zero_add k).symm).headIntegral hc C Ξ hΞ hGenerated) =
        aeMk hc C Ξ hΞ (j := (0+k)+1+1) (((F'.headIntegral hc C Ξ hΞ hGenerated).zeroCoef hc C Ξ hΞ Z).reindex C Ξ hΞ
          (Nat.zero_add (k+1)).symm)
      rw [presentation_reindex_head hc C Ξ hΞ hGenerated (Nat.zero_add k).symm]
      exact ae_mk_reindex_eq hc C Ξ hΞ _ (presentation_head_zero_coef_ae hc C Ξ hΞ hGenerated γ hγ hγ1 Z F')
  | succ p =>
    cases j with
    | zero => exact Quotient.sound (presentation_head_pos_zero_ae hc C Ξ hΞ hGenerated γ hγ1 hγ _ _)
    | succ k => exact Quotient.sound (presentation_head_left_product_ae hc C Ξ hΞ hGenerated γ hγ hγ1 _ _)

/-- Head integrals on components. -/
def aeHeadComp : (j : ℕ) → AEComp hc C Ξ hΞ (n+1) j →+ AEComp hc C Ξ hΞ n (j+1)
  | 0 => aeZeroHeadIntegralAddHom hc C Ξ hΞ hGenerated γ hγ hγ1 n
  | k+1 => aeHeadIntegralAddHom hc C Ξ hΞ hGenerated γ hγ hγ1 n k

theorem ae_head_comp_mk {j : ℕ} (F : Pres C Ξ hΞ (n+1) j) :
    aeHeadComp hc C Ξ hΞ hGenerated γ hγ hγ1 j (aeMk hc C Ξ hΞ F) = aeMk hc C Ξ hΞ (presHead hc C Ξ hΞ hGenerated F) := by
  cases j <;> rfl

/-- **Head integrals are linear on homogeneous elements.** -/
theorem ae_head_comp_act {i j : ℕ} (a : HK.GammaNamedRVClasses hc C Ξ hΞ i) (f : AEComp hc C Ξ hΞ (n+1) j) :
    aeHeadComp hc C Ξ hΞ hGenerated γ hγ hγ1 (i+j) (aeAct hc C Ξ hΞ a f) =
      aeAct hc C Ξ hΞ a (aeHeadComp hc C Ξ hΞ hGenerated γ hγ hγ1 j f) := by
  obtain ⟨u,rfl⟩ := HK.gammaNamedRVClass_surjective hc C Ξ hΞ i a
  rw [← aeMk_rep hc C Ξ hΞ f,aeAct_mk,ae_head_comp_mk,ae_head_comp_mk,aeAct_mk]
  exact pres_head_act hc C Ξ hΞ hGenerated γ hγ hγ1 u _

/-- **The graded Gamma-named head integral, as a linear map** (raising the component index by one). -/
def gradedHeadLinearMap (n : ℕ) :
    GradedAEFunction hc C Ξ hΞ (n+1) →ₗ[HK.GammaNamedRVSemiring hc C Ξ hΞ] GradedAEFunction hc C Ξ hΞ n where
  toAddHom := (DirectSum.toAddMonoid fun j => (DirectSum.of (AEComp hc C Ξ hΞ n) (j+1)).comp
    (aeHeadComp hc C Ξ hΞ hGenerated γ hγ hγ1 j)).toAddHom
  map_smul' r x := by
    let F := DirectSum.toAddMonoid fun j => (DirectSum.of (AEComp hc C Ξ hΞ n) (j+1)).comp
      (aeHeadComp hc C Ξ hΞ hGenerated γ hγ hγ1 j)
    change F (r • x) = r • F x
    induction r using DirectSum.induction_on with
    | zero => simp only [zero_smul,map_zero]
    | of i a =>
      induction x using DirectSum.induction_on with
      | zero => simp only [smul_zero,map_zero]
      | of j f =>
        rw [graded_ae_action_of]
        simp only [F,DirectSum.toAddMonoid_of,AddMonoidHom.comp_apply]
        rw [ae_head_comp_act,graded_ae_action_of]
        rfl
      | add f g hf hg => rw [smul_add,map_add,map_add,smul_add,hf,hg]
    | add r s hr hs => rw [add_smul,map_add,hr,hs,add_smul]

theorem graded_head_of {j : ℕ} (f : AEComp hc C Ξ hΞ (n+1) j) :
    gradedHeadLinearMap hc C Ξ hΞ hGenerated γ hγ hγ1 n (DirectSum.of (AEComp hc C Ξ hΞ (n+1)) j f) =
      DirectSum.of (AEComp hc C Ξ hΞ n) (j+1) (aeHeadComp hc C Ξ hΞ hGenerated γ hγ hγ1 j f) := by
  change (DirectSum.toAddMonoid fun j => (DirectSum.of (AEComp hc C Ξ hΞ n) (j+1)).comp
    (aeHeadComp hc C Ξ hΞ hGenerated γ hγ hγ1 j)) (DirectSum.of _ j f) = _
  rw [DirectSum.toAddMonoid_of]
  rfl

include hγ hγ1 in
/-- **Graded head Fubini**: the graded integral is invariant under the graded head integral. -/
theorem graded_head_fubini (n : ℕ) :
    (gradedIntegralLinearMap hc C Ξ hΞ hGenerated γ hγ hγ1 n).comp (gradedHeadLinearMap hc C Ξ hΞ hGenerated γ hγ hγ1 n) =
      gradedIntegralLinearMap hc C Ξ hΞ hGenerated γ hγ hγ1 (n+1) := by
  apply LinearMap.ext
  intro x
  induction x using DirectSum.induction_on with
  | zero => simp only [map_zero]
  | of j f =>
    change gradedIntegralAddHom hc C Ξ hΞ hGenerated γ hγ hγ1 n
        (gradedHeadLinearMap hc C Ξ hΞ hGenerated γ hγ hγ1 n (DirectSum.of _ j f)) =
      gradedIntegralAddHom hc C Ξ hΞ hGenerated γ hγ hγ1 (n+1) (DirectSum.of _ j f)
    rw [graded_head_of,graded_integral_of,graded_integral_of]
    cases j with
    | zero =>
      apply gamma_semiring_of_heq hc C Ξ hΞ _ (ae_zero_head_fubini hc C Ξ hΞ hGenerated γ hγ hγ1 f)
      simp only [append_volume_degree_eq]
      omega
    | succ k =>
      exact gamma_semiring_of_heq hc C Ξ hΞ rfl (heq_of_eq (ae_head_fubini hc C Ξ hΞ hGenerated γ hγ hγ1 f))
  | add x y hx hy => rw [map_add,map_add,hx,hy]

end IntegrationInACVF.Section7.GammaFun
