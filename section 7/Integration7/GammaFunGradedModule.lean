import Integration7.GammaFunAllDegreeAE
import HilbertMathlib.Foundation.Grading.GradedSemiringActions

/-! **The graded Gamma-named function module.** The all-degree coefficient action of
Gamma-named RV classes on the graded components of Gamma-named almost-everywhere functions is
biadditive, unital and associative, hence a graded semiring action, and the direct sum of the
components is a module over `HK.GammaNamedRVSemiring`. All laws are checked on rows: at every VF
point the row of a product is the actual product of the row coefficient with the row, and the
laws of actual products hold in every row context (`HK.Ctx`). -/
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
local notation "𝔠" x => HK.Ctx.gammaNamedRVClass hc (vfParameterVolumeContext (gammaNamedCodeContext C Ξ hΞ) x)
  (rowGammaBase (gammaNamedBase C Ξ) x)

theorem ctx_product_congr_right_heq {D : BaseContext M} {B : Base (M := M)} {i m m' : ℕ} (h : m = m')
    (U : HK.GammaRVObjects B (D.base : Set M) i) {V : HK.GammaRVObjects B (D.base : Set M) m}
    {V' : HK.GammaRVObjects B (D.base : Set M) m'}
    (hV : HEq (HK.Ctx.gammaNamedRVClass hc D B V) (HK.Ctx.gammaNamedRVClass hc D B V')) :
    HEq (HK.Ctx.gammaNamedRVClass hc D B (U.product hc V)) (HK.Ctx.gammaNamedRVClass hc D B (U.product hc V')) := by
  subst h
  exact heq_of_eq (HK.Ctx.gamma_named_product_congr_right hc D B U (eq_of_heq hV))

theorem coefRow_coprod {i : ℕ} (u v : HK.GammaRVObjects 𝔅 𝔖 i) (x : Fin (n+1) → VFType (M := M)) :
    coefRow C Ξ hΞ (u.coprod v) x = (coefRow C Ξ hΞ u x).coprod (coefRow C Ξ hΞ v x) := by
  cases i <;> rfl

theorem coefRow_empty (i : ℕ) (x : Fin (n+1) → VFType (M := M)) :
    coefRow C Ξ hΞ (HK.gammaEmpty C Ξ hΞ i) x =
      HK.Ctx.gammaEmpty (vfParameterVolumeContext 𝔇 x) (rowGammaBase 𝔅 x) i := by
  cases i <;> rfl

theorem coefRow_unit (x : Fin (n+1) → VFType (M := M)) :
    coefRow C Ξ hΞ (HK.gammaUnit hc C Ξ hΞ) x = HK.Ctx.gammaUnit hc (vfParameterVolumeContext 𝔇 x) (rowGammaBase 𝔅 x) :=
  rfl

set_option maxHeartbeats 3200000 in
theorem coefRow_product {i j : ℕ} (u : HK.GammaRVObjects 𝔅 𝔖 i) (v : HK.GammaRVObjects 𝔅 𝔖 j)
    (x : Fin (n+1) → VFType (M := M)) :
    coefRow C Ξ hΞ (u.product hc v) x = (coefRow C Ξ hΞ u x).product hc (coefRow C Ξ hΞ v x) := by
  cases i <;> cases j <;> rfl

/-! ### Addition of component presentations -/

/-- Sum of component presentations. -/
def presAdd : {j : ℕ} → Pres C Ξ hΞ n j → Pres C Ξ hΞ n j → Pres C Ξ hΞ n j
  | 0, F, H => (F : ZeroPresentation C Ξ hΞ n).add C Ξ hΞ H
  | _+1, F, H => (F : Presentation C Ξ hΞ n _).add C Ξ hΞ H

/-- The empty component presentation. -/
def presZero : (j : ℕ) → Pres C Ξ hΞ n j
  | 0 => ZeroPresentation.zero C Ξ hΞ n
  | k+1 => Presentation.zero C Ξ hΞ n k

theorem aeMk_add {j : ℕ} (F H : Pres C Ξ hΞ n j) :
    aeMk hc C Ξ hΞ (presAdd C Ξ hΞ F H) = aeMk hc C Ξ hΞ F + aeMk hc C Ξ hΞ H := by
  cases j <;> rfl

theorem aeMk_zero (j : ℕ) : aeMk hc C Ξ hΞ (presZero C Ξ hΞ (n := n) j) = 0 := by
  cases j <;> rfl

theorem pres_add_row_class {j : ℕ} (F H : Pres C Ξ hΞ n j) (x : Fin (n+1) → VFType (M := M)) :
    presRowClass hc C Ξ hΞ (presAdd C Ξ hΞ F H) x = presRowClass hc C Ξ hΞ F x + presRowClass hc C Ξ hΞ H x := by
  cases j with
  | zero => exact zero_presentation_add_row_class hc C Ξ hΞ F H x
  | succ k => exact presentation_add_row_class hc C Ξ hΞ F H x

theorem pres_zero_row_class (j : ℕ) (x : Fin (n+1) → VFType (M := M)) :
    presRowClass hc C Ξ hΞ (presZero C Ξ hΞ (n := n) j) x = 0 := by
  cases j with
  | zero => exact zero_presentation_zero_row_class hc C Ξ hΞ x
  | succ k => exact presentation_zero_row_class hc C Ξ hΞ x

theorem pres_row_class_eq {j : ℕ} (F : Pres C Ξ hΞ n j) (x : Fin (n+1) → VFType (M := M)) :
    presRowClass hc C Ξ hΞ F x = (𝔠 x) (presRow hc C Ξ hΞ F x) := rfl

/-! ### The action on almost-everywhere functions -/

/-- **The all-degree coefficient action on Gamma-named almost-everywhere functions.** -/
def aeAct {i j : ℕ} (a : HK.GammaNamedRVClasses hc C Ξ hΞ i) (f : AEComp hc C Ξ hΞ n j) : AEComp hc C Ξ hΞ n (i+j) :=
  aeMk hc C Ξ hΞ (presAct hc C Ξ hΞ (HK.gammaNamedRVRep hc C Ξ hΞ a) (aeRep hc C Ξ hΞ f))

set_option maxHeartbeats 800000 in
/-- The action computed on arbitrary representatives. -/
theorem aeAct_mk {i j : ℕ} (u : HK.GammaRVObjects 𝔅 𝔖 i) (F : Pres C Ξ hΞ n j) :
    aeAct hc C Ξ hΞ (HK.gammaNamedRVClass hc C Ξ hΞ u) (aeMk hc C Ξ hΞ F) =
      aeMk hc C Ξ hΞ (presAct hc C Ξ hΞ u F) := by
  let u' := HK.gammaNamedRVRep hc C Ξ hΞ (HK.gammaNamedRVClass hc C Ξ hΞ u)
  let F' := aeRep hc C Ξ hΞ (aeMk hc C Ξ hΞ F)
  obtain ⟨E,hE,hRows⟩ := (aeMk_eq_iff hc C Ξ hΞ F' F).mp (aeMk_rep hc C Ξ hΞ _)
  apply (aeMk_eq_iff hc C Ξ hΞ _ _).mpr
  refine ⟨E,hE,fun x hx => ?_⟩
  have hu := coef_row_class_congr hc C Ξ hΞ (HK.gammaNamedRVRep_class hc C Ξ hΞ (HK.gammaNamedRVClass hc C Ξ hΞ u)) x
  have hmid : (𝔠 x) ((coefRow C Ξ hΞ u' x).product hc (presRow hc C Ξ hΞ F' x)) =
      (𝔠 x) ((coefRow C Ξ hΞ u x).product hc (presRow hc C Ξ hΞ F x)) :=
    (HK.Ctx.gamma_named_product_congr_left hc _ _ hu _).trans
      (HK.Ctx.gamma_named_product_congr_right hc _ _ _ (hRows x hx))
  exact eq_of_heq ((pres_act_row hc C Ξ hΞ u' F' x).trans ((heq_of_eq hmid).trans (pres_act_row hc C Ξ hΞ u F x).symm))

theorem aeAct_add_right {i j : ℕ} (a : HK.GammaNamedRVClasses hc C Ξ hΞ i) (f g : AEComp hc C Ξ hΞ n j) :
    aeAct hc C Ξ hΞ a (f + g) = aeAct hc C Ξ hΞ a f + aeAct hc C Ξ hΞ a g := by
  obtain ⟨u,rfl⟩ := HK.gammaNamedRVClass_surjective hc C Ξ hΞ i a
  rw [← aeMk_rep hc C Ξ hΞ f,← aeMk_rep hc C Ξ hΞ g,← aeMk_add,aeAct_mk,aeAct_mk,aeAct_mk,← aeMk_add]
  apply aeMk_eq_of_rows
  intro x
  let F := aeRep hc C Ξ hΞ f
  let H := aeRep hc C Ξ hΞ g
  rw [pres_add_row_class,eq_of_heq (pres_act_row hc C Ξ hΞ u (presAdd C Ξ hΞ F H) x),
    eq_of_heq (pres_act_row hc C Ξ hΞ u F x),eq_of_heq (pres_act_row hc C Ξ hΞ u H x)]
  have hrow : (𝔠 x) (presRow hc C Ξ hΞ (presAdd C Ξ hΞ F H) x) =
      (𝔠 x) ((presRow hc C Ξ hΞ F x).coprod (presRow hc C Ξ hΞ H x)) :=
    (pres_add_row_class hc C Ξ hΞ F H x).trans (HK.Ctx.gammaNamedRVClass_coprod hc _ _ _ _).symm
  rw [HK.Ctx.gamma_named_product_congr_right hc _ _ _ hrow,HK.Ctx.gamma_product_right_distrib,
    HK.Ctx.gammaNamedRVClass_coprod]

theorem aeAct_zero_right {i j : ℕ} (a : HK.GammaNamedRVClasses hc C Ξ hΞ i) :
    aeAct hc C Ξ hΞ a (0 : AEComp hc C Ξ hΞ n j) = 0 := by
  obtain ⟨u,rfl⟩ := HK.gammaNamedRVClass_surjective hc C Ξ hΞ i a
  rw [← aeMk_zero hc C Ξ hΞ j,aeAct_mk,← aeMk_zero hc C Ξ hΞ (i+j)]
  apply aeMk_eq_of_rows
  intro x
  rw [eq_of_heq (pres_act_row hc C Ξ hΞ u (presZero C Ξ hΞ j) x),pres_zero_row_class]
  have hrow : (𝔠 x) (presRow hc C Ξ hΞ (presZero C Ξ hΞ (n := n) j) x) =
      (𝔠 x) (HK.Ctx.gammaEmpty _ _ j) :=
    (pres_zero_row_class hc C Ξ hΞ j x).trans (HK.Ctx.gammaNamedRV_zero_eq hc _ _ j)
  rw [HK.Ctx.gamma_named_product_congr_right hc _ _ _ hrow,HK.Ctx.gamma_product_right_zero,
    HK.Ctx.gammaNamedRV_zero_eq]

theorem aeAct_add_left {i j : ℕ} (a b : HK.GammaNamedRVClasses hc C Ξ hΞ i) (f : AEComp hc C Ξ hΞ n j) :
    aeAct hc C Ξ hΞ (a + b) f = aeAct hc C Ξ hΞ a f + aeAct hc C Ξ hΞ b f := by
  obtain ⟨u,rfl⟩ := HK.gammaNamedRVClass_surjective hc C Ξ hΞ i a
  obtain ⟨v,rfl⟩ := HK.gammaNamedRVClass_surjective hc C Ξ hΞ i b
  rw [HK.gammaNamedRV_add_eq,← aeMk_rep hc C Ξ hΞ f,aeAct_mk,aeAct_mk,aeAct_mk,← aeMk_add]
  apply aeMk_eq_of_rows
  intro x
  let F := aeRep hc C Ξ hΞ f
  rw [pres_add_row_class,eq_of_heq (pres_act_row hc C Ξ hΞ (u.coprod v) F x),
    eq_of_heq (pres_act_row hc C Ξ hΞ u F x),eq_of_heq (pres_act_row hc C Ξ hΞ v F x)]
  rw [coefRow_coprod]
  exact (HK.Ctx.gamma_product_left_distrib hc _ _ (coefRow C Ξ hΞ u x) (coefRow C Ξ hΞ v x) _).trans
    (HK.Ctx.gammaNamedRVClass_coprod hc _ _ _ _)

theorem aeAct_zero_left {i j : ℕ} (f : AEComp hc C Ξ hΞ n j) :
    aeAct hc C Ξ hΞ (0 : HK.GammaNamedRVClasses hc C Ξ hΞ i) f = 0 := by
  rw [HK.gammaNamedRV_zero_eq,← aeMk_rep hc C Ξ hΞ f,aeAct_mk,← aeMk_zero hc C Ξ hΞ (i+j)]
  apply aeMk_eq_of_rows
  intro x
  rw [eq_of_heq (pres_act_row hc C Ξ hΞ (HK.gammaEmpty C Ξ hΞ i) (aeRep hc C Ξ hΞ f) x),pres_zero_row_class,
    coefRow_empty]
  exact (HK.Ctx.gamma_product_left_zero hc _ _ (n := i) _).trans (HK.Ctx.gammaNamedRV_zero_eq hc _ _ _).symm

/-- **The biadditive coefficient action.** -/
def aeActBiadditive (n i j : ℕ) :
    HK.GammaNamedRVClasses hc C Ξ hΞ i →+ (AEComp hc C Ξ hΞ n j →+ AEComp hc C Ξ hΞ n (i+j)) where
  toFun a :=
    { toFun := aeAct hc C Ξ hΞ a
      map_zero' := aeAct_zero_right hc C Ξ hΞ a
      map_add' := aeAct_add_right hc C Ξ hΞ a }
  map_zero' := by
    ext f
    exact aeAct_zero_left hc C Ξ hΞ f
  map_add' a b := by
    ext f
    exact aeAct_add_left hc C Ξ hΞ a b f

/-! ### Unit and associativity -/

theorem aeAct_one {j : ℕ} (f : AEComp hc C Ξ hΞ n j) :
    HEq (aeAct hc C Ξ hΞ (GradedMonoid.GOne.one : HK.GammaNamedRVClasses hc C Ξ hΞ 0) f) f := by
  change HEq (aeAct hc C Ξ hΞ (HK.gammaNamedRVClass hc C Ξ hΞ (HK.gammaUnit hc C Ξ hΞ)) f) f
  rw [← aeMk_rep hc C Ξ hΞ f,aeAct_mk]
  apply aeMk_heq_of_rows hc C Ξ hΞ (Nat.zero_add j)
  intro x
  refine (pres_act_row hc C Ξ hΞ _ _ x).trans ?_
  rw [coefRow_unit]
  exact HK.Ctx.gamma_product_left_unit hc _ _ _

theorem aeAct_assoc {i j k : ℕ} (a : HK.GammaNamedRVClasses hc C Ξ hΞ i) (b : HK.GammaNamedRVClasses hc C Ξ hΞ j)
    (f : AEComp hc C Ξ hΞ n k) :
    HEq (aeAct hc C Ξ hΞ (HK.gammaNamedRVMul hc C Ξ hΞ a b) f) (aeAct hc C Ξ hΞ a (aeAct hc C Ξ hΞ b f)) := by
  obtain ⟨u,rfl⟩ := HK.gammaNamedRVClass_surjective hc C Ξ hΞ i a
  obtain ⟨v,rfl⟩ := HK.gammaNamedRVClass_surjective hc C Ξ hΞ j b
  rw [HK.gammaNamedRVMul_class,← aeMk_rep hc C Ξ hΞ f,aeAct_mk,aeAct_mk,aeAct_mk]
  apply aeMk_heq_of_rows hc C Ξ hΞ (Nat.add_assoc i j k)
  intro x
  let F := aeRep hc C Ξ hΞ f
  refine (pres_act_row hc C Ξ hΞ (u.product hc v) F x).trans ?_
  rw [coefRow_product]
  refine (HK.Ctx.gamma_product_assoc hc _ _ (coefRow C Ξ hΞ u x) (coefRow C Ξ hΞ v x) (presRow hc C Ξ hΞ F x)).trans ?_
  refine HEq.trans ?_ (pres_act_row hc C Ξ hΞ u (presAct hc C Ξ hΞ v F) x).symm
  exact ctx_product_congr_right_heq hc rfl _ (pres_act_row hc C Ξ hΞ v F x).symm

/-- **The graded action of Gamma-named RV classes on Gamma-named functions.** -/
def aeGradedAction (n : ℕ) :
    GradedSemiringAction (HK.GammaNamedRVClasses hc C Ξ hΞ) (AEComp hc C Ξ hΞ n) where
  act := aeActBiadditive hc C Ξ hΞ n
  one_act j f := aeAct_one hc C Ξ hΞ f
  mul_act i j k a b f := by exact aeAct_assoc hc C Ξ hΞ a b f

/-- **The graded Gamma-named function space.** -/
abbrev GradedAEFunction (n : ℕ) := DirectSum ℕ (AEComp hc C Ξ hΞ n)

/-- **The `HK.GammaNamedRVSemiring`-module of graded Gamma-named functions.** -/
instance gradedAEFunctionModule (n : ℕ) :
    Module (HK.GammaNamedRVSemiring hc C Ξ hΞ) (GradedAEFunction hc C Ξ hΞ n) :=
  gradedSemiringActionModule (aeGradedAction hc C Ξ hΞ n)

theorem graded_ae_action_of {i j : ℕ} (a : HK.GammaNamedRVClasses hc C Ξ hΞ i) (f : AEComp hc C Ξ hΞ n j) :
    DirectSum.of (HK.GammaNamedRVClasses hc C Ξ hΞ) i a • DirectSum.of (AEComp hc C Ξ hΞ n) j f =
      DirectSum.of (AEComp hc C Ξ hΞ n) (i+j) (aeAct hc C Ξ hΞ a f) :=
  graded_semiring_action_of_of (aeGradedAction hc C Ξ hΞ n) i j a f

end IntegrationInACVF.Section7.GammaFun
