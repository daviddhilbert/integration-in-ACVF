import Integration7.GammaFunPositiveCoefficients
import Integration7.GammaNamedPositiveProductIsos
import Integration7.GammaVolumeLeftDistributivity

/-! The action of positive Gamma-named coefficient classes on Gamma-named positive functions:
multiplication by the actual left product. It respects Gamma blowup equivalence of the
coefficient and almost-everywhere equivalence of the function, and is additive in the
function. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section5 (Point GammaSetDefinable GammaGraphDefinable gammaLogicInput carrier VF RV)
open IntegrationInACVF.Section5 IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7.GammaFun
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n k p : ℕ}
variable (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
variable (Ξ : Set (Values.Gamma (M := M))) (hΞ : Cardinal.mk Ξ < C.κ)

set_option quotPrecheck false
local notation "𝔅" => gammaNamedBase C Ξ
local notation "𝔇" => gammaNamedCodeContext C Ξ hΞ
local notation "𝔖" => ((gammaNamedCodeContext C Ξ hΞ).base : Set M)

/-- The positive coefficient `U` times the presentation `F`. -/
def Presentation.leftProduct (U : GammaVolumeObjects 𝔅 𝔖 p) (F : Presentation C Ξ hΞ n k) :
    Presentation C Ξ hΞ n ((p+1)+k) :=
  ⟨_,selectedVolumeFamilyLeftProduct U.val F.family,F.gamma.leftProduct hc U.property⟩

/-- The coefficient carried to the row context of `x`. -/
def rowCoefficient (U : GammaVolumeObjects 𝔅 𝔖 p) (x : Fin (n+1) → VFType (M := M)) :
    GammaVolumeObjects (rowGammaBase 𝔅 x) ((vfParameterVolumeContext 𝔇 x).base : Set M) p :=
  GammaVolumeObjects.changeBase (B := rowGammaBase 𝔅 x)
    (GammaVolumeObjects.extend U (fun _ h => vfParameterVolumeContext_contains 𝔇 x (Or.inl h)))
    (GammaBaseDominated.of_subset Set.subset_union_left (Set.Subset.refl _))

theorem presentation_left_product_row_class (U : GammaVolumeObjects 𝔅 𝔖 p) (F : Presentation C Ξ hΞ n k)
    (x : Fin (n+1) → VFType (M := M)) :
    (F.leftProduct hc C Ξ hΞ U).rowClass hc C Ξ hΞ x =
      gammaVolumeBlowupClass hc (vfParameterVolumeContext 𝔇 x) (rowGammaBase 𝔅 x)
        ((rowCoefficient C Ξ hΞ U x).prod hc ⟨F.family.rowInContext x,F.gamma.row hc x⟩) :=
  gamma_left_product_row_class hc U.property F.gamma x

theorem row_coefficient_equivalent {U U' : GammaVolumeObjects 𝔅 𝔖 p}
    (h : GammaVolumeBlowupEquivalent 𝔅 𝔖 p U U') (x : Fin (n+1) → VFType (M := M)) :
    GammaVolumeBlowupEquivalent (rowGammaBase 𝔅 x) ((vfParameterVolumeContext 𝔇 x).base : Set M) p
      (rowCoefficient C Ξ hΞ U x) (rowCoefficient C Ξ hΞ U' x) :=
  (h.extend _).changeBase _

/-- **The positive coefficient action respects equivalences.** -/
theorem presentation_left_product_ae {U U' : GammaVolumeObjects 𝔅 𝔖 p} (hU : GammaVolumeBlowupEquivalent 𝔅 𝔖 p U U')
    {F H : Presentation C Ξ hΞ n k} (hF : AEEquivalent hc C Ξ hΞ F H) :
    AEEquivalent hc C Ξ hΞ (F.leftProduct hc C Ξ hΞ U) (H.leftProduct hc C Ξ hΞ U') := by
  obtain ⟨E,hE,hRows⟩ := hF
  refine ⟨E,hE,fun x hx => ?_⟩
  rw [presentation_left_product_row_class,presentation_left_product_row_class]
  apply (gammaVolumeBlowupClass_eq_iff hc _ _).mpr
  exact ((row_coefficient_equivalent C Ξ hΞ hU x).product_right hc _ _).trans hc _ _
    (((gammaVolumeBlowupClass_eq_iff hc _ _).mp (hRows x hx)).product_left hc _ _)

/-- **The action of positive Gamma-named coefficients on Gamma-named positive functions.** -/
def aePositiveCoefficientAction (p : ℕ) :
    GammaVolumeBlowupClasses hc 𝔇 𝔅 p → AEFunction hc C Ξ hΞ n k → AEFunction hc C Ξ hΞ n ((p+1)+k) :=
  Quotient.map₂ (fun U F => F.leftProduct hc C Ξ hΞ U)
    (fun _ _ hU _ _ hF => presentation_left_product_ae hc C Ξ hΞ hU hF)

theorem ae_positive_coefficient_action_mk (U : GammaVolumeObjects 𝔅 𝔖 p) (F : Presentation C Ξ hΞ n k) :
    aePositiveCoefficientAction hc C Ξ hΞ p (gammaVolumeBlowupClass hc 𝔇 𝔅 U) (Quotient.mk _ F) =
      Quotient.mk _ (F.leftProduct hc C Ξ hΞ U) := rfl

/-- **The positive coefficient action is additive in the function.** -/
theorem presentation_left_product_add (U : GammaVolumeObjects 𝔅 𝔖 p) (F H : Presentation C Ξ hΞ n k) :
    AEEquivalent hc C Ξ hΞ ((F.add C Ξ hΞ H).leftProduct hc C Ξ hΞ U)
      ((F.leftProduct hc C Ξ hΞ U).add C Ξ hΞ (H.leftProduct hc C Ξ hΞ U)) := by
  apply ae_equivalent_of_rows hc C Ξ hΞ
  intro x
  rw [presentation_add_row_class,presentation_left_product_row_class,presentation_left_product_row_class,
    presentation_left_product_row_class]
  let Cx := vfParameterVolumeContext 𝔇 x
  let Bx := rowGammaBase 𝔅 x
  let R := rowCoefficient C Ξ hΞ U x
  let A : GammaVolumeObjects Bx (Cx.base : Set M) k := ⟨F.family.rowInContext x,F.gamma.row hc x⟩
  let B' : GammaVolumeObjects Bx (Cx.base : Set M) k := ⟨H.family.rowInContext x,H.gamma.row hc x⟩
  have hS : GammaVolumeBlowupEquivalent Bx (Cx.base : Set M) k
      ⟨(F.add C Ξ hΞ H).family.rowInContext x,(F.add C Ξ hΞ H).gamma.row hc x⟩ (A.coprod B') :=
    (gammaVolumeBlowupClass_eq_iff hc Cx Bx).mp (presentation_add_row_class hc C Ξ hΞ F H x)
  rw [← gammaVolumeBlowupClass_coprod]
  apply (gammaVolumeBlowupClass_eq_iff hc Cx Bx).mpr
  refine (hS.product_left hc Cx R).trans hc Cx Bx ?_
  exact GammaVolumeBlowupEquivalent.of_iso Cx Bx (volumeProductRightDistribIso hc Cx R.val A.val B'.val)
    (gamma_volume_product_right_distrib_iso hc Cx R.property A.property B'.property)

theorem presentation_left_product_zero (U : GammaVolumeObjects 𝔅 𝔖 p) (n k : ℕ) :
    AEEquivalent hc C Ξ hΞ ((Presentation.zero C Ξ hΞ n k).leftProduct hc C Ξ hΞ U)
      (Presentation.zero C Ξ hΞ n ((p+1)+k)) := by
  apply ae_equivalent_of_rows hc C Ξ hΞ
  intro x
  rw [presentation_zero_row_class]
  apply presentation_row_class_zero_of_empty hc C Ξ hΞ
  intro r hr
  obtain ⟨f,_,_⟩ := (mem_left_product U.val _ _).mp hr
  exact f.property

/-- The positive coefficient action by a fixed class, as an additive monoid homomorphism. -/
def aePositiveCoefficientAddHom (p : ℕ) (c : GammaVolumeBlowupClasses hc 𝔇 𝔅 p) (n k : ℕ) :
    AEFunction hc C Ξ hΞ n k →+ AEFunction hc C Ξ hΞ n ((p+1)+k) where
  toFun := aePositiveCoefficientAction hc C Ξ hΞ p c
  map_zero' := by
    induction c using Quotient.inductionOn with
    | h U => exact Quotient.sound (presentation_left_product_zero hc C Ξ hΞ U n k)
  map_add' f g := by
    induction c using Quotient.inductionOn with
    | h U => exact Quotient.inductionOn₂ f g (fun F H => Quotient.sound (presentation_left_product_add hc C Ξ hΞ U F H))

set_option maxHeartbeats 800000 in
theorem row_coefficient_coprod (U U' : GammaVolumeObjects 𝔅 𝔖 p) (x : Fin (n+1) → VFType (M := M)) :
    gammaVolumeBlowupClass hc (vfParameterVolumeContext 𝔇 x) (rowGammaBase 𝔅 x) (rowCoefficient C Ξ hΞ (U.coprod U') x) =
      gammaVolumeBlowupClass hc (vfParameterVolumeContext 𝔇 x) (rowGammaBase 𝔅 x)
        ((rowCoefficient C Ξ hΞ U x).coprod (rowCoefficient C Ξ hΞ U' x)) :=
  gamma_class_eq_of_select hc _ _ _ _ id (fun _ h => h) (fun s hs => ⟨s,hs,rfl⟩) (fun _ _ _ _ h => h)
    (fun _ => rfl) (fun _ => rfl)

/-- **The positive coefficient action is additive in the coefficient.** -/
theorem presentation_left_product_coef_add (U U' : GammaVolumeObjects 𝔅 𝔖 p) (F : Presentation C Ξ hΞ n k) :
    AEEquivalent hc C Ξ hΞ (F.leftProduct hc C Ξ hΞ (U.coprod U'))
      ((F.leftProduct hc C Ξ hΞ U).add C Ξ hΞ (F.leftProduct hc C Ξ hΞ U')) := by
  apply ae_equivalent_of_rows hc C Ξ hΞ
  intro x
  rw [presentation_add_row_class,presentation_left_product_row_class,presentation_left_product_row_class,
    presentation_left_product_row_class]
  let Cx := vfParameterVolumeContext 𝔇 x
  let Bx := rowGammaBase 𝔅 x
  let A : GammaVolumeObjects Bx (Cx.base : Set M) k := ⟨F.family.rowInContext x,F.gamma.row hc x⟩
  let R := rowCoefficient C Ξ hΞ U x
  let R' := rowCoefficient C Ξ hΞ U' x
  have hR := (gammaVolumeBlowupClass_eq_iff hc Cx Bx).mp (row_coefficient_coprod hc C Ξ hΞ U U' x)
  rw [← gammaVolumeBlowupClass_coprod]
  apply (gammaVolumeBlowupClass_eq_iff hc Cx Bx).mpr
  refine (hR.product_right hc Cx A).trans hc Cx Bx ?_
  exact GammaVolumeBlowupEquivalent.of_iso Cx Bx ((volumeLeftProductCoprodFoldIso hc Cx R.val R'.val A.val).symm hc Cx)
    ((gamma_volume_left_product_coprod_fold_iso hc Cx R.property R'.property A.property).symm hc Cx Bx)

theorem presentation_left_product_coef_zero (F : Presentation C Ξ hΞ n k) (p : ℕ) :
    AEEquivalent hc C Ξ hΞ (F.leftProduct hc C Ξ hΞ (GammaVolumeObjects.empty 𝔅 𝔖 p))
      (Presentation.zero C Ξ hΞ n ((p+1)+k)) := by
  apply ae_equivalent_of_rows hc C Ξ hΞ
  intro x
  rw [presentation_zero_row_class]
  apply presentation_row_class_zero_of_empty hc C Ξ hΞ
  intro r hr
  obtain ⟨_,u,_⟩ := (mem_left_product _ F.family _).mp hr
  exact u.property

/-- **The biadditive positive coefficient action.** -/
def aePositiveCoefficientBiadditive (p n k : ℕ) :
    GammaVolumeBlowupClasses hc 𝔇 𝔅 p →+ (AEFunction hc C Ξ hΞ n k →+ AEFunction hc C Ξ hΞ n ((p+1)+k)) where
  toFun c := aePositiveCoefficientAddHom hc C Ξ hΞ p c n k
  map_zero' := by
    ext f
    induction f using Quotient.inductionOn with
    | h F => exact Quotient.sound (presentation_left_product_coef_zero hc C Ξ hΞ F p)
  map_add' c c' := by
    ext f
    induction c using Quotient.inductionOn with
    | h U =>
      induction c' using Quotient.inductionOn with
      | h U' =>
        induction f using Quotient.inductionOn with
        | h F => exact Quotient.sound (presentation_left_product_coef_add hc C Ξ hΞ U U' F)

end IntegrationInACVF.Section7.GammaFun
