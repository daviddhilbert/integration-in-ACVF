import Integration7.GammaFunGradedIntegral
import Integration7.GammaNamedTheorem713
import Integration7.UnitPointVolumeSwaps
import Integration7.CentralAwayLocalization
import Integration7.GradedSemiringUnitNormalization

/-! **Gamma-named normalized coefficients.** The Gamma-named degree-one point class is
central in `HK.GammaNamedRVSemiring` (its swaps past positive and weighted degree-zero
classes are Gamma-definable). Localizing the Gamma-named class ring at the point and
normalizing homogeneous terms gives the Gamma-named normalized coefficient ring. No
hypothesis puts the common names of `⟨C.base, Ξ⟩` into `C.base`. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry SpecialTransformations.Section9
open IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {B : Base (M := M)} {k : ℕ}

theorem gamma_volume_unit_point_swap_iso (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    {U : PositiveRVVolumeObject (M := M) (C.base : Set M) k} (hU : VolumeObjectGamma U B) :
    (volumeUnitPointSwapIso C U).GammaDefinable B := by
  have hUP := hU.prod hc (VolumeObjectGamma.degreeOnePoint (B := B) hc (C.base : Set M))
  exact gamma_volume_iso_of_full_map _
    (rvProductSwapMap U.underlying.obj (degreeOnePointVolumeObject (M := M) (C.base : Set M)).underlying.obj)
    (gamma_essential_volume_domain _ hUP.coordinates)
    (gamma_rv_coordinate_map hc _ _ hUP.domain_graph (rv_product_swap_raw _ _))
    (fun _ => rfl)

end IntegrationInACVF.Section7

namespace IntegrationInACVF.Section7.HK
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
variable (Ξ : Set (Values.Gamma (M := M))) (hΞ : Cardinal.mk Ξ < C.κ)

set_option quotPrecheck false
local notation "𝔅" => gammaNamedBase C Ξ
local notation "𝔇" => gammaNamedCodeContext C Ξ hΞ
local notation "𝔖" => ((gammaNamedCodeContext C Ξ hΞ).base : Set M)

/-- The Gamma-named degree-one point class. -/
def gammaPointClass : GammaNamedRVSemiring hc C Ξ hΞ :=
  DirectSum.of (GammaNamedRVClasses hc C Ξ hΞ) 1 (gammaNamedRVClass hc C Ξ hΞ (gammaPoint hc C Ξ hΞ))

theorem gamma_point_product_swap_positive {k : ℕ} (U : GammaRVObjects 𝔅 𝔖 (k+1)) :
    HEq (gammaNamedRVClass hc C Ξ hΞ (U.product hc (gammaPoint hc C Ξ hΞ)))
      (gammaNamedRVClass hc C Ξ hΞ ((gammaPoint hc C Ξ hΞ).product hc U)) := by
  let P := degreeOnePointVolumeObject (M := M) 𝔖
  have hP : VolumeObjectGamma P 𝔅 := VolumeObjectGamma.degreeOnePoint hc _
  let V : GammaVolumeObjects 𝔅 𝔖 k := ⟨U.val,(RVVolumeObject.Gamma.positive_iff U.val).mp U.property⟩
  let h := positiveProduct_degree_swap k 0
  let W : GammaVolumeObjects 𝔅 𝔖 (0+1+k) := ⟨P.prod V.val,hP.prod hc V.property⟩
  have e1 : gammaVolumeBlowupClass hc 𝔇 𝔅 ⟨V.val.prod P,V.property.prod hc hP⟩ =
      gammaVolumeBlowupClass hc 𝔇 𝔅 (W.reindexDegree h) :=
    gammaVolumeBlowupClass_iso hc 𝔇 𝔅 (volumeUnitPointSwapIso 𝔇 V.val)
      (gamma_volume_unit_point_swap_iso hc 𝔇 V.property)
  exact (heq_of_eq e1).trans (gamma_class_reindex_heq hc 𝔇 𝔅 h W)

theorem gamma_point_product_swap_zero (U : GammaRVObjects 𝔅 𝔖 0) :
    HEq (gammaNamedRVClass hc C Ξ hΞ (U.product hc (gammaPoint hc C Ξ hΞ)))
      (gammaNamedRVClass hc C Ξ hΞ ((gammaPoint hc C Ξ hΞ).product hc U)) := by
  let P := degreeOnePointVolumeObject (M := M) 𝔖
  have hP : VolumeObjectGamma P 𝔅 := VolumeObjectGamma.degreeOnePoint hc _
  let Z : GammaZeroRVObjects 𝔅 𝔖 := ⟨U.val,(RVVolumeObject.Gamma.zero_iff U.val).mp U.property⟩
  let V : GammaVolumeObjects 𝔅 𝔖 0 := ⟨P,hP⟩
  have h1 := GammaFun.named_zero_pos_product_heq hc C Ξ hΞ Z V
  have hPZ := HK.RVVolumeObject.Gamma.product (n := 0+1) (m := 0) hc (gammaPoint hc C Ξ hΞ).property U.property
  have e1 : gammaVolumeBlowupClass hc 𝔇 𝔅 ⟨HK.product 𝔖 (0+1) 0 P U.val,(RVVolumeObject.Gamma.positive_iff _).mp hPZ⟩ =
      gammaVolumeBlowupClass hc 𝔇 𝔅 (V.posZeroProd hc Z) :=
    gammaVolumeBlowupClass_iso hc 𝔇 𝔅 (productPositiveZeroIso hc 𝔇 P Z.val)
      (gamma_volume_iso_of_label_identity hc (productPositiveZeroIso hc 𝔇 P Z.val)
        ((RVVolumeObject.Gamma.positive_iff _).mp hPZ) rfl (fun _ => rfl))
  exact h1.trans (heq_of_eq e1.symm)

theorem gamma_point_class_commutes_component (j : ℕ) (a : GammaNamedRVClasses hc C Ξ hΞ j) :
    Commute (DirectSum.of (GammaNamedRVClasses hc C Ξ hΞ) j a) (gammaPointClass hc C Ξ hΞ) := by
  change DirectSum.of (GammaNamedRVClasses hc C Ξ hΞ) j a * DirectSum.of (GammaNamedRVClasses hc C Ξ hΞ) 1 _ =
    DirectSum.of (GammaNamedRVClasses hc C Ξ hΞ) 1 _ * DirectSum.of (GammaNamedRVClasses hc C Ξ hΞ) j a
  rw [DirectSum.of_mul_of,DirectSum.of_mul_of]
  apply DirectSum.of_eq_of_gradedMonoid_eq
  apply Sigma.ext (Nat.add_comm j 1)
  obtain ⟨U,rfl⟩ := gammaNamedRVClass_surjective hc C Ξ hΞ j a
  change HEq (gammaNamedRVMul hc C Ξ hΞ (gammaNamedRVClass hc C Ξ hΞ U) (gammaNamedRVClass hc C Ξ hΞ (gammaPoint hc C Ξ hΞ)))
    (gammaNamedRVMul hc C Ξ hΞ (gammaNamedRVClass hc C Ξ hΞ (gammaPoint hc C Ξ hΞ)) (gammaNamedRVClass hc C Ξ hΞ U))
  rw [gammaNamedRVMul_class,gammaNamedRVMul_class]
  cases j with
  | zero => exact gamma_point_product_swap_zero hc C Ξ hΞ U
  | succ k => exact gamma_point_product_swap_positive hc C Ξ hΞ U

theorem gamma_point_class_commutes (a : GammaNamedRVSemiring hc C Ξ hΞ) :
    Commute a (gammaPointClass hc C Ξ hΞ) := by
  induction a using DirectSum.induction_on with
  | zero => exact Commute.zero_left _
  | of j a => exact gamma_point_class_commutes_component hc C Ξ hΞ j a
  | add a b ha hb => exact ha.add_left hb

/-! ### Localization at the point and normalization -/

def gammaPointRing : GammaNamedRVRing hc C Ξ hΞ :=
  semiringGroupificationOf (GammaNamedRVSemiring hc C Ξ hΞ) (gammaPointClass hc C Ξ hΞ)

theorem gamma_point_ring_commutes (a : GammaNamedRVRing hc C Ξ hΞ) : Commute a (gammaPointRing hc C Ξ hΞ) := by
  have hOf (x : GammaNamedRVSemiring hc C Ξ hΞ) :
      Commute (semiringGroupificationOf _ x) (gammaPointRing hc C Ξ hΞ) :=
    (gamma_point_class_commutes hc C Ξ hΞ x).map (semiringGroupificationOf _).toMonoidHom
  obtain ⟨x,y,rfl⟩ := semiringGroupification_exists_difference a
  change (semiringGroupificationOf _ x - semiringGroupificationOf _ y) * gammaPointRing hc C Ξ hΞ =
    gammaPointRing hc C Ξ hΞ * (semiringGroupificationOf _ x - semiringGroupificationOf _ y)
  rw [sub_mul,mul_sub,(hOf x).eq,(hOf y).eq]

instance gammaPointRingCentralFact : Fact (∀ a : GammaNamedRVRing hc C Ξ hΞ, Commute a (gammaPointRing hc C Ξ hΞ)) :=
  ⟨gamma_point_ring_commutes hc C Ξ hΞ⟩

abbrev GammaPointLocalization := CentralAway (gammaPointRing hc C Ξ hΞ)

def gammaPointLocalizationMap : GammaNamedRVRing hc C Ξ hΞ →+* GammaPointLocalization hc C Ξ hΞ :=
  centralAwayMap (gammaPointRing hc C Ξ hΞ)

def gammaPointLocalizationCoefficients : GammaNamedRVSemiring hc C Ξ hΞ →+* GammaPointLocalization hc C Ξ hΞ :=
  (gammaPointLocalizationMap hc C Ξ hΞ).comp (semiringGroupificationOf (GammaNamedRVSemiring hc C Ξ hΞ))

def gammaLocalizedPointUnit : (GammaPointLocalization hc C Ξ hΞ)ˣ :=
  (centralAwayMap_point_isUnit (gammaPointRing hc C Ξ hΞ)).unit

theorem gamma_localized_point_unit_value :
    (gammaLocalizedPointUnit hc C Ξ hΞ : GammaPointLocalization hc C Ξ hΞ) =
      gammaPointLocalizationMap hc C Ξ hΞ (gammaPointRing hc C Ξ hΞ) :=
  (centralAwayMap_point_isUnit (gammaPointRing hc C Ξ hΞ)).unit_spec

theorem gamma_localized_coefficients_commute_point (a : GammaNamedRVSemiring hc C Ξ hΞ) :
    Commute (gammaPointLocalizationCoefficients hc C Ξ hΞ a)
      (gammaLocalizedPointUnit hc C Ξ hΞ : GammaPointLocalization hc C Ξ hΞ) := by
  rw [gamma_localized_point_unit_value]
  exact (gamma_point_ring_commutes hc C Ξ hΞ (semiringGroupificationOf _ a)).map
    (gammaPointLocalizationMap hc C Ξ hΞ).toMonoidHom

/-- Normalization: a homogeneous class of degree `n` is divided by the `n`-th power of the point. -/
def normalizedGammaSemiringMap : GammaNamedRVSemiring hc C Ξ hΞ →+* GammaPointLocalization hc C Ξ hΞ :=
  gradedSemiringUnitNormalize (gammaPointLocalizationCoefficients hc C Ξ hΞ) (gammaLocalizedPointUnit hc C Ξ hΞ)
    (gamma_localized_coefficients_commute_point hc C Ξ hΞ)

theorem normalized_gamma_semiring_homogeneous (n : ℕ) (a : GammaNamedRVClasses hc C Ξ hΞ n) :
    normalizedGammaSemiringMap hc C Ξ hΞ (DirectSum.of (GammaNamedRVClasses hc C Ξ hΞ) n a) =
      gammaPointLocalizationCoefficients hc C Ξ hΞ (DirectSum.of (GammaNamedRVClasses hc C Ξ hΞ) n a) *
        (↑(gammaLocalizedPointUnit hc C Ξ hΞ)⁻¹ : GammaPointLocalization hc C Ξ hΞ)^n :=
  graded_semiring_unit_normalize_of _ _ _ n a

theorem normalized_gamma_semiring_point : normalizedGammaSemiringMap hc C Ξ hΞ (gammaPointClass hc C Ξ hΞ) = 1 := by
  apply graded_semiring_unit_normalize_point _ _ _ _
  exact (gamma_localized_point_unit_value hc C Ξ hΞ).symm

def normalizedGammaRingMap : GammaNamedRVRing hc C Ξ hΞ →+* GammaPointLocalization hc C Ξ hΞ :=
  semiringGroupificationLift (normalizedGammaSemiringMap hc C Ξ hΞ)

/-- The Gamma-named normalized RV coefficient ring. -/
abbrev NormalizedGammaRVRing := (normalizedGammaRingMap hc C Ξ hΞ).range

def normalizedGammaRingProjection : GammaNamedRVRing hc C Ξ hΞ →+* NormalizedGammaRVRing hc C Ξ hΞ :=
  (normalizedGammaRingMap hc C Ξ hΞ).rangeRestrict

theorem normalized_gamma_ring_projection_surjective :
    Function.Surjective (normalizedGammaRingProjection hc C Ξ hΞ) := RingHom.rangeRestrict_surjective _

/-- Gamma-named classes to normalized coefficients. -/
def normalizedGammaCoefficientMap : GammaNamedRVSemiring hc C Ξ hΞ →+* NormalizedGammaRVRing hc C Ξ hΞ :=
  (normalizedGammaRingProjection hc C Ξ hΞ).comp (semiringGroupificationOf (GammaNamedRVSemiring hc C Ξ hΞ))

theorem normalized_gamma_coefficient_point :
    normalizedGammaCoefficientMap hc C Ξ hΞ (gammaPointClass hc C Ξ hΞ) = 1 := by
  apply Subtype.ext
  change normalizedGammaRingMap hc C Ξ hΞ (semiringGroupificationOf _ (gammaPointClass hc C Ξ hΞ)) = 1
  rw [normalizedGammaRingMap,semiringGroupificationLift_of]
  exact normalized_gamma_semiring_point hc C Ξ hΞ

theorem normalized_gamma_ring_range_iff_difference (x : GammaPointLocalization hc C Ξ hΞ) :
    x ∈ (normalizedGammaRingMap hc C Ξ hΞ).range ↔
      ∃ a b : GammaNamedRVSemiring hc C Ξ hΞ,
        x = normalizedGammaSemiringMap hc C Ξ hΞ a - normalizedGammaSemiringMap hc C Ξ hΞ b := by
  constructor
  · rintro ⟨r,rfl⟩
    obtain ⟨a,b,rfl⟩ := semiringGroupification_exists_difference r
    exact ⟨a,b,by rw [map_sub,normalizedGammaRingMap,semiringGroupificationLift_of,semiringGroupificationLift_of]⟩
  · rintro ⟨a,b,rfl⟩
    exact ⟨semiringGroupificationOf _ a - semiringGroupificationOf _ b,
      by rw [map_sub,normalizedGammaRingMap,semiringGroupificationLift_of,semiringGroupificationLift_of]⟩

end IntegrationInACVF.Section7.HK
