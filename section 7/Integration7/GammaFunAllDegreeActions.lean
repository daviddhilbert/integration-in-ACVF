import Integration7.GammaFunCoefficientRows
import Integration7.GammaCtxRVLaws
import Integration7.HKZeroCoefficientSemiring
import Integration7.SignedVolumeProductSwap

/-! **All-degree coefficient actions on Gamma-named presentations.** A Gamma all-degree RV
coefficient of degree `i` (degree zero: weighted degree-zero objects; degree `p+1`: positive
objects of degree `p`) acts on Gamma-named presentations of component `j` (component zero:
degree-zero presentations; component `k+1`: positive presentations of coefficient degree `k`),
by the raw coefficient-first products. At every VF point the row of the product is, as a Gamma RV
class of the row context, the actual product of the row coefficient with the row. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section5 (Point GammaSetDefinable GammaGraphDefinable gammaLogicInput carrier VF RV)
open SpecialTransformations.DefinableGeometry (Map DefSet)
open IntegrationInACVF.Section5 IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {B : Base (M := M)} {S : Set M}

theorem gamma_zero_product_swap_iso (hc : CanonicalStructure.IsCanonical (M := M))
    (Z T : HK.GammaZeroRVObjects B S) : (HK.zeroProductSwapIso Z.val T.val).GammaDefinable B := by
  have hP := HK.RVVolumeObject.Gamma.product (n := 0) (m := 0) hc ((HK.RVVolumeObject.Gamma.zero_iff _).mpr Z.property)
    ((HK.RVVolumeObject.Gamma.zero_iff _).mpr T.property)
  refine gamma_rv_coordinate_map hc _
    (Fin.append (Fin.natAdd Z.val.underlying.obj.arity) (Fin.castAdd T.val.underlying.obj.arity)) hP.domain ?_
  intro w
  obtain ⟨z,t,rfl⟩ := SpecialTransformations.Section4.exists_rvPackPair Z.val.underlying.obj.domain
    T.val.underlying.obj.domain w
  change (SpecialTransformations.Section4.rvProductSwapMap Z.val.underlying.obj T.val.underlying.obj (SpecialTransformations.Section4.rvPackPair _ _ z t)).val = _
  rw [rvProductSwapMap_pair]
  change Fin.append t.val z.val = Fin.append z.val t.val ∘ Fin.append (Fin.natAdd _) (Fin.castAdd _)
  funext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · simp only [Function.comp_apply,Fin.append_left,Fin.append_right]
  · simp only [Function.comp_apply,Fin.append_left,Fin.append_right]

end IntegrationInACVF.Section7

namespace IntegrationInACVF.Section7.GammaFun
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n : ℕ}
variable (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
variable (Ξ : Set (Values.Gamma (M := M))) (hΞ : Cardinal.mk Ξ < C.κ)

set_option quotPrecheck false
local notation "𝔅" => gammaNamedBase C Ξ
local notation "𝔇" => gammaNamedCodeContext C Ξ hΞ
local notation "𝔖" => ((gammaNamedCodeContext C Ξ hΞ).base : Set M)

/-- The row coefficient of a Gamma all-degree coefficient at a VF point. -/
def coefRow : {i : ℕ} → HK.GammaRVObjects 𝔅 𝔖 i → (x : Fin (n+1) → VFType (M := M)) →
    HK.GammaRVObjects (rowGammaBase 𝔅 x) ((vfParameterVolumeContext 𝔇 x).base : Set M) i
  | 0, U, x => ⟨(zeroRowCoefficient ⟨U.val,(HK.RVVolumeObject.Gamma.zero_iff _).mp U.property⟩ x).val,
      (HK.RVVolumeObject.Gamma.zero_iff _).mpr (zeroRowCoefficient _ x).property⟩
  | _+1, U, x => ⟨(positiveRowCoefficient ⟨U.val,(HK.RVVolumeObject.Gamma.positive_iff _).mp U.property⟩ x).val,
      (HK.RVVolumeObject.Gamma.positive_iff _).mpr (positiveRowCoefficient _ x).property⟩

/-- Gamma-named presentations of the graded components. -/
abbrev Pres (n : ℕ) : ℕ → Type
  | 0 => ZeroPresentation C Ξ hΞ n
  | k+1 => Presentation C Ξ hΞ n k

/-- The all-degree row of a component presentation. -/
def presRow : {j : ℕ} → Pres C Ξ hΞ n j → (x : Fin (n+1) → VFType (M := M)) →
    HK.GammaRVObjects (rowGammaBase 𝔅 x) ((vfParameterVolumeContext 𝔇 x).base : Set M) j
  | 0, F, x => ⟨F.family.rowInContext x,(HK.RVVolumeObject.Gamma.zero_iff _).mpr (F.gamma.row x)⟩
  | _+1, F, x => ⟨F.family.rowInContext x,(HK.RVVolumeObject.Gamma.positive_iff _).mpr (F.gamma.row hc x)⟩

/-- The all-degree row class of a component presentation. -/
def presRowClass {j : ℕ} (F : Pres C Ξ hΞ n j) (x : Fin (n+1) → VFType (M := M)) :
    HK.Ctx.GammaNamedRVClasses hc (vfParameterVolumeContext 𝔇 x) (rowGammaBase 𝔅 x) j :=
  HK.Ctx.gammaNamedRVClass hc (vfParameterVolumeContext 𝔇 x) (rowGammaBase 𝔅 x) (presRow hc C Ξ hΞ F x)

/-- Degree reindexing of positive presentations. -/
def Presentation.reindex {k k' : ℕ} (h : k = k') (F : Presentation C Ξ hΞ n k) : Presentation C Ξ hΞ n k' :=
  h ▸ F

theorem presentation_reindex_row_heq {k k' : ℕ} (h : k = k') (F : Presentation C Ξ hΞ n k)
    (x : Fin (n+1) → VFType (M := M)) :
    HEq (presRowClass hc C Ξ hΞ (j := k'+1) (F.reindex C Ξ hΞ h) x) (presRowClass hc C Ξ hΞ (j := k+1) F x) := by
  subst h
  rfl

/-- Weighted degree-zero coefficient on a positive presentation. -/
def Presentation.zeroCoef (Z : HK.GammaZeroRVObjects 𝔅 𝔖) {k : ℕ} (F : Presentation C Ξ hΞ n k) :
    Presentation C Ξ hΞ n k :=
  ⟨_,HK.selectedFamilyWeightedZeroProduct F.family Z.val,F.gamma.weightedZero hc Z.property⟩

/-- Positive coefficient on a degree-zero presentation. -/
def ZeroPresentation.posCoef {p : ℕ} (U : GammaVolumeObjects 𝔅 𝔖 p) (F : ZeroPresentation C Ξ hΞ n) :
    Presentation C Ξ hΞ n p :=
  ⟨_,HK.selectedZeroFamilyPositiveProduct U.val F.family,F.gamma.positiveProduct hc U.property⟩

/-- Weighted degree-zero coefficient on a degree-zero presentation. -/
def ZeroPresentation.zeroCoef (Z : HK.GammaZeroRVObjects 𝔅 𝔖) (F : ZeroPresentation C Ξ hΞ n) :
    ZeroPresentation C Ξ hΞ n :=
  ⟨_,F.family.prodZero Z.val,F.gamma.prodZero hc Z.property⟩

/-- **The all-degree coefficient action on component presentations.** -/
def presAct : {i j : ℕ} → HK.GammaRVObjects 𝔅 𝔖 i → Pres C Ξ hΞ n j → Pres C Ξ hΞ n (i+j)
  | 0, 0, Z, F => (F : ZeroPresentation C Ξ hΞ n).zeroCoef hc C Ξ hΞ ⟨Z.val,(HK.RVVolumeObject.Gamma.zero_iff _).mp Z.property⟩
  | 0, _+1, Z, F => ((F : Presentation C Ξ hΞ n _).zeroCoef hc C Ξ hΞ
      ⟨Z.val,(HK.RVVolumeObject.Gamma.zero_iff _).mp Z.property⟩).reindex C Ξ hΞ (Nat.zero_add _).symm
  | _+1, 0, U, F => (F : ZeroPresentation C Ξ hΞ n).posCoef hc C Ξ hΞ
      ⟨U.val,(HK.RVVolumeObject.Gamma.positive_iff _).mp U.property⟩
  | _+1, _+1, U, F => (F : Presentation C Ξ hΞ n _).leftProduct hc C Ξ hΞ
      ⟨U.val,(HK.RVVolumeObject.Gamma.positive_iff _).mp U.property⟩

set_option maxHeartbeats 1600000 in
/-- **Rows of all-degree coefficient actions.** -/
theorem pres_act_row {i j : ℕ} (u : HK.GammaRVObjects 𝔅 𝔖 i) (F : Pres C Ξ hΞ n j) (x : Fin (n+1) → VFType (M := M)) :
    HEq (presRowClass hc C Ξ hΞ (presAct hc C Ξ hΞ u F) x)
      (HK.Ctx.gammaNamedRVClass hc (vfParameterVolumeContext 𝔇 x) (rowGammaBase 𝔅 x)
        ((coefRow C Ξ hΞ u x).product hc (presRow hc C Ξ hΞ F x))) := by
  let D := vfParameterVolumeContext 𝔇 x
  let Bx := rowGammaBase 𝔅 x
  cases i with
  | zero =>
    let Z : HK.GammaZeroRVObjects 𝔅 𝔖 := ⟨u.val,(HK.RVVolumeObject.Gamma.zero_iff _).mp u.property⟩
    cases j with
    | zero =>
      apply heq_of_eq
      let F0 : ZeroPresentation C Ξ hΞ n := F
      let RZ := zeroRowCoefficient Z x
      let RF : HK.GammaZeroRVObjects Bx (D.base : Set M) := ⟨F0.family.rowInContext x,F0.gamma.row x⟩
      have h1 := gamma_zero_family_scalar_row_iso hc F0.gamma Z x
      have h2 := gamma_zero_product_swap_iso hc RF RZ
      exact Quotient.sound ⟨(HK.zeroVolumeFamilyScalarRowIso F0.family Z.val x).trans (HK.zeroProductSwapIso RF.val RZ.val),
        h1.trans h2⟩
    | succ k =>
      let F' : Presentation C Ξ hΞ n k := F
      refine (presentation_reindex_row_heq hc C Ξ hΞ (Nat.zero_add k).symm (F'.zeroCoef hc C Ξ hΞ Z) x).trans ?_
      let RF : GammaVolumeObjects Bx (D.base : Set M) k := ⟨F'.family.rowInContext x,F'.gamma.row hc x⟩
      let RZ := zeroRowCoefficient Z x
      have e1 := gamma_weighted_zero_row_class hc F'.gamma Z x
      have e2 : gammaVolumeBlowupClass hc D Bx (RF.posZeroProd hc RZ) = gammaVolumeBlowupClass hc D Bx (RF.zeroProd hc RZ) :=
        (gammaVolumeBlowupClass_eq_iff hc D Bx).mpr (GammaVolumeBlowupEquivalent.of_iso D Bx
          (U := RF.posZeroProd hc RZ) (V := RF.zeroProd hc RZ)
          (HK.mixedProductSwapIso hc D RF.val RZ.val) (gamma_mixed_product_swap_iso hc D RF.property RZ.property))
      have hZP := HK.RVVolumeObject.Gamma.product (n := 0) (m := k+1) hc ((HK.RVVolumeObject.Gamma.zero_iff _).mpr RZ.property)
        ((HK.RVVolumeObject.Gamma.positive_iff _).mpr RF.property)
      have e3 : gammaVolumeBlowupClass hc D Bx ((RF.zeroProd hc RZ).reindexDegree (Nat.zero_add k)) =
          gammaVolumeBlowupClass hc D Bx ⟨HK.product (D.base : Set M) 0 (k+1) RZ.val RF.val,
            (HK.RVVolumeObject.Gamma.positive_iff _).mp hZP⟩ :=
        (gammaVolumeBlowupClass_eq_iff hc D Bx).mpr (GammaVolumeBlowupEquivalent.of_iso D Bx
          ((HK.productZeroPositiveIso hc D RZ.val RF.val).symm hc D)
          ((gamma_volume_iso_of_label_identity hc (HK.productZeroPositiveIso hc D RZ.val RF.val)
            ((HK.RVVolumeObject.Gamma.positive_iff _).mp hZP) rfl (fun _ => rfl)).symm hc D Bx))
      refine (heq_of_eq (e1.trans e2)).trans ?_
      exact (gamma_class_reindex_heq hc D Bx (Nat.zero_add k) _).symm.trans (heq_of_eq e3)
  | succ p =>
    let U : GammaVolumeObjects 𝔅 𝔖 p := ⟨u.val,(HK.RVVolumeObject.Gamma.positive_iff _).mp u.property⟩
    cases j with
    | zero =>
      apply heq_of_eq
      let F0 : ZeroPresentation C Ξ hΞ n := F
      let RU := positiveRowCoefficient U x
      let RF : HK.GammaZeroRVObjects Bx (D.base : Set M) := ⟨F0.family.rowInContext x,F0.gamma.row x⟩
      have e1 := gamma_zero_family_positive_product_row_class hc F0.gamma U x
      have e2 : gammaVolumeBlowupClass hc D Bx (RU.posZeroProd hc RF) =
          gammaVolumeBlowupClass hc D Bx ⟨HK.zeroProduct RF.val RU.val,VolumeObjectGamma.zeroProd hc RF.property RU.property⟩ :=
        (gammaVolumeBlowupClass_eq_iff hc D Bx).mpr (GammaVolumeBlowupEquivalent.of_iso D Bx
          (U := RU.posZeroProd hc RF) (V := ⟨HK.zeroProduct RF.val RU.val,VolumeObjectGamma.zeroProd hc RF.property RU.property⟩)
          (HK.mixedProductSwapIso hc D RU.val RF.val) (gamma_mixed_product_swap_iso hc D RU.property RF.property))
      have hPZ := HK.RVVolumeObject.Gamma.product (n := p+1) (m := 0) hc ((HK.RVVolumeObject.Gamma.positive_iff _).mpr RU.property)
        ((HK.RVVolumeObject.Gamma.zero_iff _).mpr RF.property)
      have e3 : gammaVolumeBlowupClass hc D Bx ⟨HK.product (D.base : Set M) (p+1) 0 RU.val RF.val,
            (HK.RVVolumeObject.Gamma.positive_iff _).mp hPZ⟩ = gammaVolumeBlowupClass hc D Bx (RU.posZeroProd hc RF) :=
        (gammaVolumeBlowupClass_eq_iff hc D Bx).mpr (GammaVolumeBlowupEquivalent.of_iso D Bx
          (HK.productPositiveZeroIso hc D RU.val RF.val)
          (gamma_volume_iso_of_label_identity hc (HK.productPositiveZeroIso hc D RU.val RF.val)
            ((HK.RVVolumeObject.Gamma.positive_iff _).mp hPZ) rfl (fun _ => rfl)))
      exact e1.trans (e2.symm.trans e3.symm)
    | succ k =>
      exact heq_of_eq (gamma_left_product_row_class hc U.property (F : Presentation C Ξ hΞ n k).gamma x)

end IntegrationInACVF.Section7.GammaFun
