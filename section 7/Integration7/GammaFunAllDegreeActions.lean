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

end IntegrationInACVF.Section7.GammaFun
