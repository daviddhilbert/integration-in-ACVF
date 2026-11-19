import Integration7.GammaFunAllDegreeActions

/-! **All-degree coefficient actions on Gamma-named almost-everywhere functions.** The graded
components of Gamma-named almost-everywhere functions (degree-zero functions in component zero,
positive functions of coefficient degree `k` in component `k+1`), the row criterion for their
equality, and the coefficient action, defined through representatives together with its
computation rule on arbitrary representatives. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section5 (Point GammaSetDefinable GammaGraphDefinable gammaLogicInput carrier VF RV)
open IntegrationInACVF.Section5 IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {B : Base (M := M)} {S T : Set M}

theorem HK.ZeroRVVolumeIso.GammaDefinable.extend {U V : HK.ZeroRVVolumeObject (M := M) S}
    {e : HK.ZeroRVVolumeIso U V} (he : e.GammaDefinable B) (h : S ⊆ T) : (e.extend h).GammaDefinable B := by
  apply SpecialTransformations.Section5.GammaGraphDefinable.congr he
  intro p q
  constructor
  · rintro ⟨u,hu,hv⟩
    exact ⟨⟨u.val,u.property⟩,hu,hv⟩
  · rintro ⟨u,hu,hv⟩
    exact ⟨⟨u.val,u.property⟩,hu,hv⟩

end IntegrationInACVF.Section7

namespace IntegrationInACVF.Section7.GammaFun
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n : ℕ}
variable (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
variable (Ξ : Set (Values.Gamma (M := M))) (hΞ : Cardinal.mk Ξ < C.κ)

set_option quotPrecheck false
local notation "𝔅" => gammaNamedBase C Ξ
local notation "𝔇" => gammaNamedCodeContext C Ξ hΞ
local notation "𝔖" => ((gammaNamedCodeContext C Ξ hΞ).base : Set M)

/-- The graded components of Gamma-named almost-everywhere functions on `VF^(n+1)`. -/
abbrev AEComp (n : ℕ) : ℕ → Type
  | 0 => AEZeroFunction hc C Ξ hΞ n
  | k+1 => AEFunction hc C Ξ hΞ n k

instance aeCompAddCommMonoid (n : ℕ) : (j : ℕ) → AddCommMonoid (AEComp hc C Ξ hΞ n j)
  | 0 => inferInstanceAs (AddCommMonoid (AEZeroFunction hc C Ξ hΞ n))
  | k+1 => inferInstanceAs (AddCommMonoid (AEFunction hc C Ξ hΞ n k))

/-- The almost-everywhere class of a component presentation. -/
def aeMk : {j : ℕ} → Pres C Ξ hΞ n j → AEComp hc C Ξ hΞ n j
  | 0, F => Quotient.mk _ F
  | _+1, F => Quotient.mk _ F

/-- A chosen representative of a component function. -/
def aeRep : {j : ℕ} → AEComp hc C Ξ hΞ n j → Pres C Ξ hΞ n j
  | 0, f => Quotient.out f
  | _+1, f => Quotient.out f

theorem aeMk_rep {j : ℕ} (f : AEComp hc C Ξ hΞ n j) : aeMk hc C Ξ hΞ (aeRep hc C Ξ hΞ f) = f := by
  cases j with
  | zero => exact Quotient.out_eq f
  | succ k => exact Quotient.out_eq f

/-- Almost-everywhere equality of row classes. -/
def PresAE {j : ℕ} (F H : Pres C Ξ hΞ n j) : Prop :=
  ∃ E : GammaVFSet C Ξ hΞ n,
    SpecialTransformations.Section4.vfDim (SpecialTransformations.Section4.rawRVSpace (M := M) 1) E.set < n+1 ∧
      ∀ x, x ∉ E.set.carrier → presRowClass hc C Ξ hΞ F x = presRowClass hc C Ξ hΞ H x

theorem aeMk_eq_iff {j : ℕ} (F H : Pres C Ξ hΞ n j) :
    aeMk hc C Ξ hΞ F = aeMk hc C Ξ hΞ H ↔ PresAE hc C Ξ hΞ F H := by
  cases j with
  | zero => exact ⟨fun h => Quotient.exact h,fun h => Quotient.sound h⟩
  | succ k => exact ⟨fun h => Quotient.exact h,fun h => Quotient.sound h⟩

theorem aeMk_eq_of_rows {j : ℕ} (F H : Pres C Ξ hΞ n j)
    (h : ∀ x, presRowClass hc C Ξ hΞ F x = presRowClass hc C Ξ hΞ H x) : aeMk hc C Ξ hΞ F = aeMk hc C Ξ hΞ H := by
  cases j with
  | zero => exact Quotient.sound (zero_ae_equivalent_of_rows C Ξ hΞ F H h)
  | succ k => exact Quotient.sound (ae_equivalent_of_rows hc C Ξ hΞ F H h)

theorem aeMk_heq_of_rows {j j' : ℕ} (hj : j = j') (F : Pres C Ξ hΞ n j) (H : Pres C Ξ hΞ n j')
    (h : ∀ x, HEq (presRowClass hc C Ξ hΞ F x) (presRowClass hc C Ξ hΞ H x)) :
    HEq (aeMk hc C Ξ hΞ F) (aeMk hc C Ξ hΞ H) := by
  subst hj
  exact heq_of_eq (aeMk_eq_of_rows hc C Ξ hΞ F H (fun x => eq_of_heq (h x)))

/-- Row coefficients of Gamma-named-equivalent coefficients are equivalent. -/
theorem coef_row_class_congr {i : ℕ} {u u' : HK.GammaRVObjects 𝔅 𝔖 i}
    (h : HK.gammaNamedRVClass hc C Ξ hΞ u = HK.gammaNamedRVClass hc C Ξ hΞ u') (x : Fin (n+1) → VFType (M := M)) :
    HK.Ctx.gammaNamedRVClass hc (vfParameterVolumeContext 𝔇 x) (rowGammaBase 𝔅 x) (coefRow C Ξ hΞ u x) =
      HK.Ctx.gammaNamedRVClass hc (vfParameterVolumeContext 𝔇 x) (rowGammaBase 𝔅 x) (coefRow C Ξ hΞ u' x) := by
  cases i with
  | zero =>
    obtain ⟨f,hf⟩ := Quotient.exact (s := HK.gammaZeroRVSetoid 𝔅 𝔖) h
    exact Quotient.sound ⟨f.extend _,(GammaBaseDominated.of_subset (B' := 𝔅) (B := rowGammaBase 𝔅 x)
      Set.subset_union_left (Set.Subset.refl _)).graph (hf.extend _)⟩
  | succ p =>
    have hb := (gammaVolumeBlowupClass_eq_iff hc 𝔇 𝔅).mp h
    exact (gammaVolumeBlowupClass_eq_iff hc _ _).mpr
      ((hb.extend (fun _ h => vfParameterVolumeContext_contains 𝔇 x (Or.inl h))).changeBase
        (GammaBaseDominated.of_subset (B' := 𝔅) (B := rowGammaBase 𝔅 x) Set.subset_union_left (Set.Subset.refl _)))

end IntegrationInACVF.Section7.GammaFun
