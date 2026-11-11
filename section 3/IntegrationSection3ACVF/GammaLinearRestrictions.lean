import IntegrationSection3ACVF.OpenRadiusLimits

/-! Restriction and uniqueness of actual Gamma-linearity coefficients.
These are geometric inputs to closure of the least-radius locus. -/

open Set Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer SpecialTransformations.Section3

namespace IntegrationInACVF.Section3ACVF.GammaLinearRestrictions

open GammaRadiusAtomicity

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

theorem mono {A C : Set M} (hCA : C ⊆ A) (f : M → M) (hfVF : ∀ x ∈ A, iVF (f x))
    (s : Values.Gamma (M := M)) (hLinear : GammaLinearity.GammaLinear A f hfVF s) :
    GammaLinearity.GammaLinear C f (fun x hx => hfVF x (hCA hx)) s := by
  intro x y hx hy
  exact hLinear x y (hCA hx) (hCA hy)

theorem coefficient_unique (A : Set M) (f : M → M) (hfVF : ∀ x ∈ A, iVF (f x))
    (x y : VFType (M := M)) (hx : x.val ∈ A) (hy : y.val ∈ A) (hne : x ≠ y)
    (s t : Values.Gamma (M := M))
    (hs : GammaLinearity.GammaLinear A f hfVF s) (ht : GammaLinearity.GammaLinear A f hfVF t) : s = t := by
  have hFinite : Values.vfValueHom (y-x) ≠ Values.infinity := by
    intro h
    have hz := (Values.vrv_eq_infinity_iff (CanonicalRV.encodedRv (y-x))).mp h
    exact (sub_ne_zero.mpr hne.symm) ((CanonicalRV.encodedRv_zero_iff (y-x)).mp hz)
  let γ : Values.Gamma (M := M) := ⟨Values.vfValueHom (y-x),hFinite⟩
  have hS := hs x y hx hy
  have hT := ht x y hx hy
  have hEq : (s*γ).val = (t*γ).val := by
    rw [Values.gamma_val_mul,Values.gamma_val_mul]
    exact hS.symm.trans hT
  exact mul_right_cancel (Subtype.ext hEq)

theorem ordinary_coefficient_unique (c : VFType (M := M)) (ρ : Values.Gamma (M := M))
    (f : M → M) (hfVF : ∀ x ∈ gammaBall c ρ true, iVF (f x)) (s t : Values.Gamma (M := M))
    (hs : GammaLinearity.GammaLinear (gammaBall c ρ true) f hfVF s)
    (ht : GammaLinearity.GammaLinear (gammaBall c ρ true) f hfVF t) : s = t := by
  obtain ⟨x,y,hx,hy,hne⟩ := OpenRadiusLimits.distinct_points c ρ
  exact coefficient_unique _ f hfVF x y hx hy hne s t hs ht

def SlopeAt (A : Set M) (f : M → M) (hfVF : ∀ x ∈ A, iVF (f x))
    (c : VFType (M := M)) (ρ s : Values.Gamma (M := M)) : Prop :=
  ∃ hSub : gammaBall c ρ true ⊆ A,
    GammaLinearity.GammaLinear (gammaBall c ρ true) f (fun x hx => hfVF x (hSub hx)) s

theorem slope_mono (A : Set M) (f : M → M) (hfVF : ∀ x ∈ A, iVF (f x))
    (c : VFType (M := M)) (ρ τ s : Values.Gamma (M := M)) (hρτ : ρ ≤ τ)
    (hSlope : SlopeAt A f hfVF c ρ s) : SlopeAt A f hfVF c τ s := by
  obtain ⟨hSub,hLinear⟩ := hSlope
  have hNested := OpenRadiusLimits.nested c ρ τ hρτ
  exact ⟨hNested.trans hSub,mono hNested f _ s hLinear⟩

theorem slope_unique (A : Set M) (f : M → M) (hfVF : ∀ x ∈ A, iVF (f x))
    (c : VFType (M := M)) (ρ τ s t : Values.Gamma (M := M))
    (hS : SlopeAt A f hfVF c ρ s) (hT : SlopeAt A f hfVF c τ t) : s = t := by
  obtain ⟨hSSub,hSLinear⟩ := slope_mono A f hfVF c ρ (max ρ τ) s (le_max_left _ _) hS
  obtain ⟨hTSub,hTLinear⟩ := slope_mono A f hfVF c τ (max ρ τ) t (le_max_right _ _) hT
  exact ordinary_coefficient_unique c (max ρ τ) f (fun x hx => hfVF x (hSSub hx)) s t hSLinear hTLinear

end IntegrationInACVF.Section3ACVF.GammaLinearRestrictions
